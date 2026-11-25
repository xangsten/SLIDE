module

public import LeanLab.Variants.TwoLevelSearch

set_option linter.style.header false

/-!
# Two-level sliding with arithmetic averaging

The outer and inner centers are updated without momentum. The two arithmetic
averages are used as outputs, never as extrapolated query points.
-/

@[expose] public section

namespace LeanLab.Sliding.TwoLevel.Plain

open Set
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Add one point to the mean of n previous points. -/
def meanStep (n : ℕ) (average point : E) : E :=
  mix (((n : ℝ) + 1)⁻¹) average point

theorem mean_weight (n : ℕ) :
    0 ≤ ((n : ℝ) + 1)⁻¹ ∧ ((n : ℝ) + 1)⁻¹ ≤ 1 :=
  ⟨by positivity, inv_le_one_of_one_le₀ (by simp)⟩

private theorem mean_mem {D : Set E} (hD : Convex ℝ D) (n : ℕ) {x y : E}
    (hx : x ∈ D) (hy : y ∈ D) : meanStep n x y ∈ D :=
  mix_mem hD (mean_weight n).1 (mean_weight n).2 hx hy

theorem mean_bound (F : E → ℝ) (n : ℕ) (x y : E)
    (h : F (meanStep n x y) ≤
      (1 - ((n : ℝ) + 1)⁻¹) * F x + ((n : ℝ) + 1)⁻¹ * F y) :
    ((n + 1 : ℕ) : ℝ) * F (meanStep n x y) ≤ (n : ℝ) * F x + F y := by
  let k : ℝ := (n : ℝ) + 1
  have hk : 0 < k := by dsimp [k]; positivity
  have hmul := mul_le_mul_of_nonneg_left h hk.le
  have hcoeff : k * (1 - k⁻¹) = (n : ℝ) := by
    rw [mul_sub, mul_one, mul_inv_cancel₀ hk.ne']
    simp [k]
  rw [Nat.cast_succ]
  change k * F (meanStep n x y) ≤ _
  change k * F (meanStep n x y) ≤ k * ((1 - k⁻¹) * F x + k⁻¹ * F y) at hmul
  rwa [mul_add, ← mul_assoc, ← mul_assoc, hcoeff, mul_inv_cancel₀ hk.ne', one_mul] at hmul

/-- Each inner iteration uses a fixed curvature and two evaluations of Q. -/
def innerPass {D : Set E} (P : Projection D) (Q : E → E) (m : Quadratic E)
    (H : ℝ) (start : E) : ℕ → InnerState E
  | 0 => ⟨start, start⟩
  | n + 1 =>
    let previous := innerPass P Q m H start n
    let trial := operatorStep P Q m H previous.center
    ⟨meanStep n previous.average trial.average, trial.center⟩

private theorem inner_feasible {D : Set E} (hD : Convex ℝ D)
    (P : Projection D) (Q : E → E) (m : Quadratic E) (H : ℝ)
    {start : E} (hs : start ∈ D) (n : ℕ) :
    (innerPass P Q m H start n).average ∈ D ∧ (innerPass P Q m H start n).center ∈ D := by
  induction n with
  | zero => exact ⟨hs, hs⟩
  | succ n ih => exact ⟨mean_mem hD n ih.1 (P.feasible _), P.feasible _⟩

theorem inner_pass_bound {D : Set E} (hD : Convex ℝ D) (P : Projection D)
    {Q : E → E} {m : Quadratic E} {H M : ℝ} (hm : 0 ≤ m.curvature)
    (hH : 0 < H) (hQ : MonotoneLipschitz D Q M) (hcurv : 2 * M ≤ H)
    {start w : E} (hs : start ∈ D) (hw : w ∈ D) (n : ℕ) :
    let s := innerPass P Q m H start n
    (n : ℝ) * innerGap m Q w s.average ≤
      H / 2 * (‖start - w‖ ^ 2 - ‖s.center - w‖ ^ 2) := by
  induction n with
  | zero => simp [innerPass]
  | succ n ih =>
    let prev := innerPass P Q m H start n
    let trial := operatorStep P Q m H prev.center
    have hb := operator_step_bound P hm hH hQ hw (inner_feasible hD P Q m H hs n).2 hcurv
    have hmix := innerGap_mix m Q w prev.average trial.average
      (mean_weight n).1 (mean_weight n).2 hm
    have havg := mean_bound (innerGap m Q w) n prev.average trial.average hmix
    change innerGap m Q w trial.average ≤
      H / 2 * (‖prev.center - w‖ ^ 2 - ‖trial.center - w‖ ^ 2) at hb
    change (n : ℝ) * innerGap m Q w prev.average ≤
      H / 2 * (‖start - w‖ ^ 2 - ‖prev.center - w‖ ^ 2) at ih
    change ((n + 1 : ℕ) : ℝ) * innerGap m Q w (meanStep n prev.average trial.average) ≤
      H / 2 * (‖start - w‖ ^ 2 - ‖trial.center - w‖ ^ 2)
    linarith only [havg, hb, ih]

/-- Compute the two new centers, using the supplied cached gradient. -/
def trial {D : Set E} (P : Projection D) (Q : E → E) (cfg : Config) (gx : E)
    (s : State E) : InnerState E :=
  let m : Quadratic E := ⟨cfg.Λ, s.functionCenter, gx⟩
  innerPass P Q m cfg.operatorCurvature s.operatorCenter (cfg.innerLast + 1)

/-- The outer trial checks its model at the mean returned by the inner loop.
It uses the old center for the gradient and the new center for the optional secant. -/
def step {D : Set E} (P : Projection D) (g Q : E → E) (cfg : Config)
    (n : ℕ) (s : State E) : Except ℝ (State E) :=
  let g₀ := g s.functionCenter
  let inner := trial P Q cfg g₀ s
  let τ := threshold g cfg s.functionCenter inner.average g₀
  if cfg.Λ < τ then .error τ
  else .ok ⟨meanStep n s.average inner.average, inner.average, inner.center⟩

/-- Counts include the inner work spent on any rejected trial. -/
def pass {D : Set E} (P : Projection D) (g Q : E → E) (cfg : Config)
    (zin : E) : ℕ → Run E
  | 0 => ⟨.ok ⟨zin, zin, zin⟩, ⟨0, 0⟩⟩
  | n + 1 =>
    let prev := pass P g Q cfg zin n
    match prev.result with
    | .error _ => prev
    | .ok s => ⟨step P g Q cfg n s, prev.calls.add
        ⟨gradientsPerStep cfg, 2 * (cfg.innerLast + 1)⟩⟩

theorem pass_calls {D : Set E} (P : Projection D) (g Q : E → E) (cfg : Config)
    (zin : E) (n : ℕ) :
    (pass P g Q cfg zin n).calls.gradients ≤ n * gradientsPerStep cfg ∧
      (pass P g Q cfg zin n).calls.operators ≤ n * (2 * (cfg.innerLast + 1)) := by
  induction n with
  | zero => simp [pass]
  | succ n ih =>
    cases hp : (pass P g Q cfg zin n).result with
    | error τ =>
      simp only [pass, hp]
      rw [Nat.succ_mul n (gradientsPerStep cfg), Nat.succ_mul n (2 * (cfg.innerLast + 1))]
      exact ⟨ih.1.trans (Nat.le_add_right ..), ih.2.trans (Nat.le_add_right ..)⟩
    | ok s =>
      simp only [pass, hp, Calls.add]
      rw [Nat.succ_mul n (gradientsPerStep cfg), Nat.succ_mul n (2 * (cfg.innerLast + 1))]
      exact ⟨Nat.add_le_add_right ih.1 _, Nat.add_le_add_right ih.2 _⟩

theorem gap_mean {D : Set E} {f : E → ℝ} {Q : E → E}
    (hf : ConvexOn ℝ D f) {x y : E} (hx : x ∈ D) (hy : y ∈ D) (w : E) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * gap f Q (meanStep n x y) w ≤
      (n : ℝ) * gap f Q x w + gap f Q y w := by
  apply mean_bound (fun z => gap f Q z w) n x y
  let a := ((n : ℝ) + 1)⁻¹
  have hf' := hf.2 hx hy (sub_nonneg.mpr (mean_weight n).2)
    (mean_weight n).1 (sub_add_cancel 1 a)
  change f (meanStep n x y) ≤ (1 - a) * f x + a * f y at hf'
  have hd : meanStep n x y - w = (1 - a) • (x - w) + a • (y - w) := by
    change mix a x y - w = _
    unfold mix
    module
  change gap f Q (meanStep n x y) w ≤ (1 - a) * gap f Q x w + a * gap f Q y w
  simp only [gap, hd, inner_add_right, real_inner_smul_right]
  linarith only [hf']

/-- The two center terms telescope with coefficients fixed for the entire pass. -/
def energy (cfg : Config) (w : E) (s : State E) : ℝ :=
  cfg.Λ / 2 * ‖s.functionCenter - w‖ ^ 2 +
    cfg.operatorCurvature / (2 * ((cfg.innerLast : ℝ) + 1)) * ‖s.operatorCenter - w‖ ^ 2

/-- The actual trial inequality retains the unused curvature of the model. -/
theorem trial_bound {D : Set E} (P : Projection D) {f : E → ℝ} {g Q : E → E}
    {cfg : Config} (hf : FunctionOracle D f g cfg) {M : ℝ}
    (hQ : MonotoneLipschitz D Q M) (hΛ : 0 < cfg.Λ) (hH : 0 < cfg.operatorCurvature)
    (hcurv : 2 * M ≤ cfg.operatorCurvature) {s : State E}
    (hs : Feasible D s) :
    let inner := trial P Q cfg (g s.functionCenter) s
    let v := inner.average
    v ∈ D ∧ inner.center ∈ D ∧ ∀ w ∈ D,
      gap f Q v w + (cfg.Λ - threshold g cfg s.functionCenter v (g s.functionCenter)) / 2 *
        ‖v - s.functionCenter‖ ^ 2 ≤ energy cfg w s - energy cfg w ⟨v, v, inner.center⟩ := by
  let u := s.functionCenter
  let m : Quadratic E := ⟨cfg.Λ, u, g u⟩
  let inner := innerPass P Q m cfg.operatorCurvature s.operatorCenter (cfg.innerLast + 1)
  let v := inner.average
  have hi := inner_feasible hf.convex.1 P Q m cfg.operatorCurvature hs.2.2 (cfg.innerLast + 1)
  refine ⟨hi.1, hi.2, fun w hw => ?_⟩
  let τ := threshold g cfg u v (g u)
  have hupper := threshold_upper hf hs.2.1 hi.1
  change f v ≤ f u + ⟪g u, v - u⟫ + τ / 2 * ‖v - u‖ ^ 2 at hupper
  have hsupport := hf.support hs.2.1 hw
  change f u + ⟪g u, w - u⟫ ≤ f w at hsupport
  have hlin : ⟪g u, v - u⟫ - ⟪g u, w - u⟫ = ⟪g u, v⟫ - ⟪g u, w⟫ := by
    simp only [inner_sub_right]
    ring
  have hcompare :
      gap f Q v w + (cfg.Λ - τ) / 2 * ‖v - u‖ ^ 2 +
        cfg.Λ / 2 * (‖v - w‖ ^ 2 - ‖u - w‖ ^ 2) ≤ innerGap m Q w v := by
    unfold gap innerGap Quadratic.value model
    change _ ≤ cfg.Λ / 2 * ‖v - u‖ ^ 2 + ⟪g u, v⟫ -
      (cfg.Λ / 2 * ‖w - u‖ ^ 2 + ⟪g u, w⟫) +
      cfg.Λ / 2 * ‖v - w‖ ^ 2 + ⟪Q w, v - w⟫
    rw [norm_sub_rev w u]
    linarith only [hupper, hsupport, hlin]
  let k : ℝ := (cfg.innerLast : ℝ) + 1
  have hk : 0 < k := by dsimp [k]; positivity
  have hb := inner_pass_bound hf.convex.1 P (m := m) hΛ.le hH hQ hcurv hs.2.2 hw (cfg.innerLast + 1)
  change ((cfg.innerLast + 1 : ℕ) : ℝ) * innerGap m Q w v ≤ _ at hb
  rw [Nat.cast_succ] at hb
  have hb' : innerGap m Q w v ≤ cfg.operatorCurvature / (2 * k) *
      (‖s.operatorCenter - w‖ ^ 2 - ‖inner.center - w‖ ^ 2) := by
    apply le_of_mul_le_mul_right _ hk
    have heq : cfg.operatorCurvature / (2 * k) *
        (‖s.operatorCenter - w‖ ^ 2 - ‖inner.center - w‖ ^ 2) * k =
      cfg.operatorCurvature / 2 * (‖s.operatorCenter - w‖ ^ 2 - ‖inner.center - w‖ ^ 2) := by
      field_simp [hk.ne']
    rw [heq]
    rwa [mul_comm]
  have htotal := hcompare.trans hb'
  change gap f Q v w + (cfg.Λ - τ) / 2 * ‖v - u‖ ^ 2 ≤
    energy cfg w s - energy cfg w ⟨v, v, inner.center⟩
  dsimp only [energy, State.functionCenter, State.operatorCenter]
  change _ ≤ (cfg.Λ / 2 * ‖u - w‖ ^ 2 +
    cfg.operatorCurvature / (2 * k) * ‖s.operatorCenter - w‖ ^ 2) -
    (cfg.Λ / 2 * ‖v - w‖ ^ 2 + cfg.operatorCurvature / (2 * k) * ‖inner.center - w‖ ^ 2)
  linarith only [htotal]

theorem accepted_step {D : Set E} (P : Projection D) {f : E → ℝ} {g Q : E → E}
    {cfg : Config} (hf : FunctionOracle D f g cfg) {M : ℝ}
    (hQ : MonotoneLipschitz D Q M) (hΛ : 0 < cfg.Λ) (hH : 0 < cfg.operatorCurvature)
    (hcurv : 2 * M ≤ cfg.operatorCurvature) {n : ℕ} {prev next : State E}
    (hs : Feasible D prev) (hok : step P g Q cfg n prev = .ok next) :
    Feasible D next ∧ ∀ w ∈ D,
      ((n + 1 : ℕ) : ℝ) * gap f Q next.average w ≤
        (n : ℝ) * gap f Q prev.average w + energy cfg w prev - energy cfg w next := by
  let u := prev.functionCenter
  let inner := trial P Q cfg (g u) prev
  let v := inner.average
  have hi := trial_bound P hf hQ hΛ hH hcurv hs
  have ht : threshold g cfg u v (g u) ≤ cfg.Λ ∧
      next = ⟨meanStep n prev.average v, v, inner.center⟩ := by
    simp only [step] at hok
    split at hok
    · simp at hok
    · rename_i h
      exact ⟨le_of_not_gt h, (Except.ok.inj hok).symm⟩
  obtain ⟨hcheck, rfl⟩ := ht
  refine ⟨⟨mean_mem hf.convex.1 n hs.1 hi.1, hi.1, hi.2.1⟩, ?_⟩
  intro w hw
  have ha := gap_mean (Q := Q) hf.convex hs.1 hi.1 w n
  have hb := hi.2.2 w hw
  change gap f Q v w + (cfg.Λ - threshold g cfg u v (g u)) / 2 * ‖v - u‖ ^ 2 ≤
    energy cfg w prev - energy cfg w ⟨v, v, inner.center⟩ at hb
  have hn : 0 ≤ (cfg.Λ - threshold g cfg u v (g u)) / 2 * ‖v - u‖ ^ 2 := by
    positivity
  change ((n + 1 : ℕ) : ℝ) * gap f Q (meanStep n prev.average v) w ≤
    (n : ℝ) * gap f Q prev.average w + energy cfg w prev - energy cfg w ⟨v, v, inner.center⟩
  linarith only [ha, hb, hn]

private theorem pass_energy {D : Set E} (P : Projection D) {f : E → ℝ} {g Q : E → E}
    {cfg : Config} (hf : FunctionOracle D f g cfg) {M : ℝ}
    (hQ : MonotoneLipschitz D Q M) (hΛ : 0 < cfg.Λ) (hH : 0 < cfg.operatorCurvature)
    (hcurv : 2 * M ≤ cfg.operatorCurvature) {zin : E} (hz : zin ∈ D)
    (n : ℕ) {out : State E} (hok : (pass P g Q cfg zin n).result = .ok out) :
    Feasible D out ∧ ∀ w ∈ D,
      (n : ℝ) * gap f Q out.average w + energy cfg w out ≤ energy cfg w ⟨zin, zin, zin⟩ := by
  induction n generalizing out with
  | zero =>
    have he := Except.ok.inj hok
    subst out
    exact ⟨⟨hz, hz, hz⟩, by simp⟩
  | succ n ih =>
    cases hp : (pass P g Q cfg zin n).result with
    | error τ => simp only [pass, hp, reduceCtorEq] at hok
    | ok prev =>
      have hstep : step P g Q cfg n prev = .ok out := by simpa only [pass, hp] using hok
      have hs := ih hp
      have ht := accepted_step P hf hQ hΛ hH hcurv hs.1 hstep
      refine ⟨ht.1, fun w hw => ?_⟩
      linarith only [ht.2 w hw, hs.2 w hw]

def coefficient (cfg : Config) (n : ℕ) : ℝ :=
  cfg.Λ / (2 * (n : ℝ)) +
    cfg.operatorCurvature / (2 * ((n : ℝ) * ((cfg.innerLast : ℝ) + 1)))

/-- The output of the actual two loops has the unaccelerated gap bound. -/
theorem pass_gap {D : Set E} (P : Projection D) {f : E → ℝ} {g Q : E → E}
    {cfg : Config} (hf : FunctionOracle D f g cfg) {M : ℝ}
    (hQ : MonotoneLipschitz D Q M) (hΛ : 0 < cfg.Λ) (hH : 0 < cfg.operatorCurvature)
    (hcurv : 2 * M ≤ cfg.operatorCurvature) {zin : E} (hz : zin ∈ D)
    {n : ℕ} (hn : 0 < n) {out : State E} (hok : (pass P g Q cfg zin n).result = .ok out) :
    Feasible D out ∧ ∀ w ∈ D,
      gap f Q out.average w ≤ coefficient cfg n * ‖zin - w‖ ^ 2 := by
  have h := pass_energy P hf hQ hΛ hH hcurv hz n hok
  refine ⟨h.1, fun w hw => ?_⟩
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hT : 0 < (cfg.innerLast : ℝ) + 1 := by positivity
  have hpos : 0 ≤ energy cfg w out := by unfold energy; positivity
  have htotal := h.2 w hw
  apply le_of_mul_le_mul_left _ hn'
  have heq : (n : ℝ) * (coefficient cfg n * ‖zin - w‖ ^ 2) =
      energy cfg w ⟨zin, zin, zin⟩ := by
    dsimp [coefficient, energy]
    field_simp [hn'.ne', hT.ne']
  rw [heq]
  linarith only [htotal, hpos]

theorem coefficient_split (cfg : Config) (n : ℕ) (M : ℝ)
    (hH : cfg.operatorCurvature = 2 * M) :
    coefficient cfg n = cfg.Λ / (2 * (n : ℝ)) +
      M / ((n : ℝ) * ((cfg.innerLast : ℝ) + 1)) := by
  rw [coefficient, hH, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

/-- A successful pass used the full budget, with the two oracle counts separated. -/
theorem successful_counts {D : Set E} (P : Projection D) (g Q : E → E) (cfg : Config)
    (zin : E) {n : ℕ} {out : State E} (hok : (pass P g Q cfg zin n).result = .ok out) :
    (pass P g Q cfg zin n).calls =
      ⟨n * gradientsPerStep cfg, n * (2 * (cfg.innerLast + 1))⟩ := by
  induction n generalizing out with
  | zero => simp [pass]
  | succ n ih =>
    cases hp : (pass P g Q cfg zin n).result with
    | error τ => simp only [pass, hp, reduceCtorEq] at hok
    | ok prev =>
      simp only [pass, hp, ih hp, Calls.add]
      rw [Nat.succ_mul n (gradientsPerStep cfg), Nat.succ_mul n (2 * (cfg.innerLast + 1))]

/-- A secant check on the fixed working set requests at most twice its
gradient Lipschitz bound. -/
theorem secant_cap {D : Set E} {f : E → ℝ} {g : E → E} {cfg : Config} {A : ℝ}
    (hf : FunctionOracle D f g cfg) (hm : cfg.check = .secant) (hA : 0 ≤ A)
    (hlip : ∀ x ∈ D, ∀ y ∈ D, ‖g y - g x‖ ≤ A * ‖y - x‖) :
    ∀ x ∈ D, ∀ y ∈ D, threshold g cfg x y (g x) ≤ 2 * A := by
  intro x hx y hy
  simpa only [threshold, hm] using (secant_threshold hA (hf.support hy hx) (hlip x hx y hy)).2

private theorem step_outcome {D : Set E} (P : Projection D) (g Q : E → E) (cfg : Config)
    (hD : Convex ℝ D) {K : ℝ}
    (hK : ∀ x ∈ D, ∀ y ∈ D, threshold g cfg x y (g x) ≤ K)
    (n : ℕ) {s : State E} (hs : Feasible D s) :
    ValidOutcome D cfg.Λ K (step P g Q cfg n s) := by
  let m : Quadratic E := ⟨cfg.Λ, s.functionCenter, g s.functionCenter⟩
  let inner := innerPass P Q m cfg.operatorCurvature s.operatorCenter (cfg.innerLast + 1)
  have hi := inner_feasible hD P Q m cfg.operatorCurvature hs.2.2 (cfg.innerLast + 1)
  dsimp only [step]
  split_ifs with h
  · exact ⟨h, hK _ hs.2.1 _ hi.1⟩
  · exact ⟨mean_mem hD n hs.1 hi.1, hi⟩

private theorem pass_outcome {D : Set E} (P : Projection D) (g Q : E → E) (cfg : Config)
    (hD : Convex ℝ D) {K : ℝ}
    (hK : ∀ x ∈ D, ∀ y ∈ D, threshold g cfg x y (g x) ≤ K)
    {zin : E} (hz : zin ∈ D) (n : ℕ) :
    ValidOutcome D cfg.Λ K (pass P g Q cfg zin n).result := by
  induction n with
  | zero => exact ⟨hz, hz, hz⟩
  | succ n ih =>
    cases hp : (pass P g Q cfg zin n).result with
    | error τ => simpa only [pass, hp] using ih
    | ok s =>
      have hs : Feasible D s := by simpa only [hp, ValidOutcome] using ih
      simpa only [pass, hp] using step_outcome P g Q cfg hD hK n hs

/-- Retry on the same working set by increasing the model curvature.
The iterate centers are reset, and all calls from failed passes are retained. -/
def retry {D : Set E} (P : Projection D) (g Q : E → E) (zin : E) (n : ℕ) :
    ℕ → Config → Option (ℝ × State E) × Calls
  | 0, _ => (none, ⟨0, 0⟩)
  | k + 1, cfg =>
    let trial := pass P g Q cfg zin n
    match trial.result with
    | .ok out => (some (cfg.Λ, out), trial.calls)
    | .error τ =>
      let rest := retry P g Q zin n k { cfg with Λ := max (2 * cfg.Λ) τ }
      (rest.1, trial.calls.add rest.2)

/-- With a uniform cap K on the check, k+1 attempts suffice as soon as
2^k times the initial curvature covers K. The bound includes failed passes. -/
theorem retry_certificate {D : Set E} (P : Projection D) {f : E → ℝ} {g Q : E → E}
    {M K : ℝ} (hQ : MonotoneLipschitz D Q M)
    {zin : E} (hz : zin ∈ D) {n : ℕ} (hn : 0 < n) (k : ℕ)
    {cfg : Config} (hf : FunctionOracle D f g cfg) (hΛ : 0 < cfg.Λ)
    (hH : 0 < cfg.operatorCurvature) (hcurv : 2 * M ≤ cfg.operatorCurvature)
    (hK : ∀ x ∈ D, ∀ y ∈ D, threshold g cfg x y (g x) ≤ K) (hk : K ≤ (2 : ℝ) ^ k * cfg.Λ) :
    ∃ Λ out, (retry P g Q zin n (k + 1) cfg).1 = some (Λ, out) ∧
      0 < Λ ∧ Λ ≤ max cfg.Λ (2 * K) ∧ Feasible D out ∧
      (∀ w ∈ D, gap f Q out.average w ≤ coefficient { cfg with Λ := Λ } n * ‖zin - w‖ ^ 2) ∧
      (retry P g Q zin n (k + 1) cfg).2.gradients ≤ (k + 1) * (n * gradientsPerStep cfg) ∧
      (retry P g Q zin n (k + 1) cfg).2.operators ≤ (k + 1) * (n * (2 * (cfg.innerLast + 1))) := by
  have accepted (k : ℕ) (cfg : Config) (hf : FunctionOracle D f g cfg)
      (hΛ : 0 < cfg.Λ) (hH : 0 < cfg.operatorCurvature)
      (hc : 2 * M ≤ cfg.operatorCurvature) {out : State E}
      (ht : (pass P g Q cfg zin n).result = .ok out) :
      ∃ Λ out, (retry P g Q zin n (k + 1) cfg).1 = some (Λ, out) ∧
        0 < Λ ∧ Λ ≤ max cfg.Λ (2 * K) ∧ Feasible D out ∧
        (∀ w ∈ D, gap f Q out.average w ≤ coefficient { cfg with Λ := Λ } n * ‖zin - w‖ ^ 2) ∧
        (retry P g Q zin n (k + 1) cfg).2.gradients ≤ (k + 1) * (n * gradientsPerStep cfg) ∧
        (retry P g Q zin n (k + 1) cfg).2.operators ≤
          (k + 1) * (n * (2 * (cfg.innerLast + 1))) := by
    have hgap := pass_gap P hf hQ hΛ hH hc hz hn ht
    have hcount := pass_calls P g Q cfg zin n
    refine ⟨cfg.Λ, out, by simp only [retry, ht], hΛ, le_max_left .., hgap.1, hgap.2, ?_, ?_⟩
    · simp only [retry, ht]
      exact hcount.1.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    · simp only [retry, ht]
      exact hcount.2.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  induction k generalizing cfg with
  | zero =>
    cases ht : (pass P g Q cfg zin n).result with
    | error τ =>
      have he := pass_outcome P g Q cfg hf.convex.1 hK hz n
      rw [ht] at he
      have hle : K ≤ cfg.Λ := by simpa only [pow_zero, one_mul] using hk
      exact (not_lt_of_ge (he.2.trans hle) he.1).elim
    | ok out => exact accepted 0 cfg hf hΛ hH hcurv ht
  | succ k ih =>
    cases ht : (pass P g Q cfg zin n).result with
    | ok out => exact accepted (k + 1) cfg hf hΛ hH hcurv ht
    | error τ =>
      have he := pass_outcome P g Q cfg hf.convex.1 hK hz n
      rw [ht] at he
      have hupdate := curvature_update he.1 he.2 hΛ.le
      let next : Config := { cfg with Λ := max (2 * cfg.Λ) τ }
      have hnext : 0 < next.Λ := (show 0 < 2 * cfg.Λ by positivity).trans_le hupdate.1
      have hk' : K ≤ (2 : ℝ)^k * next.Λ := by
        apply hk.trans
        rw [pow_succ, mul_assoc]
        exact mul_le_mul_of_nonneg_left hupdate.1 (by positivity)
      have hf' : FunctionOracle D f g next := ⟨hf.convex, hf.support, hf.exponential⟩
      obtain ⟨Λ, out, hout, hpos, hcap, hfeasible, hgap, hgrad, hop⟩ :=
        ih hf' hnext hH hcurv hK hk'
      have hcount := pass_calls P g Q cfg zin n
      refine ⟨Λ, out, ?_, hpos, hcap.trans ?_, hfeasible, hgap, ?_, ?_⟩
      · simpa only [retry, ht] using hout
      · exact max_le (hupdate.2.trans (le_max_right ..)) (le_max_right ..)
      · simp only [retry, ht, Calls.add]
        change (pass P g Q cfg zin n).calls.gradients +
          (retry P g Q zin n (k + 1) next).2.gradients ≤ (k + 1 + 1) * (n * gradientsPerStep cfg)
        rw [Nat.succ_mul (k + 1) (n * gradientsPerStep cfg)]
        exact (Nat.add_le_add hcount.1 hgrad).trans_eq (Nat.add_comm ..)
      · simp only [retry, ht, Calls.add]
        change (pass P g Q cfg zin n).calls.operators +
          (retry P g Q zin n (k + 1) next).2.operators ≤
            (k + 1 + 1) * (n * (2 * (cfg.innerLast + 1)))
        rw [Nat.succ_mul (k + 1) (n * (2 * (cfg.innerLast + 1)))]
        exact (Nat.add_le_add hcount.2 hop).trans_eq (Nat.add_comm ..)

/-- The symmetric segment condition gives a uniform secant cap on any
convex working set with a uniform bound B on the gradient norm. -/
theorem secant_cap_of_symmetric {D : Set E} {f : E → ℝ} {g : E → E}
    {cfg : Config} {B : ℝ} (hf : FunctionOracle D f g cfg) (hm : cfg.check = .secant)
    (hL₀ : 0 ≤ cfg.L₀) (hL₁ : 0 ≤ cfg.L₁) (hB : 0 ≤ B)
    (hgrad : ∀ z ∈ D, ‖g z‖ ≤ B)
    (hsmooth : ∀ x ∈ D, ∀ y ∈ D, ‖g y - g x‖ ≤
      (cfg.L₀ + cfg.L₁ * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖y - x‖) :
    ∀ x ∈ D, ∀ y ∈ D, threshold g cfg x y (g x) ≤ 2 * (cfg.L₀ + cfg.L₁ * B) := by
  apply secant_cap hf hm (add_nonneg hL₀ (mul_nonneg hL₁ hB))
  intro x hx y hy
  have hn : ((fun z => ‖g z‖) '' segment ℝ x y).Nonempty :=
    ⟨‖g x‖, ⟨x, left_mem_segment ℝ x y, rfl⟩⟩
  have hsup : sSup ((fun z => ‖g z‖) '' segment ℝ x y) ≤ B := by
    apply csSup_le hn
    rintro _ ⟨z, hz, rfl⟩
    exact hgrad z (hf.convex.1.segment_subset hx hy hz)
  exact (hsmooth x hx y hy).trans <| mul_le_mul_of_nonneg_right
    (add_le_add_right (mul_le_mul_of_nonneg_left hsup hL₁) _) (norm_nonneg _)

/-- A positive initial curvature always admits a finite retry budget
when the check has a uniform upper bound. -/
theorem finite_retry {D : Set E} (P : Projection D) {f : E → ℝ} {g Q : E → E}
    {cfg : Config} {M K : ℝ} (hf : FunctionOracle D f g cfg) (hΛ : 0 < cfg.Λ)
    (hQ : MonotoneLipschitz D Q M) (hH : 0 < cfg.operatorCurvature)
    (hcurv : 2 * M ≤ cfg.operatorCurvature)
    (hK : ∀ x ∈ D, ∀ y ∈ D, threshold g cfg x y (g x) ≤ K)
    {zin : E} (hz : zin ∈ D) (n : ℕ) (hn : 0 < n) :
    ∃ k Λ out, (retry P g Q zin n (k + 1) cfg).1 = some (Λ, out) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (K / cfg.Λ) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨Λ, out, hout, _⟩ := retry_certificate P hQ hz hn k hf hΛ hH hcurv hK
    ((div_lt_iff₀ hΛ).mp hk).le
  exact ⟨k, Λ, out, hout⟩

/-- The two iteration budgets suffice for an absolute gap target on a
bounded working set. The same lemma applies to a restarted pass. -/
theorem accuracy {D : Set E} {f : E → ℝ} {Q : E → E} {z zin : E}
    {cfg : Config} {n : ℕ} {M R ε : ℝ} (hΛ : 0 ≤ cfg.Λ) (hM : 0 ≤ M)
    (hH : cfg.operatorCurvature = 2 * M) (hn : 0 < n)
    (hr : ∀ w ∈ D, ‖zin - w‖ ≤ R)
    (hgrad : cfg.Λ * R ^ 2 ≤ ε * (n : ℝ))
    (hop : 2 * M * R ^ 2 ≤ ε * ((n : ℝ) * ((cfg.innerLast : ℝ) + 1)))
    (hgap : ∀ w ∈ D, gap f Q z w ≤ coefficient cfg n * ‖zin - w‖ ^ 2) :
    ∀ w ∈ D, gap f Q z w ≤ ε := by
  intro w hw
  let t : ℝ := n
  let k : ℝ := (cfg.innerLast : ℝ) + 1
  have ht : 0 < t := Nat.cast_pos.mpr hn
  have hk : 0 < k := by dsimp [k]; positivity
  have hpos : 0 ≤ cfg.Λ / (2 * t) + M / (t * k) := by positivity
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (hr w hw) 2
  have hg := hgap w hw
  rw [coefficient_split cfg n M hH] at hg
  calc
    gap f Q z w ≤ (cfg.Λ / (2 * t) + M / (t * k)) * ‖zin - w‖ ^ 2 := hg
    _ ≤ (cfg.Λ / (2 * t) + M / (t * k)) * R ^ 2 := mul_le_mul_of_nonneg_left hnorm hpos
    _ = (cfg.Λ * R ^ 2) / (2 * t) + (M * R ^ 2) / (t * k) := by ring
    _ ≤ ε / 2 + ε / 2 := by
      apply add_le_add
      · apply (div_le_iff₀ (show 0 < 2 * t by positivity)).mpr
        change cfg.Λ * R ^ 2 ≤ ε * t at hgrad
        linarith only [hgrad]
      · apply (div_le_iff₀ (mul_pos ht hk)).mpr
        change 2 * M * R ^ 2 ≤ ε * (t * k) at hop
        linarith only [hop]
    _ = ε := by ring

end

end LeanLab.Sliding.TwoLevel.Plain
