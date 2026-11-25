module

public import LeanLab.SlidingGeneralizedSmoothness

set_option linter.style.header false

/-!
# Two-level sliding

The outer level models the smooth function. The inner level slides the
monotone operator against that fixed model. Both curvature checks use the
same inner loop and report their actual oracle counts.
-/

@[expose] public section

namespace LeanLab.Sliding.TwoLevel

open Set
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact projection onto the working set, specified by its normal inequality. -/
structure Projection (D : Set E) where
  apply : E → E
  feasible (x : E) : apply x ∈ D
  normal (x : E) {w : E} : w ∈ D → ⟪x - apply x, w - apply x⟫ ≤ 0

def mix (α : ℝ) (y v : E) : E := (1 - α) • y + α • v

theorem weight_le_one (j : ℕ) : weight j ≤ 1 := by
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  exact (weight_upper j).trans ((div_le_iff₀ (by positivity)).mpr (by linarith))

theorem weight_antitone : Antitone weight := by
  apply antitone_nat_of_succ_le
  intro j
  have h₀ := weight_pos j
  have h₁ := weight_pos (j + 1)
  have hrec := weight_recurrence j
  apply (le_of_pow_le_pow_left₀ (n := 2) (by decide) h₀.le)
  have hmul := (div_eq_div_iff (pow_ne_zero _ h₁.ne') (pow_ne_zero _ h₀.ne')).mp hrec
  nlinarith [mul_nonneg h₁.le (sq_nonneg (weight j))]

theorem mix_mem {D : Set E} (hD : Convex ℝ D) {α : ℝ}
    (hα : 0 ≤ α) (hα₁ : α ≤ 1) {y v : E} (hy : y ∈ D) (hv : v ∈ D) :
    mix α y v ∈ D :=
  hD hy hv (sub_nonneg.mpr hα₁) hα (sub_add_cancel 1 α)

/-- The two quadratics minimized in a leaf call. -/
structure Quadratic (E : Type*) where
  curvature : ℝ
  center : E
  slope : E

def Quadratic.value (m : Quadratic E) (z : E) : ℝ :=
  model m.curvature m.center m.slope z

def leaf {D : Set E} (P : Projection D) (m q : Quadratic E) : E :=
  P.apply ((m.curvature + q.curvature)⁻¹ •
    (m.curvature • m.center + q.curvature • q.center - (m.slope + q.slope)))

/-- The average and the correction point of the inner level. -/
structure InnerState (E : Type*) where
  average : E
  center : E

/-- An operator trial and its correction, using the same fixed function model. -/
def operatorStep {D : Set E} (P : Projection D) (Q : E → E) (m : Quadratic E)
    (H : ℝ) (u : E) : InnerState E :=
  let q := Q u
  let v := leaf P m ⟨H, u, q⟩
  ⟨v, P.apply (v + H⁻¹ • (q - Q v))⟩

def innerStep {D : Set E} (P : Projection D) (Q : E → E) (m : Quadratic E)
    (curvature : ℝ) (j : ℕ) (s : InnerState E) : InnerState E :=
  let step := operatorStep P Q m (weight j * curvature) s.center
  ⟨mix (weight j) s.average step.average, step.center⟩

def innerRun {D : Set E} (P : Projection D) (Q : E → E) (m : Quadratic E)
    (curvature : ℝ) (u : E) : ℕ → InnerState E
  | 0 => ⟨u, u⟩
  | j + 1 => innerStep P Q m curvature j (innerRun P Q m curvature u j)

inductive Check
  | exponential
  | secant
  deriving DecidableEq

structure Calls where
  gradients : ℕ
  operators : ℕ
  deriving DecidableEq

structure State (E : Type*) where
  average : E
  functionCenter : E
  operatorCenter : E

structure Run (E : Type*) where
  result : Except ℝ (State E)
  calls : Calls

structure Config where
  L₀ : ℝ
  L₁ : ℝ
  Λ : ℝ
  operatorCurvature : ℝ
  innerLast : ℕ
  check : Check

def scale (cfg : Config) (j : ℕ) : ℝ := weight j * cfg.operatorCurvature

def gradientsPerStep (cfg : Config) : ℕ :=
  match cfg.check with
  | .exponential => 1
  | .secant => 2

def threshold (g : E → E) (cfg : Config) (x y gx : E) : ℝ :=
  match cfg.check with
  | .exponential => (cfg.L₀ + cfg.L₁ * ‖gx‖) * Real.exp (cfg.L₁ * ‖y - x‖)
  | .secant => 2 * ⟪g y - gx, y - x⟫ / ‖y - x‖ ^ 2

/-- A failed step retains its oracle counts and requests a larger curvature.
The operator-only component has zero function and needs no gradient check. -/
def outerStep {D : Set E} (P : Projection D) (g Q : E → E) (cfg : Config)
    (j : ℕ) (s : State E) : Run E :=
  let α := weight j
  let x := mix α s.average s.functionCenter
  let gx := g x
  let A := cfg.L₀ + cfg.L₁ * ‖gx‖
  if cfg.Λ < 4 * A then ⟨.error (4 * A), ⟨1, 0⟩⟩
  else
    let m : Quadratic E := ⟨α * cfg.Λ, s.functionCenter, gx⟩
    let inner := innerRun P Q m (scale cfg j) s.operatorCenter (cfg.innerLast + 1)
    let y := mix α s.average inner.average
    let τ := threshold g cfg x y gx
    let calls : Calls := ⟨gradientsPerStep cfg, 2 * (cfg.innerLast + 1)⟩
    if cfg.Λ < τ then ⟨.error τ, calls⟩
    else ⟨.ok ⟨y, inner.average, inner.center⟩, calls⟩

/-- Counts are accumulated until the first failed check. -/
def outerRun {D : Set E} (P : Projection D) (g Q : E → E) (cfg : Config)
    (zin : E) : ℕ → Run E
  | 0 => ⟨.ok ⟨zin, zin, zin⟩, ⟨0, 0⟩⟩
  | j + 1 =>
    let previous := outerRun P g Q cfg zin j
    match previous.result with
    | .error _ => previous
    | .ok s =>
      let step := outerStep P g Q cfg j s
      ⟨step.result, ⟨previous.calls.gradients + step.calls.gradients,
        previous.calls.operators + step.calls.operators⟩⟩

theorem step_calls {D : Set E} (P : Projection D) (g Q : E → E) (cfg : Config)
    (j : ℕ) (s : State E) :
    (outerStep P g Q cfg j s).calls.gradients ≤ gradientsPerStep cfg ∧
    (outerStep P g Q cfg j s).calls.operators ≤ 2 * (cfg.innerLast + 1) := by
  dsimp only [outerStep]
  split_ifs
  · cases h : cfg.check <;> simp [gradientsPerStep, h]
  all_goals simp

theorem run_calls {D : Set E} (P : Projection D) (g Q : E → E) (cfg : Config)
    (zin : E) (j : ℕ) :
    (outerRun P g Q cfg zin j).calls.gradients ≤ j * gradientsPerStep cfg ∧
    (outerRun P g Q cfg zin j).calls.operators ≤ j * (2 * (cfg.innerLast + 1)) := by
  induction j with
  | zero => simp [outerRun]
  | succ j ih =>
    cases hr : (outerRun P g Q cfg zin j).result with
    | error err =>
      simp only [outerRun, hr]
      rw [Nat.succ_mul j (gradientsPerStep cfg), Nat.succ_mul j (2 * (cfg.innerLast + 1))]
      exact ⟨ih.1.trans (Nat.le_add_right ..), ih.2.trans (Nat.le_add_right ..)⟩
    | ok s =>
      simp only [outerRun, hr]
      rw [Nat.succ_mul j (gradientsPerStep cfg), Nat.succ_mul j (2 * (cfg.innerLast + 1))]
      exact ⟨Nat.add_le_add ih.1 (step_calls P g Q cfg j s).1,
        Nat.add_le_add ih.2 (step_calls P g Q cfg j s).2⟩

/-- Three-point identity for a quadratic plus a linear term. -/
private theorem Quadratic.expand (m : Quadratic E) (v w : E) :
    m.value w - m.value v - m.curvature / 2 * ‖v - w‖ ^ 2 =
      ⟪m.curvature • (v - m.center) + m.slope, w - v⟫ := by
  have hw : w - m.center = (v - m.center) + (w - v) := by abel
  have hn : ‖w - m.center‖ ^ 2 =
      ‖v - m.center‖ ^ 2 + 2 * ⟪v - m.center, w - v⟫ + ‖v - w‖ ^ 2 := by
    conv_lhs => rw [hw, norm_add_sq_real, norm_sub_rev w v]
  simp only [Quadratic.value, model, hn, inner_add_left, real_inner_smul_left]
  rw [show ⟪m.slope, w - v⟫ = ⟪m.slope, w⟫ - ⟪m.slope, v⟫ from inner_sub_right ..]
  ring

private theorem leaf_minimum {D : Set E} (P : Projection D) (m q : Quadratic E)
    (hH : 0 < m.curvature + q.curvature) {w : E} (hw : w ∈ D) :
    let v := leaf P m q
    m.value v - m.value w + q.value v - q.value w +
      (m.curvature + q.curvature) / 2 * ‖v - w‖ ^ 2 ≤ 0 := by
  let H := m.curvature + q.curvature
  let n := m.curvature • m.center + q.curvature • q.center - (m.slope + q.slope)
  let v := leaf P m q
  have hn := P.normal (H⁻¹ • n) hw
  change ⟪H⁻¹ • n - v, w - v⟫ ≤ 0 at hn
  have hsum : (m.curvature • (v - m.center) + m.slope) +
      (q.curvature • (v - q.center) + q.slope) = -(H • (H⁻¹ • n - v)) := by
    conv_rhs => rw [smul_sub, smul_smul, mul_inv_cancel₀ (show H ≠ 0 from hH.ne'), one_smul]
    dsimp [H, n]
    module
  have hpos : 0 ≤ ⟪(m.curvature • (v - m.center) + m.slope) +
      (q.curvature • (v - q.center) + q.slope), w - v⟫ := by
    rw [hsum, inner_neg_left, real_inner_smul_left]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hH.le hn)
  rw [inner_add_left, ← m.expand, ← q.expand] at hpos
  change m.value v - m.value w + q.value v - q.value w +
    (m.curvature + q.curvature) / 2 * ‖v - w‖ ^ 2 ≤ 0
  linarith only [hpos]

private theorem mix_sub {α : ℝ} {y v c : E} :
    mix α y v - c = (1 - α) • (y - c) + α • (v - c) := by
  unfold mix
  module

private theorem norm_sq_mix {α : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1) (y v c : E) :
    ‖mix α y v - c‖ ^ 2 ≤ (1 - α) * ‖y - c‖ ^ 2 + α * ‖v - c‖ ^ 2 := by
  have h₁ := sub_nonneg.mpr hα₁
  have hn := norm_add_le ((1 - α) • (y - c)) (α • (v - c))
  rw [← mix_sub, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg h₁, abs_of_nonneg hα] at hn
  calc
    _ ≤ ((1 - α) * ‖y - c‖ + α * ‖v - c‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ _ := by
      nlinarith only [mul_nonneg (mul_nonneg h₁ hα) (sq_nonneg (‖y - c‖ - ‖v - c‖))]

def innerGap (m : Quadratic E) (Q : E → E) (w z : E) : ℝ :=
  m.value z - m.value w + m.curvature / 2 * ‖z - w‖ ^ 2 + ⟪Q w, z - w⟫

theorem innerGap_mix (m : Quadratic E) (Q : E → E) (w y v : E) {α : ℝ}
    (hα : 0 ≤ α) (hα₁ : α ≤ 1) (hm : 0 ≤ m.curvature) :
    innerGap m Q w (mix α y v) ≤ (1 - α) * innerGap m Q w y + α * innerGap m Q w v := by
  have hc : 0 ≤ m.curvature / 2 := by positivity
  have h₁ := mul_le_mul_of_nonneg_left (norm_sq_mix hα hα₁ y v m.center) hc
  have h₂ := mul_le_mul_of_nonneg_left (norm_sq_mix hα hα₁ y v w) hc
  simp only [innerGap, Quadratic.value, model]
  rw [show ⟪m.slope, mix α y v⟫ = (1 - α) * ⟪m.slope, y⟫ + α * ⟪m.slope, v⟫ by
    simp [mix, inner_add_right, real_inner_smul_right]]
  rw [show ⟪Q w, mix α y v - w⟫ =
      (1 - α) * ⟪Q w, y - w⟫ + α * ⟪Q w, v - w⟫ by
    rw [mix_sub, inner_add_right, real_inner_smul_right, real_inner_smul_right]]
  linarith only [h₁, h₂]

/-- The only analytic premises for the operator level. -/
structure MonotoneLipschitz (D : Set E) (Q : E → E) (M : ℝ) : Prop where
  nonneg : 0 ≤ M
  monotone {v w : E} : v ∈ D → w ∈ D → 0 ≤ ⟪Q v - Q w, v - w⟫
  lipschitz {u v : E} : u ∈ D → v ∈ D → ‖Q u - Q v‖ ≤ M * ‖v - u‖

private theorem inner_feasible {D : Set E} (hD : Convex ℝ D)
    (P : Projection D) (Q : E → E) (m : Quadratic E) (c : ℝ) {u : E} (hu : u ∈ D)
    (j : ℕ) : (innerRun P Q m c u j).average ∈ D ∧ (innerRun P Q m c u j).center ∈ D := by
  induction j with
  | zero => exact ⟨hu, hu⟩
  | succ j ih =>
    exact ⟨mix_mem hD (weight_pos j).le (weight_le_one j) ih.1 (P.feasible _), P.feasible _⟩

/-- One operator trial pays for its gap by reducing the squared distance
of the correction point. Averaging and acceleration are independent of this step. -/
theorem operator_step_bound {D : Set E} (P : Projection D) {Q : E → E}
    {m : Quadratic E} {H M : ℝ} (hm : 0 ≤ m.curvature) (hH : 0 < H)
    (hQ : MonotoneLipschitz D Q M) {w start : E} (hw : w ∈ D)
    (hs : start ∈ D) (hcurv : 2 * M ≤ H) :
    let next := operatorStep P Q m H start
    innerGap m Q w next.average ≤ H / 2 * (‖start - w‖ ^ 2 - ‖next.center - w‖ ^ 2) := by
  let q : Quadratic E := ⟨H, start, Q start⟩
  let v := leaf P m q
  let u := P.apply (v + H⁻¹ • (Q start - Q v))
  have hv : v ∈ D := P.feasible _
  have hleaf := leaf_minimum P m q (add_pos_of_nonneg_of_pos hm hH) hw
  change m.value v - m.value w + q.value v - q.value w +
    (m.curvature + H) / 2 * ‖v - w‖ ^ 2 ≤ 0 at hleaf
  have hmodel := model_comparison (f := fun _ : E => 0) (g := 0) (ℓ := 0)
    hH (by rfl) hQ.nonneg (by simpa only [zero_add] using hcurv)
    (by simp) (by simp) (hQ.monotone hv hw) (hQ.lipschitz hs hv)
    (P.normal (v + H⁻¹ • (Q start - Q v)) hw)
  have hcorrect : ⟪Q w, v - w⟫ + H / 2 * (‖u - w‖ ^ 2 - ‖start - w‖ ^ 2) ≤
      q.value v - q.value w + H / 2 * ‖v - w‖ ^ 2 := by
    simpa only [gap, sub_self, zero_add, Quadratic.value] using hmodel
  change innerGap m Q w v ≤ H / 2 * (‖start - w‖ ^ 2 - ‖u - w‖ ^ 2)
  unfold innerGap
  linarith only [hleaf, hcorrect]

private theorem inner_step_bound {D : Set E} (P : Projection D) {Q : E → E}
    {m : Quadratic E} {c M : ℝ} (hm : 0 ≤ m.curvature) (hc : 0 < c)
    (hQ : MonotoneLipschitz D Q M) {w : E} (hw : w ∈ D)
    (j : ℕ) (s : InnerState E) (hs : s.center ∈ D) (hcurv : 2 * M ≤ weight j * c) :
    let next := innerStep P Q m c j s
    (innerGap m Q w next.average - (1 - weight j) * innerGap m Q w s.average) /
      weight j ^ 2 ≤ c / 2 * (‖s.center - w‖ ^ 2 - ‖next.center - w‖ ^ 2) := by
  let α := weight j
  let H := α * c
  let step := operatorStep P Q m H s.center
  let v := step.average
  let u := step.center
  have hα : 0 < α := weight_pos j
  have hb := operator_step_bound P hm (mul_pos hα hc) hQ hw hs hcurv
  change innerGap m Q w v ≤ α * c / 2 * (‖s.center - w‖ ^ 2 - ‖u - w‖ ^ 2) at hb
  have hpot : innerGap m Q w v + α * c / 2 * (‖u - w‖ ^ 2 - ‖s.center - w‖ ^ 2) ≤ 0 := by
    linarith only [hb]
  have hmix := innerGap_mix m Q w s.average v hα.le (weight_le_one j) hm
  change (innerGap m Q w (mix α s.average v) - (1 - α) * innerGap m Q w s.average) /
    α ^ 2 ≤ c / 2 * (‖s.center - w‖ ^ 2 - ‖u - w‖ ^ 2)
  apply (div_le_iff₀ (sq_pos_of_pos hα)).mpr
  have hbat := mul_le_mul_of_nonneg_left hpot hα.le
  change α * (innerGap m Q w v + α * c / 2 * _) ≤ α * 0 at hbat
  linarith only [hmix, hbat]

/-- The computed inner loop returns the bound used by the outer level. -/
theorem inner_run_bound {D : Set E} (hD : Convex ℝ D) (P : Projection D)
    {Q : E → E} {m : Quadratic E} {c M : ℝ} (hm : 0 ≤ m.curvature) (hc : 0 < c)
    (hQ : MonotoneLipschitz D Q M) {w u : E} (hw : w ∈ D) (hu : u ∈ D)
    (last : ℕ) (hcurv : 2 * M ≤ weight last * c) :
    let s := innerRun P Q m c u (last + 1)
    innerGap m Q w s.average ≤ weight last ^ 2 * c / 2 * (‖u - w‖ ^ 2 - ‖s.center - w‖ ^ 2) := by
  let trace := innerRun P Q m c u
  have h := telescope (F := fun t => innerGap m Q w (trace t).average)
    (P := fun t => c / 2 * ‖(trace t).center - w‖ ^ 2)
    weight_pos weight_zero weight_recurrence last (by
      intro j hj
      have hcurv' := hcurv.trans (mul_le_mul_of_nonneg_right (weight_antitone hj) hc.le)
      have hs := (inner_feasible hD P Q m c hu j).2
      simpa only [trace, innerRun, ← mul_sub] using inner_step_bound P hm hc hQ hw j _ hs hcurv')
  change innerGap m Q w (trace (last + 1)).average ≤ _
  change _ ≤ weight last ^ 2 * (c / 2 * ‖u - w‖ ^ 2 -
    c / 2 * ‖(trace (last + 1)).center - w‖ ^ 2) at h
  exact h.trans_eq (by ring)

/-- The function oracle hypotheses on the working set. The exponential
model is Lemma 2.1 of Gorbunov et al.; the secant mode only uses support. -/
structure FunctionOracle (D : Set E) (f : E → ℝ) (g : E → E) (cfg : Config) : Prop where
  convex : ConvexOn ℝ D f
  support {x y : E} : x ∈ D → y ∈ D → f x + ⟪g x, y - x⟫ ≤ f y
  exponential {x y : E} : cfg.check = .exponential → x ∈ D → y ∈ D →
    f y ≤ f x + ⟪g x, y - x⟫ +
      (cfg.L₀ + cfg.L₁ * ‖g x‖) * Real.exp (cfg.L₁ * ‖y - x‖) / 2 * ‖y - x‖ ^ 2

theorem threshold_upper {D : Set E} {f : E → ℝ} {g : E → E} {cfg : Config}
    (hf : FunctionOracle D f g cfg) {x y : E} (hx : x ∈ D) (hy : y ∈ D) :
    f y ≤ f x + ⟪g x, y - x⟫ + threshold g cfg x y (g x) / 2 * ‖y - x‖ ^ 2 := by
  cases he : cfg.check with
  | exponential =>
    simpa only [threshold, he] using hf.exponential he hx hy
  | secant =>
    let A := ‖g y - g x‖ / ‖y - x‖
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hgrad : ‖g y - g x‖ ≤ A * ‖y - x‖ := by
      by_cases hh : y = x
      · subst y; simp
      · rw [show A * ‖y - x‖ = ‖g y - g x‖ from
          div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hh))]
    simpa only [threshold, he] using (secant_threshold hA (hf.support hy hx) hgrad).1

def Feasible (D : Set E) (s : State E) : Prop :=
  s.average ∈ D ∧ s.functionCenter ∈ D ∧ s.operatorCenter ∈ D

/-- The potential with the fixed coefficients of the outer pass. -/
def energy (cfg : Config) (w : E) (s : State E) : ℝ :=
  cfg.Λ / 2 * ‖s.functionCenter - w‖ ^ 2 +
    weight cfg.innerLast ^ 2 * cfg.operatorCurvature / 2 * ‖s.operatorCenter - w‖ ^ 2

/-- The outer recurrence follows from the actual accepted step and
the computed inner loop. -/
theorem outer_step_bound {D : Set E} (P : Projection D) {f : E → ℝ} {g Q : E → E}
    {cfg : Config} (hf : FunctionOracle D f g cfg) {M : ℝ}
    (hQ : MonotoneLipschitz D Q M) (hΛ : 0 < cfg.Λ)
    (hc : 0 < cfg.operatorCurvature)
    {j : ℕ} (hcurv : 2 * M ≤ weight cfg.innerLast * scale cfg j)
    {s next : State E} (hs : Feasible D s)
    (hstep : (outerStep P g Q cfg j s).result = .ok next) :
    Feasible D next ∧ ∀ w ∈ D,
      (gap f Q next.average w - (1 - weight j) * gap f Q s.average w) / weight j ^ 2 ≤
        energy cfg w s - energy cfg w next := by
  let α := weight j
  let x := mix α s.average s.functionCenter
  let m : Quadratic E := ⟨α * cfg.Λ, s.functionCenter, g x⟩
  let inner := innerRun P Q m (scale cfg j) s.operatorCenter (cfg.innerLast + 1)
  let v := inner.average
  let y := mix α s.average v
  have hα : 0 < α := weight_pos j
  have hα₁ : α ≤ 1 := weight_le_one j
  have hm : 0 < m.curvature := mul_pos hα hΛ
  have hscale : 0 < scale cfg j := mul_pos hα hc
  have hx := mix_mem hf.convex.1 hα.le hα₁ hs.1 hs.2.1
  have hv := inner_feasible hf.convex.1 P Q m (scale cfg j) hs.2.2 (cfg.innerLast + 1)
  have hy := mix_mem hf.convex.1 hα.le hα₁ hs.1 hv.1
  have hex :
      ¬ cfg.Λ < 4 * (cfg.L₀ + cfg.L₁ * ‖g x‖) ∧
        ¬ cfg.Λ < threshold g cfg x y (g x) ∧ next = ⟨y, v, inner.center⟩ := by
    dsimp only [outerStep] at hstep
    split at hstep
    · simp at hstep
    · rename_i hfirst
      split at hstep
      · simp at hstep
      · rename_i hcheck
        exact ⟨hfirst, hcheck, (Except.ok.inj hstep).symm⟩
  obtain ⟨_, hcheck, rfl⟩ := hex
  refine ⟨⟨hy, hv.1, hv.2⟩, ?_⟩
  intro w hw
  let φ := fun z => f (mix α s.average z) / α
  have hmaj := threshold_upper hf hx hy
  have hmaj' : f y ≤ f x + ⟪g x, y - x⟫ + cfg.Λ / 2 * ‖y - x‖ ^ 2 :=
    hmaj.trans (add_le_add_right
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (le_of_not_gt hcheck) (by norm_num : (0 : ℝ) ≤ 2))
      (sq_nonneg ‖y - x‖)) _)
  have hup : φ v ≤ φ s.functionCenter + ⟪g x, v - s.functionCenter⟫ +
      m.curvature / 2 * ‖v - s.functionCenter‖ ^ 2 := by
    have h := affine_model (f := f) (β := α) (b := (1 - α) • s.average)
      (τ := cfg.Λ) (u := s.functionCenter) (v := v) (g := g x) hα (by
        simpa only [x, y, mix, add_comm] using hmaj')
    simpa only [φ, m, mix, add_comm] using h
  have hw' := mix_mem hf.convex.1 hα.le hα₁ hs.1 hw
  have hsup := hf.support hx hw'
  have hd : mix α s.average w - x = α • (w - s.functionCenter) := by
    dsimp [x, mix]
    module
  rw [hd, real_inner_smul_right] at hsup
  have hsupp : φ s.functionCenter + ⟪g x, w - s.functionCenter⟫ ≤ φ w := by
    dsimp only [φ]
    apply (le_div_iff₀ hα).mpr
    rw [add_mul, div_mul_cancel₀ _ hα.ne']
    linarith only [hsup]
  have hmodel := model_comparison (f := φ) (Q := fun _ : E => 0) (next := v)
    (M := 0) hm hm.le (by rfl) (by simp) hup hsupp (by simp) (by simp) (by simp)
  have hmodel' : φ v - φ w + m.curvature / 2 *
      (‖v - w‖ ^ 2 - ‖s.functionCenter - w‖ ^ 2) ≤
        m.value v - m.value w + m.curvature / 2 * ‖v - w‖ ^ 2 := by
    simpa only [gap, Quadratic.value, add_zero, inner_zero_left] using hmodel
  have hchild := inner_run_bound hf.convex.1 P hm.le hscale hQ hw hs.2.2 cfg.innerLast hcurv
  let r := fun z => ⟪Q w, z⟫
  have hr : ConvexOn ℝ D r := by
    refine ⟨hf.convex.1, ?_⟩
    intro a ha b hb c d hc' hd' he
    simp [r, inner_add_right, real_inner_smul_right]
  have ht := transfer (f := f) (r := r) (child := innerGap m Q w v) hf.convex hr
    hs.1 hv.1 hw hα hα₁ (correction := m.curvature / 2 *
      (‖v - w‖ ^ 2 - ‖s.functionCenter - w‖ ^ 2)) (by
        unfold innerGap
        rw [inner_sub_right]
        simp only [φ, r, mix, sub_div] at hmodel' ⊢
        linarith only [hmodel'])
  have hgap (z : E) : f z + r z - (f w + r w) = gap f Q z w := by
    simp only [gap, r, inner_sub_right]
    ring
  rw [hgap, hgap] at ht
  change innerGap m Q w v ≤ weight cfg.innerLast ^ 2 * scale cfg j / 2 *
    (‖s.operatorCenter - w‖ ^ 2 - ‖inner.center - w‖ ^ 2) at hchild
  have hboth := mul_le_mul_of_nonneg_right (ht.trans hchild) hα.le
  rw [add_mul, div_mul_cancel₀ _ hα.ne'] at hboth
  apply (div_le_iff₀ (sq_pos_of_pos hα)).mpr
  dsimp only [energy, State.average, State.functionCenter, State.operatorCenter]
  change gap f Q y w - (1 - α) * gap f Q s.average w ≤ _
  change gap f Q y w - (1 - α) * gap f Q s.average w +
    (α * cfg.Λ / 2 * (‖v - w‖ ^ 2 - ‖s.functionCenter - w‖ ^ 2)) * α ≤
      (weight cfg.innerLast ^ 2 * (α * cfg.operatorCurvature) / 2 *
        (‖s.operatorCenter - w‖ ^ 2 - ‖inner.center - w‖ ^ 2)) * α at hboth
  linarith only [hboth]

private theorem previous_ok {D : Set E} (P : Projection D) (g Q : E → E) (cfg : Config)
    (zin : E) {j : ℕ} {s : State E}
    (hrun : (outerRun P g Q cfg zin (j + 1)).result = .ok s) :
    ∃ previous, (outerRun P g Q cfg zin j).result = .ok previous ∧
      (outerStep P g Q cfg j previous).result = .ok s := by
  cases hp : (outerRun P g Q cfg zin j).result with
  | error err =>
    simp only [outerRun, hp, reduceCtorEq] at hrun
  | ok previous =>
    exact ⟨previous, rfl, by simpa only [outerRun, hp] using hrun⟩

/-- Energy bound for a successful prefix of an actual run. -/
theorem run_energy {D : Set E} (P : Projection D) {f : E → ℝ} {g Q : E → E}
    {cfg : Config} (hf : FunctionOracle D f g cfg) {M : ℝ}
    (hQ : MonotoneLipschitz D Q M) (hΛ : 0 < cfg.Λ)
    (hc : 0 < cfg.operatorCurvature) {zin : E} (hz : zin ∈ D)
    (last : ℕ) (hcurv : 2 * M ≤ weight cfg.innerLast * scale cfg last)
    {s : State E} (hrun : (outerRun P g Q cfg zin (last + 1)).result = .ok s) :
    Feasible D s ∧ ∀ w ∈ D, gap f Q s.average w / weight last ^ 2 + energy cfg w s ≤
      energy cfg w ⟨zin, zin, zin⟩ := by
  induction last generalizing s with
  | zero =>
    have h := outer_step_bound P hf hQ hΛ hc hcurv (s := ⟨zin, zin, zin⟩) ⟨hz, hz, hz⟩
      (by simpa only [outerRun] using hrun)
    refine ⟨h.1, fun w hw => ?_⟩
    have hstep := h.2 w hw
    simp [weight_zero] at hstep ⊢
    linarith only [hstep]
  | succ j ih =>
    obtain ⟨prev, hprev, hstep⟩ := previous_ok P g Q cfg zin hrun
    have hcurv' : 2 * M ≤ weight cfg.innerLast * scale cfg j := hcurv.trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (weight_antitone (Nat.le_succ j)) hc.le)
        (weight_pos cfg.innerLast).le)
    have hprev' := ih hcurv' hprev
    have hstep' := outer_step_bound P hf hQ hΛ hc hcurv hprev'.1 hstep
    refine ⟨hstep'.1, fun w hw => ?_⟩
    have hb := hstep'.2 w hw
    rw [sub_div, mul_comm (1 - weight (j + 1)), mul_div_assoc, weight_recurrence,
      mul_one_div] at hb
    linarith only [hb, hprev'.2 w hw]

def gapCoefficient (cfg : Config) (last : ℕ) : ℝ :=
  weight last ^ 2 * (cfg.Λ + weight cfg.innerLast ^ 2 * cfg.operatorCurvature) / 2

/-- A successful two-level pass satisfies the gap estimate on its working set. -/
theorem run_gap {D : Set E} (P : Projection D) {f : E → ℝ} {g Q : E → E}
    {cfg : Config} (hf : FunctionOracle D f g cfg) {M : ℝ}
    (hQ : MonotoneLipschitz D Q M) (hΛ : 0 < cfg.Λ) (hc : 0 < cfg.operatorCurvature)
    {zin : E} (hz : zin ∈ D) (last : ℕ) (hcurv : 2 * M ≤ weight cfg.innerLast * scale cfg last)
    {s : State E} (hrun : (outerRun P g Q cfg zin (last + 1)).result = .ok s)
    {w : E} (hw : w ∈ D) :
    gap f Q s.average w ≤ gapCoefficient cfg last * ‖zin - w‖ ^ 2 := by
  have ht := (run_energy P hf hQ hΛ hc hz last hcurv hrun).2 w hw
  have hp : 0 ≤ energy cfg w s := by unfold energy; positivity
  have h := (div_le_iff₀ (sq_pos_of_pos (weight_pos last))).mp
    (show gap f Q s.average w / weight last ^ 2 ≤ energy cfg w ⟨zin, zin, zin⟩ by linarith)
  refine h.trans_eq ?_
  dsimp [energy, gapCoefficient]
  ring

/-- With operator curvature chosen as in the draft, the checked bound
has separate function and operator terms. Here the operator-only model
has no artificial smoothness term. -/
theorem gapCoefficient_split (cfg : Config) (last : ℕ) (M : ℝ)
    (hcfg : cfg.operatorCurvature = 2 * M / (weight last * weight cfg.innerLast)) :
    gapCoefficient cfg last = weight last ^ 2 * cfg.Λ / 2 +
      weight last * weight cfg.innerLast * M := by
  have ho := (weight_pos last).ne'
  have hi := (weight_pos cfg.innerLast).ne'
  unfold gapCoefficient
  rw [hcfg]
  field_simp

private theorem step_mix {D : Set E} (P : Projection D) (g Q : E → E) (cfg : Config) (j : ℕ)
    {s next : State E} (hstep : (outerStep P g Q cfg j s).result = .ok next) :
    next.average = mix (weight j) s.average next.functionCenter := by
  dsimp only [outerStep] at hstep
  split at hstep
  · simp at hstep
  · split at hstep
    · simp at hstep
    · cases (Except.ok.inj hstep)
      rfl

/-- A balanced run stays within √2 times the initial distance from a
solution. The function center is the trial point because Q₁ is zero. -/
theorem run_radius {D : Set E} (P : Projection D) {f : E → ℝ} {g Q : E → E}
    {cfg : Config} (hf : FunctionOracle D f g cfg) {M : ℝ}
    (hQ : MonotoneLipschitz D Q M) (hΛ : 0 < cfg.Λ) (hc : 0 < cfg.operatorCurvature)
    (hbalance : weight cfg.innerLast ^ 2 * cfg.operatorCurvature ≤ cfg.Λ)
    {zin solution : E} (hz : zin ∈ D) (hs : solution ∈ D)
    (hsolution : ∀ z ∈ D, 0 ≤ gap f Q z solution) (last : ℕ)
    (hcurv : 2 * M ≤ weight cfg.innerLast * scale cfg last)
    {s : State E} (hrun : (outerRun P g Q cfg zin (last + 1)).result = .ok s) :
    ‖s.average - solution‖ ≤ Real.sqrt 2 * ‖zin - solution‖ := by
  have hcenter {j : ℕ} {out : State E}
      (hcurv' : 2 * M ≤ weight cfg.innerLast * scale cfg j)
      (hrun' : (outerRun P g Q cfg zin (j + 1)).result = .ok out) :
      ‖out.functionCenter - solution‖ ≤ Real.sqrt 2 * ‖zin - solution‖ := by
    obtain ⟨hfeas, henergy⟩ := run_energy P hf hQ hΛ hc hz j hcurv' hrun'
    have h := henergy solution hs
    have hgap := div_nonneg (hsolution _ hfeas.1) (sq_nonneg (weight j))
    have hfinal : 0 ≤ weight cfg.innerLast ^ 2 * cfg.operatorCurvature / 2 *
        ‖out.operatorCenter - solution‖ ^ 2 := by positivity
    have hinit := mul_le_mul_of_nonneg_right hbalance (sq_nonneg ‖zin - solution‖)
    have hsq : ‖out.functionCenter - solution‖ ^ 2 ≤ 2 * ‖zin - solution‖ ^ 2 := by
      apply le_of_mul_le_mul_left _ hΛ
      dsimp [energy] at h
      linarith only [h, hgap, hfinal, hinit]
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    exact hsq
  induction last generalizing s with
  | zero =>
    have hmix := step_mix P g Q cfg 0 (s := ⟨zin, zin, zin⟩)
      (by simpa only [outerRun] using hrun)
    rw [hmix, weight_zero, mix]
    simpa using hcenter hcurv hrun
  | succ j ih =>
    obtain ⟨prev, hprev, hstep⟩ := previous_ok P g Q cfg zin hrun
    have hcurv' : 2 * M ≤ weight cfg.innerLast * scale cfg j := hcurv.trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (weight_antitone (Nat.le_succ j)) hc.le)
        (weight_pos cfg.innerLast).le)
    have hprev' := ih hcurv' hprev
    have hnew := hcenter hcurv hrun
    let α := weight (j + 1)
    have ha : 0 ≤ α := (weight_pos (j + 1)).le
    have h₁ : 0 ≤ 1 - α := sub_nonneg.mpr (weight_le_one (j + 1))
    rw [step_mix P g Q cfg (j + 1) hstep]
    calc
      _ ≤ (1 - α) * ‖prev.average - solution‖ + α * ‖s.functionCenter - solution‖ := by
        rw [mix_sub]
        simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg h₁] using
          norm_add_le ((1 - α) • (prev.average - solution)) (α • (s.functionCenter - solution))
      _ ≤ (1 - α) * (Real.sqrt 2 * ‖zin - solution‖) + α * (Real.sqrt 2 * ‖zin - solution‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hprev' h₁) (mul_le_mul_of_nonneg_left hnew ha)
      _ = _ := by ring

/-- A uniform bound on both thresholds, including the first 4A check. -/
def thresholdCap (cfg : Config) (A diameter : ℝ) : ℝ :=
  match cfg.check with
  | .exponential => max 4 (Real.exp (cfg.L₁ * diameter)) * A
  | .secant => 4 * A

/-- The secant mode uses the Lipschitz bound only to certify a uniform
cap on the requests for curvature; acceptance itself uses convexity. -/
structure ThresholdBounds (D : Set E) (g : E → E) (cfg : Config) (A diameter : ℝ) : Prop where
  nonneg : 0 ≤ A
  localScale {x : E} : x ∈ D → cfg.L₀ + cfg.L₁ * ‖g x‖ ≤ A
  exponential {x y : E} : cfg.check = .exponential → x ∈ D → y ∈ D →
    cfg.L₁ * ‖y - x‖ ≤ cfg.L₁ * diameter
  secant {x y : E} : cfg.check = .secant → x ∈ D → y ∈ D →
    ‖g y - g x‖ ≤ A * ‖y - x‖

private theorem thresholds_le {D : Set E} {g : E → E} {cfg : Config} {A diameter : ℝ}
    (h : ThresholdBounds D g cfg A diameter) {x y : E} (hx : x ∈ D) (hy : y ∈ D) :
    4 * (cfg.L₀ + cfg.L₁ * ‖g x‖) ≤ thresholdCap cfg A diameter ∧
      threshold g cfg x y (g x) ≤ thresholdCap cfg A diameter := by
  cases hm : cfg.check with
  | exponential =>
    simp only [threshold, thresholdCap, hm]
    constructor
    · exact (mul_le_mul_of_nonneg_left (h.localScale hx) (by norm_num)).trans
        (mul_le_mul_of_nonneg_right (le_max_left ..) h.nonneg)
    · calc
        _ ≤ A * Real.exp (cfg.L₁ * ‖y - x‖) :=
          mul_le_mul_of_nonneg_right (h.localScale hx) (Real.exp_pos _).le
        _ ≤ A * Real.exp (cfg.L₁ * diameter) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h.exponential hm hx hy)) h.nonneg
        _ ≤ _ := by
          rw [mul_comm A]
          exact mul_le_mul_of_nonneg_right (le_max_right ..) h.nonneg
  | secant =>
    simp only [threshold, thresholdCap, hm]
    refine ⟨mul_le_mul_of_nonneg_left (h.localScale hx) (by norm_num), ?_⟩
    by_cases hxy : y = x
    · simp [hxy, h.nonneg]
    · apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)))).mpr
      have hinner := real_inner_le_norm (g y - g x) (y - x)
      have hlip := mul_le_mul_of_nonneg_right (h.secant hm hx hy) (norm_nonneg (y - x))
      linarith only [hinner, hlip, mul_nonneg h.nonneg (sq_nonneg ‖y - x‖)]

def ValidOutcome (D : Set E) (Λ cap : ℝ) : Except ℝ (State E) → Prop
  | .ok s => Feasible D s
  | .error τ => Λ < τ ∧ τ ≤ cap

private theorem step_outcome {D : Set E} (P : Projection D) (g Q : E → E)
    (cfg : Config) {A diameter : ℝ} (hD : Convex ℝ D)
    (h : ThresholdBounds D g cfg A diameter) (j : ℕ) {s : State E} (hs : Feasible D s) :
    ValidOutcome D cfg.Λ (thresholdCap cfg A diameter) (outerStep P g Q cfg j s).result := by
  let α := weight j
  let x := mix α s.average s.functionCenter
  let m : Quadratic E := ⟨α * cfg.Λ, s.functionCenter, g x⟩
  let inner := innerRun P Q m (scale cfg j) s.operatorCenter (cfg.innerLast + 1)
  have hx := mix_mem hD (weight_pos j).le (weight_le_one j) hs.1 hs.2.1
  have hv := inner_feasible hD P Q m (scale cfg j) hs.2.2 (cfg.innerLast + 1)
  have hy := mix_mem hD (weight_pos j).le (weight_le_one j) hs.1 hv.1
  have hcap := thresholds_le h hx hy
  dsimp only [outerStep]
  split_ifs with hfirst hsecond
  · exact ⟨hfirst, hcap.1⟩
  · exact ⟨hsecond, hcap.2⟩
  · exact ⟨hy, hv⟩

theorem run_outcome {D : Set E} (P : Projection D) (g Q : E → E)
    (cfg : Config) {A diameter : ℝ} (hD : Convex ℝ D)
    (h : ThresholdBounds D g cfg A diameter) {zin : E} (hz : zin ∈ D) (j : ℕ) :
    ValidOutcome D cfg.Λ (thresholdCap cfg A diameter) (outerRun P g Q cfg zin j).result := by
  induction j with
  | zero => exact ⟨hz, hz, hz⟩
  | succ j ih =>
    cases hp : (outerRun P g Q cfg zin j).result with
    | error τ => simpa only [outerRun, hp] using ih
    | ok s =>
      have hs : Feasible D s := by simpa only [hp, ValidOutcome] using ih
      simpa only [outerRun, hp] using step_outcome P g Q cfg hD h j hs

end

end LeanLab.Sliding.TwoLevel
