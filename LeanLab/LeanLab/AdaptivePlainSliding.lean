module

public import LeanLab.PlainSliding

set_option linter.style.header false

/-!
# Variable curvature in unaccelerated sliding

Synchronizing the inner curvature with the outer curvature leaves fixed
weights in the potential. The accepted-trial proof keeps the nonnegative
model slack for the analysis of large-gradient steps.
-/

@[expose] public section

namespace LeanLab.Sliding.TwoLevel.Plain

open Set
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The coefficient of each squared distance is independent of the current model. -/
def potential (ρ : ℝ) (w : E) (s : State E) : ℝ :=
  ‖s.functionCenter - w‖ ^ 2 + ρ * ‖s.operatorCenter - w‖ ^ 2

/-- Form the next centers. Its average field stores the current trial point;
the final output is the weighted average of these fields. -/
def advance {D : Set E} (P : Projection D) (Q : E → E) (cfg : Config)
    (gx : E) (s : State E) : State E :=
  let inner := trial P Q cfg gx s
  ⟨inner.average, inner.average, inner.center⟩

omit [InnerProductSpace ℝ E] in
private theorem scaled_energy {cfg : Config} {ρ : ℝ} (hΛ : 0 < cfg.Λ)
    (hbalance : cfg.operatorCurvature = ρ * ((cfg.innerLast : ℝ) + 1) * cfg.Λ)
    (w : E) (s : State E) :
    2 / cfg.Λ * energy cfg w s = potential ρ w s := by
  have hT : 0 < (cfg.innerLast : ℝ) + 1 := by positivity
  unfold energy potential
  rw [hbalance]
  field_simp [hΛ.ne', hT.ne']

/-- With the stricter check, the trial gives both a weighted gap bound
and a separate decrease proportional to the squared movement. -/
theorem variable_curvature_step {D : Set E} (P : Projection D) {f : E → ℝ} {g Q : E → E}
    {cfg : Config} (hf : FunctionOracle D f g cfg) {M ρ : ℝ}
    (hQ : MonotoneLipschitz D Q M) (hΛ : 0 < cfg.Λ) (hH : 0 < cfg.operatorCurvature)
    (hcurv : 2 * M ≤ cfg.operatorCurvature)
    (hbalance : cfg.operatorCurvature = ρ * ((cfg.innerLast : ℝ) + 1) * cfg.Λ)
    {s : State E} (hs : Feasible D s)
    (hcheck : threshold g cfg s.functionCenter (advance P Q cfg (g s.functionCenter) s).average
      (g s.functionCenter) ≤ cfg.Λ / 2) :
    let next := advance P Q cfg (g s.functionCenter) s
    Feasible D next ∧ ∀ w ∈ D, 2 / cfg.Λ * gap f Q next.average w +
      ‖next.functionCenter - s.functionCenter‖ ^ 2 / 2 ≤
        potential ρ w s - potential ρ w next := by
  let next := advance P Q cfg (g s.functionCenter) s
  let τ := threshold g cfg s.functionCenter next.average (g s.functionCenter)
  have h := trial_bound P hf hQ hΛ hH hcurv hs
  refine ⟨⟨h.1, h.1, h.2.1⟩, ?_⟩
  intro w hw
  have hb := h.2.2 w hw
  change gap f Q next.average w + (cfg.Λ - τ) / 2 *
    ‖next.functionCenter - s.functionCenter‖ ^ 2 ≤ energy cfg w s - energy cfg w next at hb
  have hscaled := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 / cfg.Λ by positivity)
  rw [mul_add, mul_sub, scaled_energy hΛ hbalance, scaled_energy hΛ hbalance] at hscaled
  have hcoef : 1 / 2 ≤ (2 / cfg.Λ) * ((cfg.Λ - τ) / 2) := by
    have heq : 2 / cfg.Λ * ((cfg.Λ - τ) / 2) = (cfg.Λ - τ) / cfg.Λ := by ring
    rw [heq]
    apply (le_div_iff₀ hΛ).mpr
    change τ ≤ cfg.Λ / 2 at hcheck
    linarith only [hcheck]
  have hmove := mul_le_mul_of_nonneg_right hcoef
    (sq_nonneg ‖next.functionCenter - s.functionCenter‖)
  linarith only [hscaled, hmove]

/-- The integer budget gives the required operator curvature. It can be
chosen once at the starting curvature of a line search and kept fixed there. -/
def innerBudget (ρ M Λ : ℝ) : ℕ := max 1 ⌈2 * M / (ρ * Λ)⌉₊

theorem innerBudget_curvature {ρ M Λ₀ Λ : ℝ} (hρ : 0 < ρ) (h₀ : 0 < Λ₀)
    (hΛ : Λ₀ ≤ Λ) :
    2 * M ≤ ρ * (innerBudget ρ M Λ₀ : ℝ) * Λ := by
  have hceil : 2 * M / (ρ * Λ₀) ≤ (innerBudget ρ M Λ₀ : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right ..))
  have hb := (div_le_iff₀ (mul_pos hρ h₀)).mp hceil
  have hmul := mul_le_mul_of_nonneg_left hΛ
    (show 0 ≤ ρ * (innerBudget ρ M Λ₀ : ℝ) by positivity)
  linarith only [hb, hmul]

/-- The unnormalized weighted sum of gaps and of squared moves telescopes
for a finite sequence of accepted variable-curvature steps. -/
theorem variable_curvature_sum {f : E → ℝ} {Q : E → E}
    (s : ℕ → State E) (Λ : ℕ → ℝ) (ρ : ℝ) (w : E) (n : ℕ)
    (hstep : ∀ k < n, 2 / Λ k * gap f Q (s (k + 1)).average w +
      ‖(s (k + 1)).functionCenter - (s k).functionCenter‖ ^ 2 / 2 ≤
        potential ρ w (s k) - potential ρ w (s (k + 1))) :
    (∑ k ∈ Finset.range n, 2 / Λ k * gap f Q (s (k + 1)).average w) +
      (∑ k ∈ Finset.range n, ‖(s (k + 1)).functionCenter - (s k).functionCenter‖ ^ 2 / 2) ≤
      potential ρ w (s 0) - potential ρ w (s n) := by
  have hb := Finset.sum_le_sum fun k hk => hstep k (Finset.mem_range.mp hk)
  rw [Finset.sum_add_distrib, Finset.sum_range_sub'] at hb
  exact hb

private theorem exp_quarter_le_two : Real.exp (1 / 4) ≤ 2 := by
  exact (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)).trans (by norm_num)

/-- A short trial passes the stricter exponential check at four times
the local scale. This check uses the cached starting gradient only. -/
theorem short_trial_check {g : E → E} {cfg : Config} {u v : E}
    (hm : cfg.check = .exponential)
    (hA : 0 ≤ cfg.L₀ + cfg.L₁ * ‖g u‖)
    (hdist : cfg.L₁ * ‖v - u‖ ≤ 1 / 4)
    (hΛ : 4 * (cfg.L₀ + cfg.L₁ * ‖g u‖) ≤ cfg.Λ) :
    threshold g cfg u v (g u) ≤ cfg.Λ / 2 := by
  simp only [threshold, hm]
  have hexp := (Real.exp_le_exp.mpr hdist).trans exp_quarter_le_two
  have hmul := mul_le_mul_of_nonneg_left hexp hA
  linarith only [hΛ, hmul]

/-- At a Minty solution the gap dominates the value difference of the
convex function after shifting its gradient by its value at the solution. -/
theorem centered_gap {f : E → ℝ} {Q : E → E} {a z v : E}
    (hVI : 0 ≤ ⟪a + Q z, v - z⟫) :
    (f v - ⟪a, v⟫) - (f z - ⟪a, z⟫) ≤ gap f Q v z := by
  simp only [gap, inner_add_left, inner_sub_right] at hVI ⊢
  linarith only [hVI]

/-- A quadratic-exponential model gives a lower bound on the objective
gap from one hypothetical gradient step. This step is only in the proof. -/
theorem gradient_gap_lower {f : E → ℝ} {u z g : E} {A L₁ : ℝ}
    (hA : 0 < A) (hscale : L₁ * ‖g‖ ≤ A)
    (hmin : ∀ y, f z ≤ f y)
    (hmodel : ∀ y, f y ≤ f u + ⟪g, y - u⟫ +
      A * Real.exp (L₁ * ‖y - u‖) / 2 * ‖y - u‖ ^ 2) :
    ‖g‖ ^ 2 / (8 * A) ≤ f u - f z := by
  let t : ℝ := 1 / (4 * A)
  let y := u - t • g
  have ht : 0 < t := by dsimp [t]; positivity
  have hdist : y - u = -(t • g) := by dsimp [y]; abel
  have hnorm : ‖y - u‖ = t * ‖g‖ := by
    rw [hdist, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have htA : t * A = 1 / 4 := by dsimp [t]; field_simp
  have hlin := mul_le_mul_of_nonneg_left hscale ht.le
  have harg : L₁ * ‖y - u‖ ≤ 1 / 4 := by
    rw [hnorm]
    nlinarith only [htA, hlin]
  have hexp := (Real.exp_le_exp.mpr harg).trans exp_quarter_le_two
  have hquad := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexp (show 0 ≤ A / 2 by positivity))
    (sq_nonneg ‖y - u‖)
  have h := hmodel y
  have hf := hmin y
  rw [hdist, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at h
  rw [hnorm] at hquad
  have hq : A * Real.exp (L₁ * ‖y - u‖) / 2 * ‖y - u‖ ^ 2 ≤
      t / 4 * ‖g‖ ^ 2 := by
    have heq : (A / 2 * 2) * (t * ‖g‖) ^ 2 = t / 4 * ‖g‖ ^ 2 := by
      calc
        _ = (t * A) * t * ‖g‖ ^ 2 := by ring
        _ = _ := by rw [htA]; ring
    rw [heq] at hquad
    rw [hnorm]
    linarith only [hquad]
  have heq : ‖g‖ ^ 2 / (8 * A) = t / 2 * ‖g‖ ^ 2 := by
    dsimp [t]
    field_simp; ring
  rw [heq]
  rw [hdist] at hq
  nlinarith only [h, hf, hq, mul_nonneg ht.le (sq_nonneg ‖g‖)]

/-- For a large centered gradient, either movement or the transferred
gap yields a fixed amount of progress. The upper bound on Λ is needed
only at short trials. -/
theorem large_gradient_progress {f : E → ℝ} {Q : E → E}
    {z u v a : E} {Λ A L₁ C Pprev Pnext : ℝ}
    (hΛ : 0 < Λ) (hA : 0 < A) (hL₁ : 0 < L₁) (hC : 0 < C)
    (hsize : 0 < ‖a‖) (hscale : A ≤ 2 * L₁ * ‖a‖)
    (hgap : ‖a‖ ^ 2 / (8 * A) ≤ f u - f z)
    (hsupport : f u + ⟪a, v - u⟫ ≤ f v)
    (hsolution : 0 ≤ gap f Q v z) (htransfer : f v - f z ≤ gap f Q v z)
    (hstep : 2 / Λ * gap f Q v z + ‖v - u‖ ^ 2 / 2 ≤ Pprev - Pnext)
    (hshort : ‖v - u‖ < 1 / (32 * L₁) → Λ ≤ C * L₁ * ‖a‖) :
    min ((1 / (32 * L₁)) ^ 2 / 2) (1 / (16 * C * L₁ ^ 2)) ≤ Pprev - Pnext := by
  by_cases hm : ‖v - u‖ < 1 / (32 * L₁)
  · have hlow : ‖a‖ / (16 * L₁) ≤ f u - f z := by
      apply le_trans _ hgap
      apply (div_le_div_iff₀ (by positivity : 0 < 16 * L₁) (by positivity : 0 < 8 * A)).mpr
      have h := mul_le_mul_of_nonneg_right hscale (norm_nonneg a)
      nlinarith only [h]
    have hmove := mul_le_mul_of_nonneg_left hm.le (norm_nonneg a)
    have hinner : -(‖a‖ * ‖v - u‖) ≤ ⟪a, v - u⟫ := by
      exact (abs_le.mp (abs_real_inner_le_norm a (v - u))).1
    have htrial : ‖a‖ / (32 * L₁) ≤ gap f Q v z := by
      have he : ‖a‖ / (16 * L₁) = 2 * (‖a‖ / (32 * L₁)) := by field_simp; ring
      rw [he] at hlow
      have hz : ‖a‖ * (1 / (32 * L₁)) = ‖a‖ / (32 * L₁) := by ring
      rw [hz] at hmove
      linarith only [hlow, hmove, hinner, hsupport, htransfer]
    have hdecrease : 1 / (16 * C * L₁ ^ 2) ≤ 2 / Λ * gap f Q v z := by
      calc
        _ ≤ (2 / Λ) * (‖a‖ / (32 * L₁)) := by
          rw [div_mul_div_comm]
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          have h := mul_le_mul_of_nonneg_right (hshort hm) hL₁.le
          nlinarith only [h]
        _ ≤ _ := mul_le_mul_of_nonneg_left htrial (by positivity)
    exact (min_le_right ..).trans (by linarith only [hdecrease, hstep, sq_nonneg ‖v - u‖])
  · have hsq := pow_le_pow_left₀ (show 0 ≤ 1 / (32 * L₁) by positivity) (le_of_not_gt hm) 2
    have hgap' : 0 ≤ 2 / Λ * gap f Q v z := by positivity
    exact (min_le_left ..).trans (by linarith only [hstep, hsq, hgap'])

theorem centered_gap_eq {f : E → ℝ} {Q : E → E} (a v w : E) :
    gap (fun z => f z - ⟪a, z⟫) (fun z => Q z + a) v w = gap f Q v w := by
  simp only [gap, inner_add_left, inner_sub_right]
  ring

private theorem gap_convex {D : Set E} {f : E → ℝ} {Q : E → E}
    (hf : ConvexOn ℝ D f) (w : E) : ConvexOn ℝ D (fun z => gap f Q z w) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hp := hf.2 hx hy ha hb hab
  change f (a • x + b • y) ≤ a * f x + b * f y at hp
  change gap f Q (a • x + b • y) w ≤ a * gap f Q x w + b * gap f Q y w
  simp only [gap, inner_sub_right, inner_add_right, real_inner_smul_right]
  linear_combination hp + (f w + ⟪Q w, w⟫) * hab

/-- The weighted mean has a gap bounded by the initial fixed potential divided
by the total inverse curvature. -/
theorem weighted_gap {D : Set E} {f : E → ℝ} {Q : E → E}
    (hf : ConvexOn ℝ D f) (s : ℕ → State E) (Λ : ℕ → ℝ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (w : E) {n : ℕ} (hn : 0 < n) (hΛ : ∀ k < n, 0 < Λ k)
    (hmem : ∀ k < n, (s (k + 1)).average ∈ D)
    (hstep : ∀ k < n, 2 / Λ k * gap f Q (s (k + 1)).average w +
      ‖(s (k + 1)).functionCenter - (s k).functionCenter‖ ^ 2 / 2 ≤
        potential ρ w (s k) - potential ρ w (s (k + 1))) :
    let t := Finset.range n
    let weight := fun k => 2 / Λ k
    let out := t.centerMass weight (fun k => (s (k + 1)).average)
    out ∈ D ∧ gap f Q out w ≤ potential ρ w (s 0) / ∑ k ∈ t, weight k := by
  let t := Finset.range n
  let weight := fun k => 2 / Λ k
  have hp : ∀ k ∈ t, 0 < weight k := fun k hk =>
    div_pos (by norm_num) (hΛ k (Finset.mem_range.mp hk))
  have ht : t.Nonempty := ⟨0, Finset.mem_range.mpr hn⟩
  have hs := Finset.sum_pos hp ht
  have hfeas : ∀ k ∈ t, (s (k + 1)).average ∈ D := fun k hk => hmem k (Finset.mem_range.mp hk)
  refine ⟨hf.1.centerMass_mem (fun k hk => (hp k hk).le) hs hfeas, ?_⟩
  have hj := (gap_convex (Q := Q) hf w).map_centerMass_le (fun k hk => (hp k hk).le) hs hfeas
  have hsum := variable_curvature_sum s Λ ρ w n hstep
  have hlast : 0 ≤ potential ρ w (s n) := by unfold potential; positivity
  have hmovement : 0 ≤ ∑ k ∈ t, ‖(s (k + 1)).functionCenter - (s k).functionCenter‖ ^ 2 / 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hbound : (∑ k ∈ t, weight k * gap f Q (s (k + 1)).average w) ≤ potential ρ w (s 0) := by
    change (∑ k ∈ Finset.range n, 2 / Λ k * gap f Q (s (k + 1)).average w) ≤ _
    change 0 ≤ ∑ k ∈ Finset.range n,
      ‖(s (k + 1)).functionCenter - (s k).functionCenter‖ ^ 2 / 2 at hmovement
    linarith only [hsum, hlast, hmovement]
  refine hj.trans ?_
  rw [Finset.centerMass]
  simp only [smul_eq_mul]
  rw [← div_eq_inv_mul]
  exact div_le_div_of_nonneg_right hbound hs.le

/-- An additive decrease on selected steps bounds how many such steps
can occur before the nonnegative potential is exhausted. -/
theorem count_progress_steps {P : ℕ → ℝ} (bad : ℕ → Prop) [DecidablePred bad]
    {c : ℝ} (n : ℕ) (hfinal : 0 ≤ P n)
    (hstep : ∀ k < n, P (k + 1) ≤ P k)
    (hbad : ∀ k < n, bad k → c ≤ P k - P (k + 1)) :
    ((Finset.range n).filter bad).card * c ≤ P 0 := by
  have hsum : (∑ k ∈ Finset.range n, if bad k then c else 0) ≤
      ∑ k ∈ Finset.range n, (P k - P (k + 1)) := by
    apply Finset.sum_le_sum
    intro k hk
    split_ifs with hb
    · exact hbad k (Finset.mem_range.mp hk) hb
    · exact sub_nonneg.mpr (hstep k (Finset.mem_range.mp hk))
  rw [Finset.sum_range_sub', ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hsum
  linarith only [hsum, hfinal]

private theorem projection_nonexpansive {D : Set E} (P : Projection D) (x y : E) :
    ‖P.apply x - P.apply y‖ ≤ ‖x - y‖ := by
  let d := P.apply x - P.apply y
  have hx := P.normal x (P.feasible y)
  have hy := P.normal y (P.feasible x)
  have hrev : P.apply y - P.apply x = -d := by dsimp [d]; abel
  rw [hrev, inner_neg_right] at hx
  change ⟪y - P.apply y, d⟫ ≤ 0 at hy
  have he : x - y = (x - P.apply x) + d - (y - P.apply y) := by dsimp [d]; abel
  have hlo : ‖d‖ ^ 2 ≤ ⟪x - y, d⟫ := by
    rw [he, inner_sub_left, inner_add_left, real_inner_self_eq_norm_sq]
    linarith only [hx, hy]
  have hh := hlo.trans (real_inner_le_norm (x - y) d)
  change ‖d‖ ≤ ‖x - y‖
  by_cases h : 0 < ‖d‖
  · apply le_of_mul_le_mul_right _ h
    simpa only [sq] using hh
  · linarith [norm_nonneg (x - y), norm_nonneg d]

private theorem projection_fixes {D : Set E} (P : Projection D) {x : E} (hx : x ∈ D) :
    P.apply x = x := by
  have h := projection_bound (P.normal x hx)
  rw [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
  have he : ‖P.apply x - x‖ = 0 := by nlinarith [sq_nonneg ‖x - P.apply x‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

/-- One inner trial in reciprocal curvature coordinates. b is the
ratio of the inner to the outer curvature, kept fixed across the search. -/
def reciprocalStep {D : Set E} (P : Projection D) (Q : E → E) (u gx : E)
    (b θ : ℝ) (q : E) : InnerState E :=
  let v := P.apply (mix (b / (1 + b)) u q - (θ / (1 + b)) • (gx + Q q))
  ⟨v, P.apply (v + (θ / b) • (Q q - Q v))⟩

def reciprocalPass {D : Set E} (P : Projection D) (Q : E → E) (u gx q : E)
    (b θ : ℝ) : ℕ → InnerState E
  | 0 => ⟨q, q⟩
  | n + 1 =>
    let prev := reciprocalPass P Q u gx q b θ n
    let next := reciprocalStep P Q u gx b θ prev.center
    ⟨meanStep n prev.average next.average, next.center⟩

private theorem reciprocal_step_eq {D : Set E} (P : Projection D) (Q : E → E)
    (u gx q : E) {b θ : ℝ} (hb : 0 < b) (hθ : 0 < θ) :
    reciprocalStep P Q u gx b θ q =
      operatorStep P Q ⟨θ⁻¹, u, gx⟩ (b * θ⁻¹) q := by
  have hb' : 1 + b ≠ 0 := by positivity
  have hi : (θ⁻¹ + b * θ⁻¹)⁻¹ = θ / (1 + b) := by
    rw [show θ⁻¹ + b * θ⁻¹ = (1 + b) * θ⁻¹ by ring]
    field_simp [hb', hθ.ne']
  have h₁ : θ / (1 + b) * θ⁻¹ = 1 - b / (1 + b) := by
    field_simp [hb', hθ.ne']; ring
  have h₂ : θ / (1 + b) * (b * θ⁻¹) = b / (1 + b) := by
    field_simp [hb', hθ.ne']
  have h₃ : (b * θ⁻¹)⁻¹ = θ / b := by field_simp [hb.ne', hθ.ne']
  have he : (θ⁻¹ + b * θ⁻¹)⁻¹ • (θ⁻¹ • u + (b * θ⁻¹) • q - (gx + Q q)) =
      mix (b / (1 + b)) u q - (θ / (1 + b)) • (gx + Q q) := by
    rw [hi, smul_sub, smul_add, smul_smul, smul_smul, h₁, h₂]
    rfl
  simp only [reciprocalStep, operatorStep, leaf, he, h₃]

theorem reciprocal_pass_eq {D : Set E} (P : Projection D) (Q : E → E)
    (u gx q : E) {b θ : ℝ} (hb : 0 < b) (hθ : 0 < θ) (n : ℕ) :
    reciprocalPass P Q u gx q b θ n =
      innerPass P Q ⟨θ⁻¹, u, gx⟩ (b * θ⁻¹) q n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [reciprocalPass, innerPass, ih, reciprocal_step_eq P Q u gx _ hb hθ]

theorem reciprocal_pass_continuous {D : Set E} (P : Projection D) {Q : E → E}
    (hQ : Continuous Q) (u gx q : E) (b : ℝ) (n : ℕ) :
    Continuous (fun θ => (reciprocalPass P Q u gx q b θ n).average) ∧
      Continuous (fun θ => (reciprocalPass P Q u gx q b θ n).center) := by
  have hP : Continuous P.apply := (show LipschitzWith 1 P.apply from
    LipschitzWith.of_dist_le_mul fun x y => by
      simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
        projection_nonexpansive P x y).continuous
  induction n with
  | zero => exact ⟨continuous_const, continuous_const⟩
  | succ n ih =>
    obtain ⟨ha, hc⟩ := ih
    let prev := fun θ => reciprocalPass P Q u gx q b θ n
    let v := fun θ => P.apply (mix (b / (1 + b)) u (prev θ).center -
      (θ / (1 + b)) • (gx + Q (prev θ).center))
    have hv : Continuous v := by
      dsimp [v, mix]
      exact hP.comp (by fun_prop)
    change Continuous (fun θ => meanStep n (prev θ).average (v θ)) ∧
      Continuous (fun θ => P.apply (v θ + (θ / b) • (Q (prev θ).center - Q (v θ))))
    constructor
    · unfold meanStep mix
      fun_prop
    · exact hP.comp (by fun_prop)

private theorem reciprocal_zero_step {D : Set E} (hD : Convex ℝ D)
    (P : Projection D) (Q : E → E) {u q : E} (gx : E) (hu : u ∈ D)
    (hq : q ∈ D) {b : ℝ} (hb : 0 < b) :
    let s := reciprocalStep P Q u gx b 0 q
    s.average ∈ D ∧ s.center = s.average ∧
      ‖s.average - u‖ = b / (1 + b) * ‖q - u‖ := by
  let α := b / (1 + b)
  have ha : 0 ≤ α := by dsimp [α]; positivity
  have ha' : α ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hm := mix_mem hD ha ha' hu hq
  have hd : mix α u q - u = α • (q - u) := by unfold mix; module
  simp only [reciprocalStep, zero_div, zero_smul, sub_zero, add_zero]
  rw [projection_fixes P hm, projection_fixes P hm, hd, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ha]
  exact ⟨hm, rfl, rfl⟩

/-- The limiting trial as curvature tends to infinity keeps a contribution
from the previous operator center. With b = ρ * n its size is at most
ρ times the initial distance between the centers. -/
theorem reciprocal_zero_bound {D : Set E} (hD : Convex ℝ D) (P : Projection D)
    (Q : E → E) {u q : E} (gx : E) (hu : u ∈ D) (hq : q ∈ D)
    {b : ℝ} (hb : 0 < b) (n : ℕ) :
    let s := reciprocalPass P Q u gx q b 0 n
    s.center ∈ D ∧ (n : ℝ) * ‖s.average - u‖ ≤ b * (‖q - u‖ - ‖s.center - u‖) := by
  induction n with
  | zero => exact ⟨hq, by simp [reciprocalPass]⟩
  | succ n ih =>
    let prev := reciprocalPass P Q u gx q b 0 n
    let next := reciprocalStep P Q u gx b 0 prev.center
    obtain ⟨hf, hc, hd⟩ := reciprocal_zero_step hD P Q gx hu ih.1 hb
    change next.average ∈ D at hf
    change next.center = next.average at hc
    change ‖next.average - u‖ = b / (1 + b) * ‖prev.center - u‖ at hd
    have hs : ‖next.average - u‖ ≤ b * (‖prev.center - u‖ - ‖next.center - u‖) := by
      rw [hc]
      have he := (eq_div_iff (show 1 + b ≠ 0 by positivity)).mp
        (by rw [hd]; ring :
          ‖next.average - u‖ = (b * ‖prev.center - u‖) / (1 + b))
      nlinarith only [he]
    have hm : ((n + 1 : ℕ) : ℝ) * ‖meanStep n prev.average next.average - u‖ ≤
        (n : ℝ) * ‖prev.average - u‖ + ‖next.average - u‖ := by
      apply mean_bound (fun x => ‖x - u‖) n prev.average next.average
      let α := ((n : ℝ) + 1)⁻¹
      have he : meanStep n prev.average next.average - u =
          (1 - α) • (prev.average - u) + α • (next.average - u) := by
        unfold meanStep mix
        change (1 - α) • prev.average + α • next.average - u = _
        module
      rw [he]
      change _ ≤ (1 - α) * ‖prev.average - u‖ + α * ‖next.average - u‖
      have hα : 0 ≤ α := (mean_weight n).1
      have h₁ : 0 ≤ 1 - α := sub_nonneg.mpr (mean_weight n).2
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg h₁, abs_of_nonneg hα] using
        norm_add_le ((1 - α) • (prev.average - u)) (α • (next.average - u))
    change next.center ∈ D ∧ ((n + 1 : ℕ) : ℝ) * ‖meanStep n prev.average next.average - u‖ ≤
      b * (‖q - u‖ - ‖next.center - u‖)
    exact ⟨hc ▸ hf, by linarith only [ih.2, hm, hs]⟩

/-- A fixed inner budget provides a continuous line search. If the
initial trial is too long, a different curvature yields exactly δ, so
the strict model check can be satisfied without accepting a tiny move. -/
theorem reciprocal_trial_choice {D : Set E} (hD : Convex ℝ D) (P : Projection D)
    {Q : E → E} (hQ : Continuous Q) {u q : E} (gx : E) (hu : u ∈ D) (hq : q ∈ D)
    {ρ θ₀ δ : ℝ} (hρ : 0 < ρ) (hθ : 0 < θ₀) {n : ℕ} (hn : 0 < n)
    (hclose : ρ * ‖q - u‖ < δ) :
    let d := fun θ => ‖(reciprocalPass P Q u gx q (ρ * (n : ℝ)) θ n).average - u‖
    ∃ θ, 0 < θ ∧ θ ≤ θ₀ ∧ d θ ≤ δ ∧ (θ = θ₀ ∨ d θ = δ) := by
  let b := ρ * (n : ℝ)
  let d := fun θ => ‖(reciprocalPass P Q u gx q b θ n).average - u‖
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hb : 0 < b := mul_pos hρ hn'
  obtain ⟨_, hz⟩ := reciprocal_zero_bound hD P Q gx hu hq hb n
  have hz' : d 0 ≤ ρ * ‖q - u‖ := by
    apply le_of_mul_le_mul_left _ hn'
    rw [← mul_assoc, mul_comm (n : ℝ) ρ]
    exact hz.trans (mul_le_mul_of_nonneg_left (sub_le_self _ (norm_nonneg _)) hb.le)
  by_cases h : d θ₀ ≤ δ
  · exact ⟨θ₀, hθ, le_rfl, h, Or.inl rfl⟩
  have hc : Continuous d := by
    dsimp [d]
    have hh := (reciprocal_pass_continuous P hQ u gx q b n).1
    fun_prop
  have hi := intermediate_value_Icc hθ.le hc.continuousOn
    (show δ ∈ Icc (d 0) (d θ₀) from ⟨(hz'.trans_lt hclose).le, (le_of_not_ge h)⟩)
  obtain ⟨θ, hθmem, heq⟩ := hi
  have hθpos : 0 < θ := by
    refine lt_of_le_of_ne hθmem.1 ?_
    rintro rfl
    exact (not_lt_of_ge heq.ge) (hz'.trans_lt hclose)
  exact ⟨θ, hθpos, hθmem.2, heq.le, Or.inr heq⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem innerBudget_le {ρ M Λ₀ : ℝ} (hρ : 0 < ρ) (hΛ₀ : 0 < Λ₀) (hM : 0 ≤ M) :
    (innerBudget ρ M Λ₀ : ℝ) ≤ 1 + 2 * M / (ρ * Λ₀) := by
  have ha : 0 ≤ 2 * M / (ρ * Λ₀) := by positivity
  rw [innerBudget, Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) ((Nat.ceil_lt_add_one ha).le.trans_eq (add_comm ..))

/-- Keep the inner budget selected at the initial curvature. A search
probe only changes the two proportionally coupled model curvatures. -/
def matchedConfig (base : Config) (ρ M Λ : ℝ) : Config :=
  let n := innerBudget ρ M base.Λ
  { base with Λ := Λ, operatorCurvature := ρ * (n : ℝ) * Λ, innerLast := n - 1 }

/-- The exponential check admits either the initial curvature or a trial
of the prescribed positive length. This is an existence certificate for
the line search, with a fixed inner budget and one cached gradient. -/
theorem exists_accepted_trial {D : Set E} (hD : Convex ℝ D) (P : Projection D)
    {g Q : E → E} (hQ : Continuous Q) (base : Config) (hm : base.check = .exponential)
    {s : State E} (hs : Feasible D s) {ρ M δ : ℝ} (hρ : 0 < ρ) (h₀ : 0 < base.Λ)
    (hL₁ : 0 ≤ base.L₁) (hA : 0 ≤ base.L₀ + base.L₁ * ‖g s.functionCenter‖)
    (hinit : 4 * (base.L₀ + base.L₁ * ‖g s.functionCenter‖) ≤ base.Λ)
    (hδ : base.L₁ * δ ≤ 1 / 4)
    (hclose : ρ * ‖s.operatorCenter - s.functionCenter‖ < δ) :
    ∃ Λ, base.Λ ≤ Λ ∧
      let cfg := matchedConfig base ρ M Λ
      let next := advance P Q cfg (g s.functionCenter) s
      2 * M ≤ cfg.operatorCurvature ∧
        cfg.operatorCurvature = ρ * ((cfg.innerLast : ℝ) + 1) * cfg.Λ ∧
        threshold g cfg s.functionCenter next.average (g s.functionCenter) ≤ cfg.Λ / 2 ∧
        ‖next.functionCenter - s.functionCenter‖ ≤ δ ∧
        (Λ = base.Λ ∨ ‖next.functionCenter - s.functionCenter‖ = δ) := by
  let n := innerBudget ρ M base.Λ
  have hn : 0 < n := lt_of_lt_of_le (by decide) (le_max_left ..)
  have hcount : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hn)
  have hcount' : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
    exact_mod_cast hcount
  obtain ⟨θ, hθ, hθ₀, hdist, halt⟩ :=
    reciprocal_trial_choice hD P hQ (g s.functionCenter) hs.2.1 hs.2.2 hρ
      (inv_pos.mpr h₀) hn hclose
  let cfg := matchedConfig base ρ M θ⁻¹
  let next := advance P Q cfg (g s.functionCenter) s
  have hΛ : base.Λ ≤ θ⁻¹ := by simpa only [inv_inv] using inv_anti₀ hθ hθ₀
  have heq : next.functionCenter =
      (reciprocalPass P Q s.functionCenter (g s.functionCenter) s.operatorCenter
        (ρ * (n : ℝ)) θ n).average := by
    dsimp only [next, advance, trial]
    change (innerPass P Q ⟨θ⁻¹, s.functionCenter, g s.functionCenter⟩
      (ρ * (n : ℝ) * θ⁻¹) s.operatorCenter (n - 1 + 1)).average = _
    rw [hcount, reciprocal_pass_eq P Q _ _ _ (mul_pos hρ (Nat.cast_pos.mpr hn)) hθ]
  have hv : ‖next.functionCenter - s.functionCenter‖ ≤ δ := by simpa only [heq] using hdist
  have hv' : ‖next.average - s.functionCenter‖ ≤ δ := hv
  have hbal : cfg.operatorCurvature = ρ * ((cfg.innerLast : ℝ) + 1) * cfg.Λ := by
    change ρ * (n : ℝ) * θ⁻¹ = ρ * (((n - 1 : ℕ) : ℝ) + 1) * θ⁻¹
    rw [hcount']
  refine ⟨θ⁻¹, hΛ, innerBudget_curvature hρ h₀ hΛ, hbal, ?_, hv, ?_⟩
  · exact short_trial_check (cfg := cfg) hm hA
      ((mul_le_mul_of_nonneg_left hv' hL₁).trans hδ) (hinit.trans hΛ)
  · rcases halt with hθeq | hdeq
    · exact Or.inl (by rw [hθeq, inv_inv])
    · apply Or.inr
      change ‖next.functionCenter - s.functionCenter‖ = δ
      rw [heq]
      exact hdeq

/-- Each bisection iteration evaluates the trial distance at one point.
On success the returned distance lies in [δ/2, δ]. -/
def bisectDistance (d : ℝ → ℝ) (δ : ℝ) : ℕ → ℝ → ℝ → Option ℝ
  | 0, _, _ => none
  | n + 1, a, b =>
    let m := (a + b) / 2
    let dm := d m
    if dm < δ / 2 then bisectDistance d δ n m b
    else if δ < dm then bisectDistance d δ n a m
    else some m

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A Lipschitz modulus on the bracket gives an explicit probe bound.
Monotonicity of the trial distance is unnecessary. -/
theorem bisectDistance_success (d : ℝ → ℝ) {a b δ L : ℝ} (hδ : 0 < δ) (hab : a ≤ b)
    (hlo : d a < δ / 2) (hhi : δ < d b)
    (hLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖d y - d x‖ ≤ L * ‖y - x‖)
    (n : ℕ) (hbudget : L * (b - a) / (2 : ℝ) ^ n ≤ δ / 2) :
    ∃ θ ∈ Icc a b, bisectDistance d δ n a b = some θ ∧ d θ ∈ Icc (δ / 2) δ := by
  induction n generalizing a b with
  | zero =>
    have h := hLip a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩
    have hh : 0 ≤ d b - d a := by linarith only [hlo, hhi, hδ]
    rw [Real.norm_eq_abs, abs_of_nonneg hh, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hab)] at h
    simp only [pow_zero, div_one] at hbudget
    exfalso
    linarith only [h, hbudget, hlo, hhi]
  | succ n ih =>
    let m := (a + b) / 2
    have ham : a ≤ m := by dsimp [m]; linarith
    have hmb : m ≤ b := by dsimp [m]; linarith
    have hl : L * (m - a) / (2 : ℝ) ^ n =
        L * (b - a) / (2 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      dsimp [m]
      field_simp; ring
    have hr : L * (b - m) / (2 : ℝ) ^ n =
        L * (b - a) / (2 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      dsimp [m]
      field_simp; ring
    dsimp only [bisectDistance]
    split_ifs with hleft hright
    · obtain ⟨θ, hθ, ht, hd⟩ := ih hmb hleft hhi
        (fun x hx y hy => hLip x ⟨ham.trans hx.1, hx.2⟩ y ⟨ham.trans hy.1, hy.2⟩)
        (by rw [hr]; exact hbudget)
      exact ⟨θ, ⟨ham.trans hθ.1, hθ.2⟩, ht, hd⟩
    · obtain ⟨θ, hθ, ht, hd⟩ := ih ham hlo hright
        (fun x hx y hy => hLip x ⟨hx.1, hx.2.trans hmb⟩ y ⟨hy.1, hy.2.trans hmb⟩)
        (by rw [hl]; exact hbudget)
      exact ⟨θ, ⟨hθ.1, hθ.2.trans hmb⟩, ht, hd⟩
    · exact ⟨m, ⟨ham, hmb⟩, rfl, ⟨le_of_not_gt hleft, le_of_not_gt hright⟩⟩

end

end LeanLab.Sliding.TwoLevel.Plain
