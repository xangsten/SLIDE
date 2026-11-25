module

public import LeanLab.AdaptiveAcceleratedSliding

set_option linter.style.header false

/-!
# Step length in nonaccelerated sliding

Starting the operator loop at the current function center permits a
relative comparison with the exact resolvent. Resetting both centers
to their midpoint preserves the decrease of the squared distance.
-/

@[expose] public section

namespace LeanLab.Sliding.TwoLevel.Plain

open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- A bound on the gap of the strongly monotone subproblem bounds the
computed movement relative to the movement of its exact solution. -/
theorem relative_trial_move {u v q z : E}
    (h : ‖v - z‖ ^ 2 + ‖q - z‖ ^ 2 / 2 ≤ ‖u - z‖ ^ 2 / 2) :
    ‖u - z‖ / 4 ≤ ‖v - u‖ ∧ ‖v - u‖ ≤ 2 * ‖u - z‖ ∧
      ‖q - u‖ ≤ 2 * ‖u - z‖ := by
  have hv : ‖v - z‖ ≤ 3 * ‖u - z‖ / 4 := by
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith only [h, sq_nonneg ‖q - z‖, sq_nonneg ‖u - z‖]
  have hq : ‖q - z‖ ≤ ‖u - z‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    nlinarith only [h, sq_nonneg ‖v - z‖]
  have htriangle (x y t : E) : ‖x - t‖ ≤ ‖x - y‖ + ‖y - t‖ := by
    have heq : x - t = (x - y) + (y - t) := by abel
    rw [heq]
    exact norm_add_le _ _
  have hlower := htriangle u v z
  rw [norm_sub_rev u v] at hlower
  refine ⟨?_, ?_, ?_⟩
  · linarith only [hlower, hv]
  · linarith only [htriangle v z u, hv, norm_sub_rev z u, norm_nonneg (u - z)]
  · linarith only [htriangle q z u, hq, norm_sub_rev z u]

/-- Monotonicity of the two resolvent values gives both bounds on the
movement after reducing the proximal step from `b` to `a`. -/
theorem resolvent_move {u x y : E} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hmono : 0 ≤ ⟪(1 / a) • (u - x) - (1 / b) • (u - y), x - y⟫) :
    ‖x - u‖ ≤ ‖y - u‖ ∧ a * ‖y - u‖ ≤ b * ‖x - u‖ := by
  have hb := ha.trans_le hab
  have hx : u - x = -(x - u) := by abel
  have hy : u - y = -(y - u) := by abel
  have hxy : x - y = (x - u) - (y - u) := by abel
  have h := mul_le_mul_of_nonneg_left hmono (show 0 ≤ a * b by positivity)
  rw [hxy, hx, hy] at h
  let X := x - u
  let Y := y - u
  rw [mul_zero] at h
  change 0 ≤ a * b * ⟪(1 / a) • -X - (1 / b) • -Y, X - Y⟫ at h
  simp only [inner_sub_left, real_inner_smul_left, inner_neg_left, inner_sub_right,
    real_inner_self_eq_norm_sq] at h
  rw [show ⟪Y, X⟫ = ⟪X, Y⟫ from real_inner_comm _ _] at h
  have hquad : b * ‖x - u‖ ^ 2 + a * ‖y - u‖ ^ 2 ≤ (a + b) * ⟪x - u, y - u⟫ := by
    change b * ‖X‖ ^ 2 + a * ‖Y‖ ^ 2 ≤ (a + b) * ⟪X, Y⟫
    field_simp [ha.ne', hb.ne'] at h
    linarith only [h]
  have hprod := hquad.trans (mul_le_mul_of_nonneg_left
    (real_inner_le_norm (x - u) (y - u)) (by positivity : 0 ≤ a + b))
  have hfactor : 0 ≤ (‖y - u‖ - ‖x - u‖) * (b * ‖x - u‖ - a * ‖y - u‖) := by
    linarith only [hprod]
  have hord : ‖x - u‖ ≤ ‖y - u‖ := by
    by_contra! hbad
    have ht : 0 < b * ‖x - u‖ - a * ‖y - u‖ := by
      have h₁ := mul_lt_mul_of_pos_left hbad ha
      have h₂ := mul_le_mul_of_nonneg_right hab (norm_nonneg (x - u))
      linarith
    exact (not_lt_of_ge hfactor) (mul_neg_of_neg_of_pos (sub_neg.mpr hbad) ht)
  refine ⟨hord, ?_⟩
  rcases eq_or_lt_of_le hord with heq | hlt
  · rw [heq]
    exact mul_le_mul_of_nonneg_right hab (norm_nonneg _)
  · exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hfactor (sub_pos.mpr hlt))

/-- Resetting two centers to their midpoint preserves the decrease of
their squared-distance potential. -/
theorem midpoint_energy (v q w : E) :
    ‖(1 / 2 : ℝ) • (v + q) - w‖ ^ 2 ≤ (‖v - w‖ ^ 2 + ‖q - w‖ ^ 2) / 2 := by
  have heq : (1 / 2 : ℝ) • (v + q) - w = (1 / 2 : ℝ) • ((v - w) + (q - w)) := by
    module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)), mul_pow]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (v - w) (q - w)) 2
  nlinarith only [h, sq_nonneg (‖v - w‖ - ‖q - w‖)]

end

end LeanLab.Sliding.TwoLevel.Plain
