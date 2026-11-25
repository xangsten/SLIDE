module

public import Mathlib

set_option linter.style.header false

/-!
# Generalized smoothness in recursive sliding

The curvature check supplies a quadratic upper bound for a single accepted step.
The lemmas below give the projected model comparison, the transfer between
levels, the telescoping estimate, and the extension from a ball to the domain.
-/

@[expose] public section

namespace LeanLab.Sliding

open Set
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The gap uses the value of the operator at the comparison point. -/
def gap (f : E → ℝ) (Q : E → E) (z w : E) : ℝ :=
  f z - f w + ⟪Q w, z - w⟫

/-- One quadratic model in the recursion. -/
def model (H : ℝ) (u slope z : E) : ℝ :=
  H / 2 * ‖z - u‖ ^ 2 + ⟪slope, z⟫

/-- The variational inequality characterizing the projection gives a
Pythagorean inequality against each feasible comparison point. -/
theorem projection_bound {a x w : E} (h : ⟪a - x, w - x⟫ ≤ 0) :
    ‖x - w‖ ^ 2 + ‖a - x‖ ^ 2 ≤ ‖a - w‖ ^ 2 := by
  have hsplit : a - w = (a - x) - (w - x) := by abel
  conv_rhs => rw [hsplit, norm_sub_sq_real, norm_sub_rev w x]
  linarith

/-- Scaling the input by β and the function values by its reciprocal
leaves the model slope unchanged and multiplies the curvature by β. -/
theorem affine_model {f : E → ℝ} {u v b g : E} {β τ : ℝ} (hβ : 0 < β)
    (hupper : f (β • v + b) ≤ f (β • u + b) +
      ⟪g, (β • v + b) - (β • u + b)⟫ + τ / 2 * ‖(β • v + b) - (β • u + b)‖ ^ 2) :
    f (β • v + b) / β ≤ f (β • u + b) / β + ⟪g, v - u⟫ + (β * τ) / 2 * ‖v - u‖ ^ 2 := by
  have hd : (β • v + b) - (β • u + b) = β • (v - u) := by module
  rw [hd, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hβ] at hupper
  apply (div_le_iff₀ hβ).mpr
  calc
    _ ≤ _ := hupper
    _ = _ := by field_simp

/-- The curvature arising from the accepted check and the operator term. -/
theorem accepted_curvature {β s Λ τ M : ℝ}
    (hs : 0 < s) (hβ : s ≤ β) (hΛ : τ ≤ Λ) (hM : 0 ≤ M) :
    β * τ + 2 * M ≤ β * (Λ + 2 * M / s) := by
  have hpart := mul_le_mul_of_nonneg_left hΛ (show 0 ≤ β by linarith)
  have hratio : 2 * M ≤ β * (2 * M / s) := by
    calc
      2 * M ≤ (2 * M * β) / s := (le_div_iff₀ hs).mpr
        (mul_le_mul_of_nonneg_left hβ (by positivity))
      _ = β * (2 * M / s) := by ring
  linarith [mul_add β Λ (2 * M / s)]

/-- The projected comparison in equation (11) of the draft. The two
inequalities on f come from the accepted quadratic model and convexity. -/
theorem model_comparison_of_curvature
    {f : E → ℝ} {Q : E → E} {u v w next g : E} {H ℓ M : ℝ}
    (hH : 0 < H) (hℓ : 0 ≤ ℓ) (hM : 0 ≤ M) (hcurv : ℓ + M ≤ H)
    (hupper : f v ≤ f u + ⟪g, v - u⟫ + ℓ / 2 * ‖v - u‖ ^ 2)
    (hsupport : f u + ⟪g, w - u⟫ ≤ f w)
    (hmono : 0 ≤ ⟪Q v - Q w, v - w⟫)
    (hlip : ‖Q u - Q v‖ ≤ M * ‖v - u‖)
    (hproj : ⟪v + H⁻¹ • (Q u - Q v) - next, w - next⟫ ≤ 0) :
    gap f Q v w + H / 2 * (‖next - w‖ ^ 2 - ‖u - w‖ ^ 2) ≤
      model H u (g + Q u) v - model H u (g + Q u) w + H / 2 * ‖v - w‖ ^ 2 := by
  have hd := projection_bound hproj
  have hsplit :
      v + H⁻¹ • (Q u - Q v) - w = (v - w) + H⁻¹ • (Q u - Q v) := by abel
  rw [hsplit, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hH.le), real_inner_comm (Q u - Q v) (v - w)] at hd
  have hcomplete :
      H / 2 * ‖next - w‖ ^ 2 ≤ H / 2 * ‖v - w‖ ^ 2 +
        ⟪Q u - Q v, v - w⟫ + ‖Q u - Q v‖ ^ 2 / (2 * H) := by
    have hdrop := le_add_of_nonneg_right (a := ‖next - w‖ ^ 2)
      (sq_nonneg ‖v + H⁻¹ • (Q u - Q v) - next‖)
    have hscaled := mul_le_mul_of_nonneg_left (hdrop.trans hd) (show 0 ≤ H / 2 by positivity)
    refine hscaled.trans_eq ?_
    field_simp
  have hMle : M ≤ H := by linarith
  have hcoef : M * M / (2 * H) ≤ (H - ℓ) / 2 := by
    apply (div_le_iff₀ (show 0 < 2 * H by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_left hMle hM
    have hc := mul_le_mul_of_nonneg_right (show M ≤ H - ℓ by linarith) hH.le
    nlinarith
  have hcost : ‖Q u - Q v‖ ^ 2 / (2 * H) ≤ (H - ℓ) / 2 * ‖v - u‖ ^ 2 := by
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hlip 2
    calc
      _ ≤ (M * ‖v - u‖) ^ 2 / (2 * H) := div_le_div_of_nonneg_right hsq (by positivity)
      _ = (M * M / (2 * H)) * ‖v - u‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
  unfold gap model
  rw [norm_sub_rev w u]
  simp only [inner_add_left, inner_sub_left, inner_sub_right] at hmono hcomplete ⊢
  simp only [inner_sub_right] at hupper hsupport
  linarith only [hmono, hcomplete, hupper, hsupport, hcost]

/-- Projected model comparison with the conservative curvature used by the
two-level search. -/
theorem model_comparison
    {f : E → ℝ} {Q : E → E} {u v w next g : E} {H ℓ M : ℝ}
    (hH : 0 < H) (hℓ : 0 ≤ ℓ) (hM : 0 ≤ M) (hcurv : ℓ + 2 * M ≤ H)
    (hupper : f v ≤ f u + ⟪g, v - u⟫ + ℓ / 2 * ‖v - u‖ ^ 2)
    (hsupport : f u + ⟪g, w - u⟫ ≤ f w)
    (hmono : 0 ≤ ⟪Q v - Q w, v - w⟫)
    (hlip : ‖Q u - Q v‖ ≤ M * ‖v - u‖)
    (hproj : ⟪v + H⁻¹ • (Q u - Q v) - next, w - next⟫ ≤ 0) :
    gap f Q v w + H / 2 * (‖next - w‖ ^ 2 - ‖u - w‖ ^ 2) ≤
      model H u (g + Q u) v - model H u (g + Q u) w + H / 2 * ‖v - w‖ ^ 2 :=
  model_comparison_of_curvature hH hℓ hM (by linarith) hupper hsupport hmono hlip hproj

/-- The leaf computes a projection of the sum's quadratic center. Given the
first-order condition for that minimum, the leaf potential is nonpositive. -/
theorem leaf_bound {H : ℝ} {u slope v w : E}
    (hmin : 0 ≤ ⟪H • (v - u) + slope, w - v⟫) :
    model H u slope v - model H u slope w + H / 2 * ‖v - w‖ ^ 2 ≤ 0 := by
  have hsplit : w - u = (v - u) + (w - v) := by abel
  have hnorm : ‖w - u‖ ^ 2 =
      ‖v - u‖ ^ 2 + 2 * ⟪v - u, w - v⟫ + ‖v - w‖ ^ 2 := by
    conv_lhs => rw [hsplit, norm_add_sq_real, norm_sub_rev w v]
  simp only [inner_add_left, real_inner_smul_left] at hmin
  unfold model
  rw [hnorm]
  have hs : ⟪slope, w - v⟫ = ⟪slope, w⟫ - ⟪slope, v⟫ := inner_sub_right ..
  linarith only [hmin, hs]

/-- The bridge between levels, equation (13). The function f aggregates
the nonlinear terms still being transformed; r aggregates the carried
convex terms, including the affine contributions of the remaining operators. -/
theorem transfer
    {D : Set E} {f r : E → ℝ} {y v w : E} {α child correction : ℝ}
    (hf : ConvexOn ℝ D f) (hr : ConvexOn ℝ D r)
    (hy : y ∈ D) (hv : v ∈ D) (hw : w ∈ D) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hchild : (f ((1 - α) • y + α • v) - f ((1 - α) • y + α • w)) / α +
      (r v - r w) + correction ≤ child) :
    ((f ((1 - α) • y + α • v) + r ((1 - α) • y + α • v) - (f w + r w)) -
      (1 - α) * (f y + r y - (f w + r w))) / α + correction ≤ child := by
  have h₁ : 0 ≤ 1 - α := sub_nonneg.mpr hα₁
  have hw' := hf.2 hy hw h₁ hα.le (sub_add_cancel 1 α)
  have hv' := hr.2 hy hv h₁ hα.le (sub_add_cancel 1 α)
  change f _ ≤ (1 - α) * f y + α * f w at hw'
  change r _ ≤ (1 - α) * r y + α * r v at hv'
  have hineq :
      (f ((1 - α) • y + α • v) + r ((1 - α) • y + α • v) - (f w + r w)) -
          (1 - α) * (f y + r y - (f w + r w)) ≤
        f ((1 - α) • y + α • v) - f ((1 - α) • y + α • w) + α * (r v - r w) := by
    linarith
  have hdiv := div_le_div_of_nonneg_right hineq hα.le
  rw [add_div, mul_div_cancel_left₀ _ hα.ne'] at hdiv
  linarith only [hdiv, hchild]

/-- The child's bound and the corrected model inequality imply the
per-iteration bound (15), before the sum over iterations. -/
theorem iteration_bound {F Fnext child α β c d dnext tail tailNext : ℝ}
    (hα : 0 < α)
    (htransfer : (Fnext - (1 - α) * F) / α + (β * α * c / 2) * (dnext - d) ≤ child)
    (hchild : child ≤ β * α / 2 * (tail - tailNext)) :
    (Fnext - (1 - α) * F) / α ^ 2 ≤
      β / 2 * ((c * d + tail) - (c * dnext + tailNext)) := by
  have h := htransfer.trans hchild
  apply (div_le_iff₀ (sq_pos_of_pos hα)).mpr
  have hscaled := mul_le_mul_of_nonneg_right h hα.le
  rw [add_mul, div_mul_cancel₀ _ hα.ne'] at hscaled
  linarith only [hscaled]

/-- The telescope in (15). The recurrence on the weights removes every
intermediate gap, and the centered potential telescopes separately. -/
theorem telescope {α F P : ℕ → ℝ}
    (hα : ∀ t, 0 < α t) (hfirst : α 0 = 1)
    (hrec : ∀ t, (1 - α (t + 1)) / α (t + 1) ^ 2 = 1 / α t ^ 2)
    (t : ℕ)
    (hstep : ∀ j ≤ t, (F (j + 1) - (1 - α j) * F j) / α j ^ 2 ≤ P j - P (j + 1)) :
    F (t + 1) ≤ α t ^ 2 * (P 0 - P (t + 1)) := by
  suffices h : F (t + 1) / α t ^ 2 ≤ P 0 - P (t + 1) by
    have h' := (div_le_iff₀ (sq_pos_of_pos (hα t))).mp h
    simpa only [mul_comm] using h'
  revert hstep
  induction t with
  | zero =>
    intro hstep
    simpa [hfirst] using hstep 0 le_rfl
  | succ t ih =>
    intro hstep
    have hprev := ih fun j hj => hstep j (hj.trans (Nat.le_succ t))
    have h := hstep (t + 1) le_rfl
    rw [sub_div, mul_comm (1 - α (t + 1)), mul_div_assoc, hrec, mul_one_div] at h
    linarith only [h, hprev]

omit [InnerProductSpace ℝ E] in
/-- The radius argument in section 5.5. The energy estimate bounds both
centers; the projected correction moves at most half the trial displacement. -/
theorem trial_radius {u next v solution : E} {r : ℝ}
    (hu : ‖u - solution‖ ≤ Real.sqrt 2 * r)
    (hnext : ‖next - solution‖ ≤ Real.sqrt 2 * r)
    (hmove : ‖v - next‖ ≤ ‖v - u‖ / 2) :
    ‖v - solution‖ ≤ 3 * Real.sqrt 2 * r := by
  have hfirst : v - solution = (v - next) + (next - solution) := by abel
  have hsecond : v - u = (v - solution) - (u - solution) := by abel
  have htri : ‖v - solution‖ ≤ ‖v - next‖ + ‖next - solution‖ := by
    rw [hfirst]
    exact norm_add_le _ _
  have htrial : ‖v - u‖ ≤ ‖v - solution‖ + ‖u - solution‖ := by
    rw [hsecond]
    exact norm_sub_le _ _
  linarith only [hu, hnext, hmove, htri, htrial]

/-- The correction satisfies the movement premise of `trial_radius` when
the operator contribution to the curvature is at least twice its
Lipschitz constant. -/
theorem correction_move {Q : E → E} {u v next : E} {H M : ℝ}
    (hH : 0 < H) (hM : 2 * M ≤ H) (hlip : ‖Q u - Q v‖ ≤ M * ‖v - u‖)
    (hproj : ⟪v + H⁻¹ • (Q u - Q v) - next, v - next⟫ ≤ 0) :
    ‖v - next‖ ≤ ‖v - u‖ / 2 := by
  have h := projection_bound hproj
  have heq : v + H⁻¹ • (Q u - Q v) - v = H⁻¹ • (Q u - Q v) := by abel
  rw [heq, norm_sub_rev next v] at h
  have hnorm : ‖v - next‖ ≤ ‖H⁻¹ • (Q u - Q v)‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    linarith only [h, sq_nonneg ‖v + H⁻¹ • (Q u - Q v) - next‖]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hH), ← div_eq_inv_mul] at hnorm
  refine hnorm.trans ((div_le_iff₀ hH).mpr ?_)
  refine hlip.trans ?_
  have hm := mul_le_mul_of_nonneg_right hM (norm_nonneg (v - u))
  linarith only [hm]

/-- Each failed curvature check at a fixed radius at least doubles the
estimate, and updates it to at most twice the bound on the threshold. -/
theorem curvature_update {Λ τ K : ℝ} (hfail : Λ < τ) (hK : τ ≤ K) (hΛ : 0 ≤ Λ) :
    2 * Λ ≤ max (2 * Λ) τ ∧ max (2 * Λ) τ ≤ 2 * K := by
  exact ⟨le_max_left .., max_le (by linarith) (by linarith)⟩

/-- A positive estimate below a fixed bound cannot keep doubling.
This applies to the radius and to each subsequence of failed curvature checks. -/
theorem finite_doublings {x : ℕ → ℝ} {B : ℝ}
    (hx : 0 < x 0) (hB : ∀ n, x n ≤ B) :
    ∃ n, x (n + 1) < 2 * x n := by
  by_contra! h
  have hlower (n : ℕ) : (2 : ℝ) ^ n * x 0 ≤ x n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_assoc]
      exact (mul_le_mul_of_nonneg_left ih (by norm_num)).trans (h n)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B / x 0) (show (1 : ℝ) < 2 by norm_num)
  exact (not_lt_of_ge ((hlower n).trans (hB n))) ((div_lt_iff₀ hx).mp hn)

/-- A gradient secant bounds the quadratic-model error. This gives a
curvature test using the gradient at the trial endpoint in addition to g. -/
theorem secant_model {f : E → ℝ} {x y gx gy : E} {A : ℝ}
    (hy : f y + ⟪gy, x - y⟫ ≤ f x)
    (hgrad : ‖gy - gx‖ ≤ A * ‖y - x‖) :
    f y - f x - ⟪gx, y - x⟫ ≤ ⟪gy - gx, y - x⟫ ∧
    ⟪gy - gx, y - x⟫ ≤ A * ‖y - x‖ ^ 2 := by
  constructor
  · rw [inner_sub_left]
    have hd : x - y = -(y - x) := by abel
    rw [hd, inner_neg_right] at hy
    linarith
  · calc
      _ ≤ ‖gy - gx‖ * ‖y - x‖ := real_inner_le_norm _ _
      _ ≤ (A * ‖y - x‖) * ‖y - x‖ := mul_le_mul_of_nonneg_right hgrad (norm_nonneg _)
      _ = _ := by ring

/-- The secant threshold certifies the trial model and is at most twice
the Lipschitz bound on the segment. In the zero-displacement case Lean's
division by zero makes the threshold zero. -/
theorem secant_threshold {f : E → ℝ} {x y gx gy : E} {A : ℝ}
    (hA : 0 ≤ A) (hy : f y + ⟪gy, x - y⟫ ≤ f x)
    (hgrad : ‖gy - gx‖ ≤ A * ‖y - x‖) :
    let τ := 2 * ⟪gy - gx, y - x⟫ / ‖y - x‖ ^ 2
    f y ≤ f x + ⟪gx, y - x⟫ + τ / 2 * ‖y - x‖ ^ 2 ∧ τ ≤ 2 * A := by
  rcases eq_or_ne y x with rfl | hne
  · simp [hA]
  have hd : 0 < ‖y - x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  obtain ⟨herror, hcurv⟩ := secant_model hy hgrad
  dsimp only
  have hcancel :
      (2 * ⟪gy - gx, y - x⟫ / ‖y - x‖ ^ 2) / 2 * ‖y - x‖ ^ 2 =
        ⟪gy - gx, y - x⟫ := by
    field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)]
  constructor
  · rw [hcancel]
    linarith only [herror]
  · apply (div_le_iff₀ hd).mpr
    linarith only [hcurv]

/-- Convexity and monotonicity compare the gap at the end of a segment
with the gap at an intermediate comparison point. -/
theorem gap_on_segment {D : Set E} {f : E → ℝ} {Q : E → E}
    (hf : ConvexOn ℝ D f)
    (hQ : ∀ x ∈ D, ∀ y ∈ D, 0 ≤ ⟪Q x - Q y, x - y⟫)
    {z w : E} (hz : z ∈ D) (hw : w ∈ D)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ₁ : θ < 1) :
    θ * gap f Q z w ≤ gap f Q z ((1 - θ) • z + θ • w) := by
  let w' := (1 - θ) • z + θ • w
  have h₁ : 0 ≤ 1 - θ := by linarith
  have hw' : w' ∈ D := hf.1 hz hw h₁ hθ (sub_add_cancel 1 θ)
  have hf' := hf.2 hz hw h₁ hθ (sub_add_cancel 1 θ)
  change f w' ≤ (1 - θ) * f z + θ * f w at hf'
  have hsub : z - w' = θ • (z - w) := by
    dsimp [w']
    module
  have hsub' : w - w' = (1 - θ) • (w - z) := by
    dsimp [w']
    module
  have hm := hQ w hw w' hw'
  rw [hsub', real_inner_smul_right] at hm
  have hm' := nonneg_of_mul_nonneg_right hm (sub_pos.mpr hθ₁)
  have hr : w - z = -(z - w) := by abel
  rw [hr, inner_neg_right, inner_sub_left] at hm'
  have hmon := mul_le_mul_of_nonneg_left (show ⟪Q w, z - w⟫ ≤ ⟪Q w', z - w⟫ by
    linarith) hθ
  change θ * gap f Q z w ≤ gap f Q z w'
  unfold gap
  rw [hsub, real_inner_smul_right]
  linarith

/-- The local coefficient in (16) is also valid on the entire domain.
The interpolation weight is R / (2r - R), where r is the distance
from the initial point to the comparison point. -/
theorem global_gap_bound {C : Set E} {f : E → ℝ} {Q : E → E} {z zin : E} {R K : ℝ}
    (hf : ConvexOn ℝ C f)
    (hQ : ∀ x ∈ C, ∀ y ∈ C, 0 ≤ ⟪Q x - Q y, x - y⟫)
    (hz : z ∈ C) (hR : 0 < R) (hK : 0 ≤ K)
    (hradius : ‖z - zin‖ ≤ R / 2)
    (hlocal : ∀ w ∈ C, ‖w - zin‖ ≤ R → gap f Q z w ≤ K * ‖w - zin‖ ^ 2)
    (w : E) (hw : w ∈ C) : gap f Q z w ≤ K * ‖w - zin‖ ^ 2 := by
  by_cases hlocalw : ‖w - zin‖ ≤ R
  · exact hlocal w hw hlocalw
  · let r := ‖w - zin‖
    have hr : R < r := lt_of_not_ge hlocalw
    have hden : 0 < 2 * r - R := by linarith
    let θ := R / (2 * r - R)
    have hθ : 0 < θ := div_pos hR hden
    have hθ₁ : θ < 1 := (div_lt_iff₀ hden).mpr (by linarith)
    have hweights : (1 - θ) + θ = 1 := sub_add_cancel 1 θ
    have h₁ : 0 ≤ 1 - θ := by linarith
    let w' := (1 - θ) • z + θ • w
    have hw' : w' ∈ C := hf.1 hz hw h₁ hθ.le hweights
    have hbalance : θ * (2 * r - R) = R := div_mul_cancel₀ _ hden.ne'
    have hsplit : w' - zin = (1 - θ) • (z - zin) + θ • (w - zin) := by
      dsimp [w']
      module
    have hball : ‖w' - zin‖ ≤ R := by
      calc
        _ ≤ (1 - θ) * ‖z - zin‖ + θ * r := by
          rw [hsplit]
          simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg h₁, abs_of_pos hθ] using
            norm_add_le ((1 - θ) • (z - zin)) (θ • (w - zin))
        _ ≤ (1 - θ) * (R / 2) + θ * r :=
          add_le_add_left (mul_le_mul_of_nonneg_left hradius h₁) _
        _ = R := by linarith [show θ * (2 * r - R) = 2 * (θ * r) - θ * R by ring]
    have hsegment := gap_on_segment hf hQ hz hw hθ.le hθ₁
    have hlocal' := hlocal w' hw' hball
    have hbound := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hball 2) hK
    have hscaled : θ * gap f Q z w ≤ K * R ^ 2 := hsegment.trans (hlocal'.trans hbound)
    have hgeom : R ^ 2 ≤ θ * r ^ 2 := by
      change R ^ 2 ≤ (R / (2 * r - R)) * r ^ 2
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hden).mpr
      nlinarith [mul_nonneg hR.le (sq_nonneg (r - R))]
    apply le_of_mul_le_mul_left _ hθ
    calc
      θ * gap f Q z w ≤ K * R ^ 2 := hscaled
      _ ≤ K * (θ * r ^ 2) := mul_le_mul_of_nonneg_left hgeom hK
      _ = θ * (K * r ^ 2) := by ring

/-- The reciprocal of the accelerated weight, with the update in (4). -/
def reciprocalWeight : ℕ → ℝ
  | 0 => 1
  | t + 1 => (1 + Real.sqrt (1 + 4 * reciprocalWeight t ^ 2)) / 2

/-- The reciprocal weights grow by at least one half per iteration. -/
theorem reciprocalWeight_lower (t : ℕ) : ((t : ℝ) + 2) / 2 ≤ reciprocalWeight t := by
  induction t with
  | zero => norm_num [reciprocalWeight]
  | succ t ih =>
    rw [reciprocalWeight, Nat.cast_succ]
    have hroot : 2 * reciprocalWeight t ≤ Real.sqrt (1 + 4 * reciprocalWeight t ^ 2) := by
      apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
      rw [Real.sq_sqrt (by positivity)]
      linarith
    linarith only [ih, hroot]

/-- The weights used in the algorithm. -/
def weight (t : ℕ) : ℝ := (reciprocalWeight t)⁻¹

theorem weight_pos (t : ℕ) : 0 < weight t := by
  have hlower := reciprocalWeight_lower t
  exact inv_pos.mpr (lt_of_lt_of_le (by positivity) hlower)

theorem weight_zero : weight 0 = 1 := by simp [weight, reciprocalWeight]

theorem weight_recurrence (t : ℕ) :
    (1 - weight (t + 1)) / weight (t + 1) ^ 2 = 1 / weight t ^ 2 := by
  have hpos (j : ℕ) : 0 < reciprocalWeight j := inv_pos.mp (weight_pos j)
  have hquadratic : reciprocalWeight (t + 1) ^ 2 - reciprocalWeight (t + 1) =
      reciprocalWeight t ^ 2 := by
    rw [reciprocalWeight]
    nlinarith only [Real.sq_sqrt (show 0 ≤ 1 + 4 * reciprocalWeight t ^ 2 by positivity)]
  unfold weight
  field_simp [(hpos t).ne', (hpos (t + 1)).ne']
  linarith only [hquadratic]

theorem weight_upper (t : ℕ) : weight t ≤ 2 / ((t : ℝ) + 2) := by
  have hlower := reciprocalWeight_lower t
  have hbase : 0 < ((t : ℝ) + 2) / 2 := by positivity
  simpa [weight, inv_div] using inv_anti₀ hbase hlower

/-- The gap theorem for an accepted pass. The hypothesis hstep expresses
the per-iteration bound (15) for the top level; c includes the factor 1/2
and the weights from the inner levels. -/
theorem accepted_pass_gap {ι : Type*} [Fintype ι]
    {C : Set E} {f : E → ℝ} {Q : E → E} {zin : E} {R : ℝ}
    {α : ℕ → ℝ} {y : ℕ → E} {U : ι → ℕ → E} {c : ι → ℝ} {t : ℕ}
    (hf : ConvexOn ℝ C f)
    (hQ : ∀ x ∈ C, ∀ w ∈ C, 0 ≤ ⟪Q x - Q w, x - w⟫)
    (hR : 0 < R) (hout : y (t + 1) ∈ C) (haccept : ‖y (t + 1) - zin‖ ≤ R / 2)
    (hα : ∀ j, 0 < α j) (hfirst : α 0 = 1)
    (hrec : ∀ j, (1 - α (j + 1)) / α (j + 1) ^ 2 = 1 / α j ^ 2)
    (hc : ∀ i, 0 ≤ c i) (hinit : ∀ i, U i 0 = zin)
    (hstep : ∀ w ∈ C, ‖w - zin‖ ≤ R → ∀ j ≤ t,
      (gap f Q (y (j + 1)) w - (1 - α j) * gap f Q (y j) w) / α j ^ 2 ≤
        (∑ i, c i * ‖U i j - w‖ ^ 2) - (∑ i, c i * ‖U i (j + 1) - w‖ ^ 2))
    (w : E) (hw : w ∈ C) :
    gap f Q (y (t + 1)) w ≤ (α t ^ 2 * ∑ i, c i) * ‖w - zin‖ ^ 2 := by
  have hsum : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  apply global_gap_bound hf hQ hout hR (mul_nonneg (sq_nonneg _) hsum) haccept _ w hw
  intro w' hw' hball
  have h := telescope (F := fun j => gap f Q (y j) w')
    (P := fun j => ∑ i, c i * ‖U i j - w'‖ ^ 2) hα hfirst hrec t (hstep w' hw' hball)
  have hlast : 0 ≤ ∑ i, c i * ‖U i (t + 1) - w'‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (sq_nonneg _)
  simp only [hinit, norm_sub_rev zin w', ← Finset.sum_mul] at h
  rw [mul_assoc]
  exact h.trans (mul_le_mul_of_nonneg_left (sub_le_self _ hlast) (sq_nonneg _))

/-- A limit of feasible outputs with vanishing gap bounds solves the
variational inequality. Apply this to any convergent subsequence. -/
theorem limit_solves {C : Set E} {f : E → ℝ} {Q : E → E} {zin solution : E}
    {z : ℕ → E} {K : ℕ → ℝ}
    (hC : IsClosed C) (hf : Continuous f)
    (hz : Filter.Tendsto z Filter.atTop (nhds solution))
    (hK : Filter.Tendsto K Filter.atTop (nhds 0))
    (hfeasible : ∀ n, z n ∈ C)
    (hgap : ∀ n, ∀ w ∈ C, gap f Q (z n) w ≤ K n * ‖zin - w‖ ^ 2) :
    solution ∈ C ∧ ∀ w ∈ C, gap f Q solution w ≤ 0 := by
  refine ⟨hC.mem_of_tendsto hz (Filter.Eventually.of_forall hfeasible), ?_⟩
  intro w hw
  have hcont : Continuous (fun x => gap f Q x w) := by
    unfold gap
    exact (hf.sub continuous_const).add
      (continuous_const.inner (continuous_id.sub continuous_const))
  have hleft := (hcont.tendsto solution).comp hz
  have hright := hK.mul_const (‖zin - w‖ ^ 2)
  have h := le_of_tendsto_of_tendsto' hleft hright (fun n => hgap n w hw)
  simpa only [zero_mul] using h

end

end LeanLab.Sliding
