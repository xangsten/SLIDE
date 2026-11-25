module

public import LeanLab.AdaptivePlainSliding

set_option linter.style.header false

/-!
# Variable weights in accelerated two-level sliding

The function model has curvature `1 / a`. Choosing the curvature
of the operator loop to be `T / a` gives both center terms a fixed
coefficient after multiplying the gap bound by `a`.
-/

@[expose] public section

namespace LeanLab.Sliding.TwoLevel.Accelerated

open Set
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The weighted gap increment is controlled by one affine model and
the error at the actual trial endpoint. -/
theorem weighted_model_gap {p : E → ℝ} {Q : E → E} {y u v w g : E}
    {A a τ : ℝ} (hA : 0 ≤ A) (ha : 0 < a)
    (hsupportY : let x := mix (a / (A + a)) y u; p x + ⟪g, y - x⟫ ≤ p y)
    (hsupportW : let x := mix (a / (A + a)) y u; p x + ⟪g, w - x⟫ ≤ p w)
    (hupper : let θ := a / (A + a); let x := mix θ y u; let y' := mix θ y v
      p y' ≤ p x + ⟪g, y' - x⟫ + τ / 2 * ‖y' - x‖ ^ 2) :
    (A + a) * gap p Q (mix (a / (A + a)) y v) w - A * gap p Q y w ≤
      a * ⟪g + Q w, v - w⟫ + (τ * a ^ 2 / (A + a)) / 2 * ‖v - u‖ ^ 2 := by
  let B := A + a
  let θ := a / B
  let x := mix θ y u
  let y' := mix θ y v
  have hB : 0 < B := by dsimp [B]; linarith
  have hθ : 0 ≤ θ := (div_pos ha hB).le
  have hleft : 0 ≤ 1 - θ := sub_nonneg.mpr ((div_le_one hB).mpr (by dsimp [B]; linarith))
  have hBa : B * θ = a := mul_div_cancel₀ a hB.ne'
  have hBA : B * (1 - θ) = A := by rw [mul_sub, mul_one, hBa]; dsimp [B]; ring
  have hd : y' - x = θ • (v - u) := by dsimp [x, y', mix]; module
  have hs : (1 - θ) • (y - x) + θ • (w - x) = θ • (w - u) := by
    dsimp [x, mix]; module
  have hsupport : p x + θ * ⟪g, w - u⟫ ≤ (1 - θ) * p y + θ * p w := by
    have hY := mul_le_mul_of_nonneg_left hsupportY hleft
    have hW := mul_le_mul_of_nonneg_left hsupportW hθ
    have hi := congrArg (fun z : E => ⟪g, z⟫) hs
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, real_inner_smul_right] at hi
    change (1 - θ) * (p x + ⟪g, y - x⟫) ≤ (1 - θ) * p y at hY
    change θ * (p x + ⟪g, w - x⟫) ≤ θ * p w at hW
    linarith only [hY, hW, hi]
  change p y' ≤ p x + ⟪g, y' - x⟫ + τ / 2 * ‖y' - x‖ ^ 2 at hupper
  rw [hd, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ, mul_pow] at hupper
  have hsplit : ⟪g, v - w⟫ = ⟪g, v - u⟫ - ⟪g, w - u⟫ := by
    simp only [inner_sub_right]; ring
  have hfun : p y' ≤ (1 - θ) * p y + θ * p w + θ * ⟪g, v - w⟫ +
      τ / 2 * (θ ^ 2 * ‖v - u‖ ^ 2) := by
    rw [hsplit]
    linarith only [hupper, hsupport]
  have hop : y' - w = (1 - θ) • (y - w) + θ • (v - w) := by
    dsimp [y', mix]; module
  have hscaled := mul_le_mul_of_nonneg_left hfun hB.le
  rw [mul_add, mul_add, mul_add, ← mul_assoc B (1 - θ), hBA,
    ← mul_assoc B θ, hBa, ← mul_assoc B θ, hBa] at hscaled
  have hcoef : B * (τ / 2 * (θ ^ 2 * ‖v - u‖ ^ 2)) =
      (τ * a ^ 2 / B) / 2 * ‖v - u‖ ^ 2 := by
    dsimp [θ]
    field_simp
  rw [hcoef] at hscaled
  change B * gap p Q y' w - A * gap p Q y w ≤ _
  unfold gap
  rw [hop, inner_add_right, real_inner_smul_right, real_inner_smul_right, inner_add_left]
  have hQY : B * ((1 - θ) * ⟪Q w, y - w⟫) = A * ⟪Q w, y - w⟫ := by rw [← mul_assoc, hBA]
  have hQV : B * (θ * ⟪Q w, v - w⟫) = a * ⟪Q w, v - w⟫ := by rw [← mul_assoc, hBa]
  linarith only [hscaled, hQY, hQV, show B = A + a by rfl]

/-- With an accepted secant, the weighted gap and both centers form
a fixed potential, even when the trial step varies between iterations. -/
theorem accepted_step {p : E → ℝ} {Q : E → E} {y u v q q' w g : E} {A a τ : ℝ}
    (ha : 0 < a) (hcheck : τ * a ^ 2 / (A + a) ≤ 1 / 2)
    (hgap : (A + a) * gap p Q (mix (a / (A + a)) y v) w - A * gap p Q y w ≤
      a * ⟪g + Q w, v - w⟫ + (τ * a ^ 2 / (A + a)) / 2 * ‖v - u‖ ^ 2)
    (hinner : a * innerGap ⟨1 / a, u, g⟩ Q w v ≤
      (‖q - w‖ ^ 2 - ‖q' - w‖ ^ 2) / 2) :
    (A + a) * gap p Q (mix (a / (A + a)) y v) w +
      (‖v - w‖ ^ 2 + ‖q' - w‖ ^ 2) / 2 + ‖v - u‖ ^ 2 / 4 ≤
      A * gap p Q y w + (‖u - w‖ ^ 2 + ‖q - w‖ ^ 2) / 2 := by
  have hmodel :
      a * innerGap ⟨1 / a, u, g⟩ Q w v =
        a * ⟪g + Q w, v - w⟫ + (‖v - u‖ ^ 2 - ‖u - w‖ ^ 2 + ‖v - w‖ ^ 2) / 2 := by
    unfold innerGap Quadratic.value model
    dsimp only
    simp only [inner_add_left, inner_sub_right, norm_sub_rev w u]
    field_simp
    ring
  rw [hmodel] at hinner
  have hslack := mul_le_mul_of_nonneg_right hcheck (sq_nonneg ‖v - u‖)
  linarith only [hgap, hinner, hslack]

/-- The finite operator loop provides the error term used in `accepted_step`. -/
theorem trial_inner_certificate {D : Set E} (hD : Convex ℝ D) (P : Projection D)
    {Q : E → E} {M a : ℝ} {u q g w : E} (hQ : MonotoneLipschitz D Q M)
    (hq : q ∈ D) (hw : w ∈ D) (ha : 0 < a) {T : ℕ} (hT : 0 < T)
    (hH : 2 * M ≤ (T : ℝ) / a) :
    let m : Quadratic E := ⟨1 / a, u, g⟩
    let s := Plain.innerPass P Q m ((T : ℝ) / a) q T
    a * innerGap m Q w s.average ≤ (‖q - w‖ ^ 2 - ‖s.center - w‖ ^ 2) / 2 := by
  let m : Quadratic E := ⟨1 / a, u, g⟩
  let s := Plain.innerPass P Q m ((T : ℝ) / a) q T
  have hT' : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  have hb := Plain.inner_pass_bound hD P (m := m) (H := (T : ℝ) / a)
    (by dsimp [m]; positivity) (div_pos hT' ha) hQ hH hq hw T
  change (T : ℝ) * innerGap m Q w s.average ≤
    ((T : ℝ) / a) / 2 * (‖q - w‖ ^ 2 - ‖s.center - w‖ ^ 2) at hb
  have hscaled := mul_le_mul_of_nonneg_left hb (div_pos ha hT').le
  change a * innerGap m Q w s.average ≤ (‖q - w‖ ^ 2 - ‖s.center - w‖ ^ 2) / 2
  convert hscaled using 1 <;> field_simp [ha.ne', hT'.ne']

end

end LeanLab.Sliding.TwoLevel.Accelerated
