module

public import LeanLab.PathA.Restart

set_option linter.style.header false

/-!
# Distance contraction for path A under strong convexity

The relative gap already proved for path A bounds the distance to the solution
when the sum of the smooth components is strongly convex.
-/

@[expose] public section

namespace LeanLab.Sliding.PathA

open Set
open TwoLevel (Projection)
open Localized (region)
open scoped BigOperators RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Strong convexity of the sum gives quadratic growth of the composite gap
at any solution of the original variational inequality. -/
theorem Family.strong_convex_gap_lower {n : ℕ} (F : Family E n) {C : Set E} {μ : ℝ}
    (hp : StrongConvexOn C μ (fun y => ∑ i, F.value i y))
    (hg : ∀ i, ∀ x ∈ C, HasGradientWithinAt (F.value i) (F.gradient i x) C x)
    {z y : E} (hz : z ∈ C) (hy : y ∈ C)
    (hVI : ∀ w ∈ C, 0 ≤ ⟪(∑ i, F.gradient i z) + (∑ i, F.operator i z), w - z⟫) :
    μ / 2 * ‖y - z‖ ^ 2 ≤ gap (fun x => ∑ i, F.value i x) (fun x => ∑ i, F.operator i x) y z := by
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap z y
  have hmaps : MapsTo line (Icc 0 1) C := hp.1.mapsTo_lineMap hz hy
  have hzero : line 0 = z := AffineMap.lineMap_apply_zero ..
  have hline : HasDerivWithinAt (fun t => line t) (y - z) (Icc 0 1) 0 :=
    AffineMap.hasDerivWithinAt_lineMap
  have hconv :=
    (((strongConvexOn_iff_convex.mp hp).comp_affineMap line).subset hmaps (convex_Icc 0 1))
  have hsum : HasDerivWithinAt (fun t => ∑ i, F.value i (line t))
      (∑ i, ⟪F.gradient i z, y - z⟫) (Icc 0 1) 0 := by
    apply HasDerivWithinAt.fun_sum
    intro i _
    have hd := (hg i z hz).hasFDerivWithinAt
    rw [← hzero] at hd
    simpa only [InnerProductSpace.toDual_apply_apply, hzero, Function.comp_def] using
      hd.comp_hasDerivWithinAt 0 hline hmaps
  have hd := hsum.sub (hline.norm_sq.const_mul (μ / 2))
  have hs := hconv.le_slope_of_hasDerivWithinAt (by simp) (by simp) zero_lt_one hd
  simp only [slope_def_field, Function.comp_def, sub_zero, div_one, hzero,
    show line 1 = y from AffineMap.lineMap_apply_one .., ← sum_inner] at hs
  have hnorm : ‖y‖ ^ 2 = ‖z‖ ^ 2 + 2 * ⟪z, y - z⟫ + ‖y - z‖ ^ 2 := by
    conv_lhs => rw [show y = z + (y - z) by abel, norm_add_sq_real]
  have hv := hVI y hy
  rw [inner_add_left] at hv
  unfold gap
  linarith only [hs, hv, congrArg (fun a : ℝ => μ / 2 * a) hnorm]

/-- A complete path A run at relative accuracy μ/8 halves the distance to
the solution under strong convexity of the sum. -/
theorem Family.pathA_of_symmetric_contracts [ProperSpace E] {n : ℕ}
    (F : Family E (n + 1)) {C : Set E} (hclosed : IsClosed C) (hC : Convex ℝ C)
    (hp : ∀ i, ConvexOn ℝ C (F.value i))
    (hg : ∀ i, ∀ x ∈ C, HasGradientWithinAt (F.value i) (F.gradient i x) C x)
    (hQ : ∀ i, TwoLevel.MonotoneLipschitz C (F.operator i) (F.lipschitz i))
    (L₀ L₁ : Fin (n + 1) → ℝ)
    (hsmooth : ∀ i, SymmetricSmoothOn C (F.gradient i) (L₀ i) (L₁ i))
    {s z : E} (hs : s ∈ C) (hz : z ∈ C)
    (hVI : ∀ w ∈ C, 0 ≤ ⟪(∑ i, F.gradient i z) + (∑ i, F.operator i z), w - z⟫)
    (project : ∀ R, 0 < R → Projection (region C s R))
    {μ R₀ : ℝ} (hμ : 0 < μ) (hR₀ : 0 < R₀) (Λ₀ : Fin (n + 1) → ℝ)
    (hstrong : StrongConvexOn C μ (fun w => ∑ i, F.value i w)) :
    let δ := (μ / 8) / 3
    let a := initialParameters δ R₀ Λ₀
    let L := F.smoothCaps L₀ L₁ C s (max R₀ (24 * ‖s - z‖))
    let cap := parameterCaps a ‖s - z‖ L
    let result := restart (F.attempt δ s project) (remaining cap a + 1) a
    ∃ (b : Parameters (n + 1)) (y : E), result.outcome = some (b, y) ∧ y ∈ C ∧
      ‖y - z‖ ≤ ‖s - z‖ / 2 := by
  have h := F.pathA_of_symmetric hclosed hC hp hg hQ L₀ L₁ hsmooth hs hz hVI project
    (show 0 < μ / 8 by positivity) hR₀ Λ₀
  obtain ⟨b, y, hout, hy, _, _, hgap, _⟩ := h
  refine ⟨b, y, hout, hy, ?_⟩
  have hlower := F.strong_convex_gap_lower hstrong hg hz hy hVI
  have hupper := hgap z hz
  rw [norm_sub_rev z s] at hupper
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (by positivity)
  apply le_of_mul_le_mul_left _ hμ
  nlinarith only [hlower, hupper]

end LeanLab.Sliding.PathA
