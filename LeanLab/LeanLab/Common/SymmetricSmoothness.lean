module

public import Mathlib

set_option linter.style.header false

/-!
# Symmetric generalized smoothness

Segment bounds, affine scaling, and localization for the operator version of
symmetric `(L₀, L₁)`-smoothness. This applies both to gradients in the working
Hilbert norm and to the aggregate operator when it satisfies the same condition.
-/

@[expose] public section

namespace LeanLab.Sliding

open Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The segment form of symmetric generalized smoothness. Continuity on the
domain ensures the norm of the oracle is bounded on each contained segment. -/
structure SymmetricSmoothOn (D : Set E) (g : E → E) (L₀ L₁ : ℝ) : Prop where
  continuousOn : ContinuousOn g D
  zero_nonneg : 0 ≤ L₀
  one_nonneg : 0 ≤ L₁
  segment_bound : ∀ x ∈ D, ∀ y ∈ D,
    ‖g y - g x‖ ≤ (L₀ + L₁ * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖y - x‖

namespace SymmetricSmoothOn

variable {D : Set E} {g : E → E} {L₀ L₁ : ℝ}

/-- A uniform bound on the local coefficient along a segment controls its secant. -/
theorem norm_sub_le (h : SymmetricSmoothOn D g L₀ L₁) {x y : E}
    (hx : x ∈ D) (hy : y ∈ D) (hseg : segment ℝ x y ⊆ D) {B : ℝ}
    (hB : ∀ z ∈ segment ℝ x y, L₀ + L₁ * ‖g z‖ ≤ B) :
    ‖g y - g x‖ ≤ B * ‖y - x‖ := by
  have hcompact : IsCompact ((fun z => ‖g z‖) '' segment ℝ x y) :=
    (show IsCompact (segment ℝ x y) by
      rw [segment_eq_image']
      exact isCompact_Icc.image (by fun_prop)).image_of_continuousOn
        (h.continuousOn.norm.mono hseg)
  have hne : ((fun z => ‖g z‖) '' segment ℝ x y).Nonempty :=
    ⟨‖g x‖, ⟨x, left_mem_segment ℝ x y, rfl⟩⟩
  obtain ⟨z, hz, heq⟩ := hcompact.sSup_mem hne
  exact (h.segment_bound x hx y hy).trans <|
    mul_le_mul_of_nonneg_right (heq ▸ hB z hz) (norm_nonneg _)

/-- One affine scaling of the oracle argument scales both parameters. -/
theorem homothety (h : SymmetricSmoothOn D g L₀ L₁) (hD : Convex ℝ D)
    {c : E} (hc : c ∈ D) {α : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1) :
    SymmetricSmoothOn D (g ∘ AffineMap.homothety c α) (α * L₀) (α * L₁) := by
  let T : E →ᵃ[ℝ] E := AffineMap.homothety c α
  have hmaps : MapsTo T D D := by
    intro x hx
    change AffineMap.homothety c α x ∈ D
    rw [AffineMap.homothety_eq_lineMap]
    exact hD.mapsTo_lineMap hc hx ⟨hα, hα₁⟩
  have hcont : Continuous T := by
    simp only [T, AffineMap.coe_homothety, vsub_eq_sub, vadd_eq_add]
    fun_prop
  refine ⟨h.continuousOn.comp hcont.continuousOn hmaps, mul_nonneg hα h.zero_nonneg,
    mul_nonneg hα h.one_nonneg, ?_⟩
  intro x hx y hy
  have hdist : ‖T y - T x‖ = α * ‖y - x‖ := by
    simp only [T, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_sub_add_right_eq_sub]
    rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul_of_nonneg hα]
  have hs := h.segment_bound (T x) (hmaps hx) (T y) (hmaps hy)
  rw [← image_segment ℝ T x y, image_image, hdist] at hs
  change ‖g (T y) - g (T x)‖ ≤
    (α * L₀ + α * L₁ * sSup ((fun z => ‖g (T z)‖) '' segment ℝ x y)) * ‖y - x‖
  convert hs using 1
  ring

/-- The exponential coefficient bound along a segment follows from the
right difference quotients of the norm of the oracle. -/
theorem coefficient_le_exp (h : SymmetricSmoothOn D g L₀ L₁) (hD : Convex ℝ D)
    {x y : E} (hx : x ∈ D) (hy : y ∈ D) :
    L₀ + L₁ * ‖g y‖ ≤ (L₀ + L₁ * ‖g x‖) * Real.exp (L₁ * ‖y - x‖) := by
  let T : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  let φ : ℝ → ℝ := fun t => L₀ + L₁ * ‖g (T t)‖
  let K : ℝ := L₁ * ‖y - x‖
  have hmaps : MapsTo T (Icc 0 1) D := hD.mapsTo_lineMap hx hy
  have hT : Continuous T := by
    change Continuous (fun t : ℝ => AffineMap.lineMap x y t)
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    fun_prop
  have hφ : ContinuousOn φ (Icc 0 1) :=
    continuousOn_const.add (continuousOn_const.mul (h.continuousOn.comp
      hT.continuousOn hmaps).norm)
  have hdiff : ∀ t ∈ Ico (0 : ℝ) 1, ∀ r, K * φ t < r →
      ∃ᶠ u in 𝓝[>] t, (u - t)⁻¹ * (φ u - φ t) < r := by
    intro t ht r hr
    let ε := (r - K * φ t) / (K + 1)
    have hK : 0 ≤ K := mul_nonneg h.one_nonneg (norm_nonneg _)
    have hε : 0 < ε := div_pos (sub_pos.mpr hr) (by linarith)
    have hr' : K * (φ t + ε) < r := by
      have heq : ε * (K + 1) = r - K * φ t :=
        (div_mul_cancel₀ _ (by linarith))
      nlinarith
    obtain ⟨δ, hδ, hclose⟩ :=
      Metric.continuousOn_iff.mp hφ t ⟨ht.1, ht.2.le⟩ ε hε
    have hnear : Ioo t (min 1 (t + δ)) ∈ 𝓝[>] t :=
      Ioo_mem_nhdsGT (lt_min ht.2 (by linarith))
    apply Filter.Eventually.frequently
    filter_upwards [hnear] with u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨ht.1.trans hu.1.le, (lt_min_iff.mp hu.2).1.le⟩
    have hseg : segment ℝ (T t) (T u) ⊆ D := hD.segment_subset (hmaps ⟨ht.1, ht.2.le⟩)
      (hmaps hu')
    have hbound : ∀ z ∈ segment ℝ (T t) (T u), L₀ + L₁ * ‖g z‖ ≤ φ t + ε := by
      rw [← image_segment ℝ T t u, segment_eq_Icc hu.1.le]
      rintro _ ⟨v, hv, rfl⟩
      have hv' : v ∈ Icc (0 : ℝ) 1 := ⟨ht.1.trans hv.1, hv.2.trans hu'.2⟩
      have hvδ : dist v t < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hv.1)]
        have := (lt_min_iff.mp hu.2).2
        linarith [hv.2]
      have hvalue := hclose v hv' hvδ
      rw [Real.dist_eq] at hvalue
      change φ v ≤ φ t + ε
      linarith [(abs_lt.mp hvalue).2]
    have hnorm := h.norm_sub_le (hmaps ⟨ht.1, ht.2.le⟩) (hmaps hu') hseg hbound
    have hdist : ‖T u - T t‖ = (u - t) * ‖y - x‖ := by
      have hd : T u - T t = (u - t) • (y - x) := by
        simp only [T, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
          add_sub_add_right_eq_sub, sub_smul]
      rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hu.1)]
    have hφsub : φ u - φ t ≤ K * (φ t + ε) * (u - t) := calc
      _ = L₁ * (‖g (T u)‖ - ‖g (T t)‖) := by dsimp [φ]; ring
      _ ≤ L₁ * ‖g (T u) - g (T t)‖ :=
        mul_le_mul_of_nonneg_left (norm_sub_norm_le _ _) h.one_nonneg
      _ ≤ _ := by
        rw [hdist] at hnorm
        calc
          _ ≤ L₁ * ((φ t + ε) * ((u - t) * ‖y - x‖)) :=
            mul_le_mul_of_nonneg_left hnorm h.one_nonneg
          _ = _ := by dsimp [K]; ring
    rw [← div_eq_inv_mul]
    exact ((div_le_iff₀ (sub_pos.mpr hu.1)).mpr hφsub).trans_lt hr'
  have hgr := le_gronwallBound_of_liminf_deriv_right_le hφ hdiff (δ := φ 0) (K := K) (ε := 0)
    le_rfl (fun t _ => by simp) 1 (by simp)
  simpa [gronwallBound_ε0, φ, T, K] using hgr

/-- Localization on a convex subset of a ball in the working norm. -/
theorem local_norm_sub_le (h : SymmetricSmoothOn D g L₀ L₁) (hD : Convex ℝ D)
    {s : E} (hs : s ∈ D) (R : ℝ) {x y : E}
    (hx : x ∈ D ∩ Metric.closedBall s R) (hy : y ∈ D ∩ Metric.closedBall s R) :
    ‖g y - g x‖ ≤ (L₀ + L₁ * ‖g s‖) * Real.exp (L₁ * R) * ‖y - x‖ := by
  apply h.norm_sub_le hx.1 hy.1 (hD.segment_subset hx.1 hy.1)
  intro z hz
  have hzD := hD.segment_subset hx.1 hy.1 hz
  have hzR := (convex_closedBall s R).segment_subset hx.2 hy.2 hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hzR
  exact (h.coefficient_le_exp hD hs hzD).trans <|
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hzR h.one_nonneg))
      (add_nonneg h.zero_nonneg (mul_nonneg h.one_nonneg (norm_nonneg _)))

/-- Exponential control of the secant with the coefficient evaluated at its start. -/
theorem norm_sub_le_exp (h : SymmetricSmoothOn D g L₀ L₁) (hD : Convex ℝ D)
    {x y : E} (hx : x ∈ D) (hy : y ∈ D) :
    ‖g y - g x‖ ≤ (L₀ + L₁ * ‖g x‖) * Real.exp (L₁ * ‖y - x‖) * ‖y - x‖ :=
  h.local_norm_sub_le hD hx ‖y - x‖ ⟨hx, Metric.mem_closedBall_self (norm_nonneg _)⟩
    ⟨hy, by rw [Metric.mem_closedBall, dist_eq_norm]⟩

/-- A known classical Lipschitz bound yields a polynomial secant estimate. -/
theorem norm_sub_le_of_classical (h : SymmetricSmoothOn D g L₀ L₁) (hD : Convex ℝ D)
    {L : ℝ} (hL : 0 ≤ L) (hLip : ∀ x ∈ D, ∀ y ∈ D, ‖g y - g x‖ ≤ L * ‖y - x‖)
    {x y : E} (hx : x ∈ D) (hy : y ∈ D) :
    ‖g y - g x‖ ≤ (L₀ + L₁ * ‖g x‖ + L₁ * L * ‖y - x‖) * ‖y - x‖ := by
  apply h.norm_sub_le hx hy (hD.segment_subset hx hy)
  intro z hz
  have hzD := hD.segment_subset hx hy hz
  have hdist := (convex_closedBall x ‖y - x‖).segment_subset
    (Metric.mem_closedBall_self (norm_nonneg _))
    (by rw [Metric.mem_closedBall, dist_eq_norm]) hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hdist
  have hnorm : ‖g z‖ - ‖g x‖ ≤ L * ‖y - x‖ :=
    (norm_sub_norm_le _ _).trans ((hLip x hx z hzD).trans
      (mul_le_mul_of_nonneg_left hdist hL))
  linarith only [mul_le_mul_of_nonneg_left hnorm h.one_nonneg]

end SymmetricSmoothOn

section Gradient

open scoped RealInnerProductSpace Interval

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {D : Set H} {f : H → ℝ} {g : H → H}

/-- Rescaling an unmodified component of the recursion preserves convexity and
cancels the weight in the gradient, while scaling both smoothness parameters. -/
theorem SymmetricSmoothOn.rescale_component {L₀ L₁ : ℝ}
    (h : SymmetricSmoothOn D g L₀ L₁) (hf : ConvexOn ℝ D f)
    (hgrad : ∀ x ∈ D, HasGradientWithinAt f (g x) D x)
    {c : H} (hc : c ∈ D) {α : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1) :
    let T := AffineMap.homothety c α
    let F := fun x => α⁻¹ * f (T x)
    ConvexOn ℝ D F ∧ (∀ x ∈ D, HasGradientWithinAt F (g (T x)) D x) ∧
      SymmetricSmoothOn D (g ∘ T) (α * L₀) (α * L₁) := by
  dsimp only
  let T : H →ᵃ[ℝ] H := AffineMap.homothety c α
  have hmaps : MapsTo T D D := by
    intro x hx
    change AffineMap.homothety c α x ∈ D
    rw [AffineMap.homothety_eq_lineMap]
    exact hf.1.mapsTo_lineMap hc hx ⟨hα.le, hα₁⟩
  refine ⟨?_, ?_, h.homothety hf.1 hc hα.le hα₁⟩
  · exact ((hf.comp_affineMap T).subset hmaps hf.1).smul (inv_nonneg.mpr hα.le)
  · intro x hx
    have hT : HasFDerivAt T (α • ContinuousLinearMap.id ℝ H) x := by
      simpa only [T, AffineMap.coe_homothety, vsub_eq_sub, vadd_eq_add, Pi.add_apply,
        Pi.smul_apply, Pi.sub_apply, ContinuousLinearMap.id_apply] using
        ((((ContinuousLinearMap.id ℝ H).hasFDerivAt (x := x)).sub_const c).const_smul α).add_const c
    rw [hasGradientWithinAt_iff_hasFDerivWithinAt]
    have hderiv := ((hgrad _ (hmaps hx)).hasFDerivWithinAt.comp x
      hT.hasFDerivWithinAt hmaps).const_smul α⁻¹
    have hcancel : α⁻¹ • ((InnerProductSpace.toDual ℝ H (g (T x))).comp
        (α • ContinuousLinearMap.id ℝ H)) = InnerProductSpace.toDual ℝ H (g (T x)) := by
      ext v
      simp [hα.ne']
    rw [hcancel] at hderiv
    exact hderiv

/-- The linearization error integrates the change of gradient along the segment. -/
private theorem abs_linearization_error_le (hD : Convex ℝ D) (hg : ContinuousOn g D)
    (hf : ∀ z ∈ D, HasGradientWithinAt f (g z) D z)
    {x y : H} (hx : x ∈ D) (hy : y ∈ D) {A B : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖g (AffineMap.lineMap x y t) - g x‖ ≤ A * t + B * t ^ 2) :
    |f y - f x - ⟪g x, y - x⟫| ≤ (A / 2 + B / 3) * ‖y - x‖ := by
  let T : ℝ →ᵃ[ℝ] H := AffineMap.lineMap x y
  let F : ℝ → ℝ := fun t => f (T t) - t * ⟪g x, y - x⟫
  let F' : ℝ → ℝ := fun t => ⟪g (T t) - g x, y - x⟫
  have hmaps : MapsTo T (Icc 0 1) D := hD.mapsTo_lineMap hx hy
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt F (F' t) (Icc 0 1) t := by
    intro t ht
    have hline : HasDerivWithinAt (f ∘ ⇑T) ⟪g (T t), y - x⟫ (Icc 0 1) t := by
      simpa only [InnerProductSpace.toDual_apply_apply] using
        (hf _ (hmaps ht)).hasFDerivWithinAt.comp_hasDerivWithinAt t
          AffineMap.hasDerivWithinAt_lineMap hmaps
    change HasDerivWithinAt ((f ∘ ⇑T) - fun u => u * ⟪g x, y - x⟫) (F' t) (Icc 0 1) t
    simpa only [F', inner_sub_left, id_eq, one_mul] using
      hline.sub (((hasDerivAt_id t).mul_const ⟪g x, y - x⟫).hasDerivWithinAt
        (s := Icc 0 1))
  have hT : Continuous T := by
    change Continuous (fun t : ℝ => AffineMap.lineMap x y t)
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    fun_prop
  have hF' : ContinuousOn F' (Icc 0 1) :=
    ((hg.comp hT.continuousOn hmaps).sub continuousOn_const).inner continuousOn_const
  have hFTC : (∫ t in (0 : ℝ)..1, F' t) = F 1 - F 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    · exact fun t ht => (hderiv t ht).continuousWithinAt
    · exact fun t ht => (hderiv t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
    · exact hF'.intervalIntegrable_of_Icc zero_le_one
  have heq : F 1 - F 0 = f y - f x - ⟪g x, y - x⟫ := by
    simp [F, T]
    ring
  rw [← heq, ← hFTC, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, (A * t + B * t ^ 2) * ‖y - x‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      · apply Filter.Eventually.of_forall
        intro t ht
        calc
          ‖F' t‖ ≤ ‖g (T t) - g x‖ * ‖y - x‖ := abs_real_inner_le_norm _ _
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (hbound t (Ioc_subset_Icc_self ht)) (norm_nonneg _)
      · exact (show Continuous (fun t : ℝ => (A * t + B * t ^ 2) * ‖y - x‖) by
          fun_prop).intervalIntegrable 0 1
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_add,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_id, integral_pow]
      · norm_num
        left
        ring
      · exact (show Continuous (fun t : ℝ => A * t) by fun_prop).intervalIntegrable 0 1
      · exact (show Continuous (fun t : ℝ => B * t ^ 2) by fun_prop).intervalIntegrable 0 1

/-- The uniform quadratic model on the localized domain of variant A. -/
theorem SymmetricSmoothOn.local_abs_linearization_error_le {L₀ L₁ : ℝ}
    (h : SymmetricSmoothOn D g L₀ L₁) (hD : Convex ℝ D)
    (hf : ∀ z ∈ D, HasGradientWithinAt f (g z) D z)
    {s : H} (hs : s ∈ D) (R : ℝ) {x y : H}
    (hx : x ∈ D ∩ Metric.closedBall s R) (hy : y ∈ D ∩ Metric.closedBall s R) :
    |f y - f x - ⟪g x, y - x⟫| ≤
      ((L₀ + L₁ * ‖g s‖) * Real.exp (L₁ * R) / 2) * ‖y - x‖ ^ 2 := by
  let C := (L₀ + L₁ * ‖g s‖) * Real.exp (L₁ * R)
  have hK := hD.inter (convex_closedBall s R)
  have hmodel := abs_linearization_error_le hK (h.continuousOn.mono inter_subset_left)
    (fun z hz => (hf z hz.1).hasFDerivWithinAt.mono inter_subset_left) hx hy
    (A := C * ‖y - x‖) (B := 0) (by
      intro t ht
      let z := AffineMap.lineMap x y t
      have hz := hK.mapsTo_lineMap hx hy ht
      have hdist : ‖z - x‖ = t * ‖y - x‖ := by
        simp [z, AffineMap.lineMap_apply, norm_smul_of_nonneg ht.1]
      change ‖g z - g x‖ ≤ C * ‖y - x‖ * t + 0 * t ^ 2
      calc
        _ ≤ C * ‖z - x‖ := h.local_norm_sub_le hD hs R hx hz
        _ = _ := by rw [hdist]; ring)
  exact hmodel.trans_eq (by change _ = (C / 2) * ‖y - x‖ ^ 2; ring)

/-- The exponential quadratic model with its coefficient evaluated at the start. -/
theorem SymmetricSmoothOn.abs_linearization_error_le_exp {L₀ L₁ : ℝ}
    (h : SymmetricSmoothOn D g L₀ L₁) (hD : Convex ℝ D)
    (hf : ∀ z ∈ D, HasGradientWithinAt f (g z) D z) {x y : H} (hx : x ∈ D) (hy : y ∈ D) :
    |f y - f x - ⟪g x, y - x⟫| ≤
      ((L₀ + L₁ * ‖g x‖) * Real.exp (L₁ * ‖y - x‖) / 2) * ‖y - x‖ ^ 2 :=
  h.local_abs_linearization_error_le hD hf hx ‖y - x‖
    ⟨hx, Metric.mem_closedBall_self (norm_nonneg _)⟩
    ⟨hy, by rw [Metric.mem_closedBall, dist_eq_norm]⟩

/-- When a classical Lipschitz constant is known, the cubic model has no
exponential factor. -/
theorem SymmetricSmoothOn.abs_linearization_error_le_of_classical {L₀ L₁ L : ℝ}
    (h : SymmetricSmoothOn D g L₀ L₁) (hD : Convex ℝ D)
    (hf : ∀ z ∈ D, HasGradientWithinAt f (g z) D z)
    (hL : 0 ≤ L) (hLip : ∀ x ∈ D, ∀ y ∈ D, ‖g y - g x‖ ≤ L * ‖y - x‖)
    {x y : H} (hx : x ∈ D) (hy : y ∈ D) :
    |f y - f x - ⟪g x, y - x⟫| ≤
      (L₀ + L₁ * ‖g x‖) / 2 * ‖y - x‖ ^ 2 + L₁ * L / 3 * ‖y - x‖ ^ 3 := by
  let A := (L₀ + L₁ * ‖g x‖) * ‖y - x‖
  let B := L₁ * L * ‖y - x‖ ^ 2
  have hmodel := abs_linearization_error_le hD h.continuousOn hf hx hy (A := A) (B := B) (by
    intro t ht
    let z := AffineMap.lineMap x y t
    have hz : z ∈ D := hD.mapsTo_lineMap hx hy ht
    have hdist : ‖z - x‖ = t * ‖y - x‖ := by
      simp [z, AffineMap.lineMap_apply, norm_smul_of_nonneg ht.1]
    calc
      _ ≤ (L₀ + L₁ * ‖g x‖ + L₁ * L * ‖z - x‖) * ‖z - x‖ :=
        h.norm_sub_le_of_classical hD hL hLip hx hz
      _ = A * t + B * t ^ 2 := by rw [hdist]; dsimp [A, B]; ring)
  exact hmodel.trans_eq (by dsimp [A, B]; ring)

end Gradient

end LeanLab.Sliding
