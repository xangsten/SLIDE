module

public import LeanLab.Variants.Accelerated

set_option linter.style.header false

/-!
# Certificates and obstructions for dynamic multilevel sliding
-/

@[expose] public section

namespace LeanLab.Sliding.Multilevel

open scoped BigOperators RealInnerProductSpace

noncomputable section

section Certificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The requested child certificate closes the parent potential for any number
of child centers. The center coefficients can remain fixed across accepted steps. -/
theorem accepted_step {ι : Type*} [Fintype ι] {p₁ p₂ : E → ℝ} {Q : E → E}
    {y u v w g : E} {A a τ : ℝ} {c : ι → ℝ} {q q' : ι → E}
    (hA : 0 ≤ A) (ha : 0 < a) (hcheck : τ * a ^ 2 / (A + a) ≤ 1 / 2)
    (hsupportY : let x := TwoLevel.mix (a / (A + a)) y u
      p₁ x + ⟪g, y - x⟫ ≤ p₁ y)
    (hsupportW : let x := TwoLevel.mix (a / (A + a)) y u
      p₁ x + ⟪g, w - x⟫ ≤ p₁ w)
    (hupper : let θ := a / (A + a); let x := TwoLevel.mix θ y u
      let y' := TwoLevel.mix θ y v
      p₁ y' ≤ p₁ x + ⟪g, y' - x⟫ + τ / 2 * ‖y' - x‖ ^ 2)
    (hconv : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      p₂ (TwoLevel.mix t y v) ≤ (1 - t) * p₂ y + t * p₂ v)
    (hchild : a * (TwoLevel.innerGap ⟨1 / a, u, g⟩ Q w v + (p₂ v - p₂ w)) ≤
      (∑ i, c i * ‖q i - w‖ ^ 2) / 2 - (∑ i, c i * ‖q' i - w‖ ^ 2) / 2) :
    let p := fun z => p₁ z + p₂ z
    (A + a) * gap p Q (TwoLevel.mix (a / (A + a)) y v) w +
      ‖v - w‖ ^ 2 / 2 + (∑ i, c i * ‖q' i - w‖ ^ 2) / 2 + ‖v - u‖ ^ 2 / 4 ≤
      A * gap p Q y w + ‖u - w‖ ^ 2 / 2 + (∑ i, c i * ‖q i - w‖ ^ 2) / 2 := by
  let B := A + a
  let θ := a / B
  have hB : 0 < B := by dsimp [B]; linarith
  have hθ : 0 ≤ θ := (div_pos ha hB).le
  have hθ' : θ ≤ 1 := (div_le_one hB).mpr (by dsimp [B]; linarith)
  have hBa : B * θ = a := mul_div_cancel₀ a hB.ne'
  have hBA : B * (1 - θ) = A := by rw [mul_sub, mul_one, hBa]; dsimp [B]; ring
  have hp₂ := mul_le_mul_of_nonneg_left (hconv θ hθ hθ') hB.le
  rw [mul_add, ← mul_assoc B (1 - θ), hBA, ← mul_assoc B θ, hBa] at hp₂
  have hp₁ := TwoLevel.Accelerated.weighted_model_gap (Q := Q) hA ha hsupportY hsupportW hupper
  change B * gap p₁ Q (TwoLevel.mix θ y v) w - A * gap p₁ Q y w ≤ _ at hp₁
  have hmodel :
      a * TwoLevel.innerGap ⟨1 / a, u, g⟩ Q w v =
        a * ⟪g + Q w, v - w⟫ +
          (‖v - u‖ ^ 2 - ‖u - w‖ ^ 2 + ‖v - w‖ ^ 2) / 2 := by
    unfold TwoLevel.innerGap TwoLevel.Quadratic.value model
    dsimp only
    simp only [inner_add_left, inner_sub_right, norm_sub_rev w u]
    field_simp
    ring
  have hslack := mul_le_mul_of_nonneg_right hcheck (sq_nonneg ‖v - u‖)
  change τ * a ^ 2 / B * ‖v - u‖ ^ 2 ≤ _ at hslack
  rw [mul_add, hmodel] at hchild
  change B * gap (fun z => p₁ z + p₂ z) Q (TwoLevel.mix θ y v) w +
    ‖v - w‖ ^ 2 / 2 + (∑ i, c i * ‖q' i - w‖ ^ 2) / 2 + ‖v - u‖ ^ 2 / 4 ≤
    A * gap (fun z => p₁ z + p₂ z) Q y w + ‖u - w‖ ^ 2 / 2 +
      (∑ i, c i * ‖q i - w‖ ^ 2) / 2
  unfold gap at hp₁ ⊢
  linarith only [hp₁, hp₂, hchild, hslack, show B = A + a by rfl]

/-- Numerical telescope for fixed potentials and nonnegative slack. -/
theorem telescope_with_slack {P D : ℕ → ℝ}
    (hstep : ∀ k, P (k + 1) + D k ≤ P k) (n : ℕ) :
    P n + ∑ k ∈ Finset.range n, D k ≤ P 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    linarith [hstep k]

/-- The same weighted bound can be applied to every comparator once the
accumulated weight reaches the desired accuracy. -/
theorem normalized_gap {A ε G D C R : ℝ}
    (hA : 0 < A) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hweight : C ≤ ε * A) (hpotential : A * G + D ≤ C * R) :
    G ≤ ε * R := by
  apply (mul_le_mul_iff_left₀ hA).mp
  have h := mul_le_mul_of_nonneg_right hweight hR
  linarith only [hpotential, hD, h]

/-- A frozen tangent admits an exact block telescope once its Bregman terms
are carried in the potential. The reference is fixed for the whole block. -/
theorem frozen_block {P D A error : ℕ → ℝ} {comparatorError : ℝ}
    (hstep : ∀ k, P (k + 1) + D k ≤ P k +
      (A (k + 1) * error (k + 1) - A k * error k) -
      (A (k + 1) - A k) * comparatorError) (n : ℕ) :
    P n + ∑ k ∈ Finset.range n, D k ≤ P 0 +
      (A n * error n - A 0 * error 0) - (A n - A 0) * comparatorError := by
  let corrected := fun k => P k - A k * error k + A k * comparatorError
  have hcorrected (k : ℕ) : corrected (k + 1) + D k ≤ corrected k := by
    dsimp [corrected]
    linarith only [hstep k]
  have h := telescope_with_slack hcorrected n
  dsimp [corrected] at h
  linarith only [h]

end Certificate

section ProximalScaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A relative proximal residual at the extrapolated point closes a one-center
potential for the smooth sum, with proximal scale a² / (A + a). -/
theorem scaled_proximal_step {p₁ p₂ : E → ℝ} {y u u' v w g h : E}
    {A a η τ e slack : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (hη : 0 < η)
    (hscale : a ^ 2 = (A + a) * η)
    (hsupportY : let x := TwoLevel.mix (a / (A + a)) y u
      p₁ x + ⟪g, y - x⟫ ≤ p₁ y)
    (hsupportW : let x := TwoLevel.mix (a / (A + a)) y u
      p₁ x + ⟪g, w - x⟫ ≤ p₁ w)
    (hupper : let x := TwoLevel.mix (a / (A + a)) y u
      p₁ v ≤ p₁ x + ⟪g, v - x⟫ + τ / 2 * ‖v - x‖ ^ 2)
    (hcutY : p₂ v - p₂ y ≤ ⟪h, v - y⟫ + e)
    (hcutW : p₂ v - p₂ w ≤ ⟪h, v - w⟫ + e)
    (hproject : ⟪(u - a • (g + h)) - u', w - u'⟫ ≤ 0)
    (hresidual : let x := TwoLevel.mix (a / (A + a)) y u
      ‖(v - x) + η • (g + h)‖ ^ 2 + 2 * η * (e + slack) ≤ (1 - η * τ) * ‖v - x‖ ^ 2) :
    (A + a) * (p₁ v + p₂ v - (p₁ w + p₂ w)) + ‖u' - w‖ ^ 2 / 2 + (A + a) * slack ≤
      A * (p₁ y + p₂ y - (p₁ w + p₂ w)) + ‖u - w‖ ^ 2 / 2 := by
  let B := A + a
  let x := TwoLevel.mix (a / B) y u
  have hB : 0 < B := by dsimp [B]; linarith
  have hx : B • (v - x) + a • (u - w) = A • (v - y) + a • (v - w) := by
    have ht : B * (a / B) = a := mul_div_cancel₀ a hB.ne'
    have hs : B * (1 - a / B) = A := by rw [mul_sub, mul_one, ht]; dsimp [B]; ring
    dsimp [x, TwoLevel.mix]
    rw [smul_sub, smul_add, smul_smul, smul_smul, ht, hs]
    dsimp [B]
    module
  have h₁Y : p₁ v - p₁ y ≤ ⟪g, v - y⟫ + τ / 2 * ‖v - x‖ ^ 2 := by
    change p₁ x + ⟪g, y - x⟫ ≤ p₁ y at hsupportY
    change p₁ v ≤ p₁ x + ⟪g, v - x⟫ + τ / 2 * ‖v - x‖ ^ 2 at hupper
    simp only [inner_sub_right] at hsupportY hupper ⊢
    linarith only [hsupportY, hupper]
  have h₁W : p₁ v - p₁ w ≤ ⟪g, v - w⟫ + τ / 2 * ‖v - x‖ ^ 2 := by
    change p₁ x + ⟪g, w - x⟫ ≤ p₁ w at hsupportW
    change p₁ v ≤ p₁ x + ⟪g, v - x⟫ + τ / 2 * ‖v - x‖ ^ 2 at hupper
    simp only [inner_sub_right] at hsupportW hupper ⊢
    linarith only [hsupportW, hupper]
  have hlin := congrArg (fun z : E => ⟪g + h, z⟫) hx
  simp only [inner_add_right, real_inner_smul_right] at hlin
  have hgap :
      B * (p₁ v + p₂ v - (p₁ w + p₂ w)) - A * (p₁ y + p₂ y - (p₁ w + p₂ w)) ≤
      a * ⟪g + h, u - w⟫ + B * (⟪g + h, v - x⟫ + τ / 2 * ‖v - x‖ ^ 2 + e) := by
    have hY := mul_le_mul_of_nonneg_left (add_le_add h₁Y hcutY) hA
    have hW := mul_le_mul_of_nonneg_left (add_le_add h₁W hcutW) ha.le
    simp only [inner_add_left] at hlin ⊢
    linarith only [hY, hW, hlin, show B = A + a by rfl]
  have hproj := projection_bound hproject
  have hsplit : u - a • (g + h) - w = (u - w) - a • (g + h) := by abel
  have hnorm : ‖u - a • (g + h) - w‖ ^ 2 =
      ‖u - w‖ ^ 2 - 2 * (a * ⟪g + h, u - w⟫) + a ^ 2 * ‖g + h‖ ^ 2 := by
    rw [hsplit, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ha, mul_pow, real_inner_comm (u - w) (g + h)]
  rw [hnorm] at hproj
  change ‖(v - x) + η • (g + h)‖ ^ 2 + 2 * η * (e + slack) ≤
    (1 - η * τ) * ‖v - x‖ ^ 2 at hresidual
  have hcomm : ⟪v - x, g + h⟫ = ⟪g + h, v - x⟫ := real_inner_comm _ _
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hη, mul_pow, hcomm] at hresidual
  have herror : ⟪g + h, v - x⟫ + τ / 2 * ‖v - x‖ ^ 2 + e +
      η * ‖g + h‖ ^ 2 / 2 + slack ≤ 0 := by
    apply nonpos_of_mul_nonpos_right _ (show 0 < 2 * η by positivity)
    linarith only [hresidual]
  have herror' := mul_nonpos_of_nonneg_of_nonpos hB.le herror
  change B * (p₁ v + p₂ v - (p₁ w + p₂ w)) + ‖u' - w‖ ^ 2 / 2 + B * slack ≤
    A * (p₁ y + p₂ y - (p₁ w + p₂ w)) + ‖u - w‖ ^ 2 / 2
  change a ^ 2 = B * η at hscale
  rw [hscale] at hproj
  linarith only [hgap, hproj, herror', sq_nonneg ‖u - a • (g + h) - u'‖]

/-- Fixed proximal scale makes the square root of total weight grow linearly. -/
theorem sqrt_weight_progress {A a η : ℝ} (hA : 0 ≤ A) (ha : 0 < a) (hη : 0 < η)
    (hscale : a ^ 2 = η * (A + a)) :
    Real.sqrt A + Real.sqrt η / 2 ≤ Real.sqrt (A + a) := by
  have hB : 0 < A + a := by linarith
  have hroot := Real.sqrt_le_sqrt (show A ≤ A + a by linarith)
  have hfact : a = Real.sqrt η * Real.sqrt (A + a) := by
    rw [← Real.sqrt_mul hη.le, ← hscale, Real.sqrt_sq ha.le]
  have hmul : (Real.sqrt (A + a) - Real.sqrt A) * Real.sqrt (A + a) * 2 ≥ a := by
    have heq : (Real.sqrt (A + a) - Real.sqrt A) *
        (Real.sqrt (A + a) + Real.sqrt A) = a := by
      nlinarith only [Real.sq_sqrt hA, Real.sq_sqrt hB.le]
    have hle := mul_le_mul_of_nonneg_left (show Real.sqrt (A + a) + Real.sqrt A ≤
        Real.sqrt (A + a) * 2 by linarith) (sub_nonneg.mpr hroot)
    linarith only [hle, heq]
  have hbound : Real.sqrt η ≤ (Real.sqrt (A + a) - Real.sqrt A) * 2 := by
    apply (mul_le_mul_iff_left₀ (Real.sqrt_pos.mpr hB)).mp
    linarith only [hmul, hfact]
  linarith only [hbound]

/-- Quadratic growth of the accumulated weight under a fixed proximal scale. -/
theorem sqrt_weight_iterations {A a : ℕ → ℝ} {η : ℝ} (hη : 0 < η)
    (hA : ∀ k, 0 ≤ A k) (ha : ∀ k, 0 < a k)
    (hnext : ∀ k, A (k + 1) = A k + a k) (hscale : ∀ k, a k ^ 2 = η * A (k + 1))
    (n : ℕ) : (n : ℝ) * (Real.sqrt η / 2) ≤ Real.sqrt (A n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hs := hscale k
    rw [hnext] at hs
    have hp := sqrt_weight_progress (hA k) (ha k) hη hs
    rw [← hnext] at hp
    push_cast
    linarith only [ih, hp]

end ProximalScaling

section Restarts

/-- A cap on each accepted weight gives a lower bound on a charged square-root
restart cost, even for very uneven weights. Rejected trials only add cost. -/
theorem restart_cost {ι : Type*} {s : Finset ι} {a : ι → ℝ} {L H T : ℝ}
    (hL : 0 ≤ L) (hH : 0 < H)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hcap : ∀ i ∈ s, a i ≤ H)
    (hmass : T ≤ ∑ i ∈ s, a i) :
    Real.sqrt L * T / Real.sqrt H ≤ ∑ i ∈ s, Real.sqrt (L * a i) := by
  have hsum := Finset.sum_le_sum (s := s) fun i hi => by
    have hroot := Real.sqrt_le_sqrt (hcap i hi)
    calc
      Real.sqrt L * a i = Real.sqrt L * (Real.sqrt (a i) * Real.sqrt (a i)) := by
        rw [Real.mul_self_sqrt (ha i hi)]
      _ ≤ Real.sqrt L * (Real.sqrt (a i) * Real.sqrt H) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _)
      _ = Real.sqrt (L * a i) * Real.sqrt H := by rw [Real.sqrt_mul hL]; ring
  rw [← Finset.mul_sum, ← Finset.sum_mul] at hsum
  apply (div_le_iff₀ (Real.sqrt_pos.2 hH)).2
  exact (mul_le_mul_of_nonneg_left hmass (Real.sqrt_nonneg _)).trans hsum

/-- Exact secant of a convex quadratic for every distinct pair of endpoints. -/
theorem quadratic_secant {L x y : ℝ} (hL : 0 ≤ L) (hxy : y ≠ x) :
    |L * y - L * x| / |y - x| = L := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hL,
    mul_div_cancel_right₀ L (abs_ne_zero.mpr (sub_ne_zero.mpr hxy))]

/-- The quadratic parent's accepted-step test bounds the maximum weight even
when the last step overshoots the required total weight. -/
theorem quadratic_restart_cost {ι : Type*} {s : Finset ι} {a B : ι → ℝ}
    {L₁ L₂ T U : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 ≤ L₂)
    (hU : 0 < U)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hB : ∀ i ∈ s, B i ≤ U)
    (hcheck : ∀ i ∈ s, L₁ * a i ^ 2 ≤ B i / 2)
    (hmass : T ≤ ∑ i ∈ s, a i) :
    Real.sqrt L₂ * T / Real.sqrt (Real.sqrt (U / (2 * L₁))) ≤
      ∑ i ∈ s, Real.sqrt (L₂ * a i) := by
  refine restart_cost hL₂ (Real.sqrt_pos.2 (by positivity)) ha ?_ hmass
  intro i hi
  have h : a i ^ 2 ≤ U / (2 * L₁) := by
    apply (le_div_iff₀ (by positivity)).2
    linarith only [hcheck i hi, hB i hi]
  simpa [Real.sqrt_sq (ha i hi)] using Real.sqrt_le_sqrt h

/-- A first crossing of the target does not require an extra overshoot
assumption for a quadratic parent when its curvature times the target is large. -/
theorem quadratic_first_crossing {L A a T : ℝ} (hA : A ≤ T)
    (hT : 0 < T) (hLT : 1 ≤ L * T) (hcheck : L * a ^ 2 ≤ (A + a) / 2) :
    A + a ≤ 2 * T := by
  by_contra! h
  have hlarge : T < a := by linarith
  have hLa : 0 < L := by
    by_contra! hL
    nlinarith only [hLT, mul_nonpos_of_nonpos_of_nonneg hL hT.le]
  have hprod := mul_pos hLa (sub_pos.mpr hlarge)
  have hmul := mul_pos (show 0 < a by linarith) (show 0 < L * a - 1 by linarith only [hprod, hLT])
  nlinarith only [hcheck, hA, hlarge, hmul]

end Restarts

/-- Increasing only a component that failed a secant check keeps each
estimate within a factor of two of its own valid Lipschitz bound. -/
theorem doubling_on_failure {ι : Type*} {estimate L : ι → ℝ} {floor : ℝ} {i : ι}
    [DecidableEq ι] (h : ∀ j, estimate j ≤ max floor (2 * L j))
    (hfail : estimate i < L i) :
    ∀ j, Function.update estimate i (2 * estimate i) j ≤ max floor (2 * L j) := by
  intro j
  by_cases hj : j = i
  · subst j
    rw [Function.update_self]
    exact (by linarith only [hfail] : 2 * estimate i ≤ 2 * L i).trans (le_max_right _ _)
  · simpa [Function.update_of_ne hj] using h j

section Scalar

/-- On the full line, two fixed-mass center potentials are ordered exactly when
their first moments agree and the second moment does not increase. -/
theorem center_potential_le_iff {c d q r q' r' : ℝ} :
    (∀ w : ℝ, c * (q' - w)^2 + d * (r' - w)^2 ≤
      c * (q - w)^2 + d * (r - w)^2) ↔
      c * q' + d * r' = c * q + d * r ∧ c * q'^2 + d * r'^2 ≤ c * q^2 + d * r^2 := by
  let m := c * q' + d * r' - (c * q + d * r)
  let S := c * q'^2 + d * r'^2 - (c * q^2 + d * r^2)
  have heq (w : ℝ) : c * (q' - w)^2 + d * (r' - w)^2 -
      (c * (q - w)^2 + d * (r - w)^2) = S - 2 * m * w := by dsimp [m, S]; ring
  constructor
  · intro h
    have hs := h 0
    simp only [sub_zero] at hs
    refine ⟨?_, hs⟩
    by_contra hne
    have hm : m ≠ 0 := sub_ne_zero.mpr hne
    have ht : S - 2 * m * ((S - 1) / (2 * m)) = 1 := by field_simp; ring
    linarith only [h ((S - 1) / (2 * m)), heq ((S - 1) / (2 * m)), ht]
  · rintro ⟨hm, hs⟩ w
    have hzero : m = 0 := sub_eq_zero.mpr hm
    have hnonpos : S ≤ 0 := sub_nonpos.mpr hs
    linarith only [heq w, hnonpos, show 2 * m * w = 0 by rw [hzero]; ring]

/-- A zero-weight rejection cannot move synchronized centers in a fixed
potential unless another term supplies slack. -/
theorem rejected_centers_fixed {c d q q' r' : ℝ} (hc : 0 < c) (hd : 0 < d)
    (h : ∀ w : ℝ, c * (q' - w)^2 + d * (r' - w)^2 ≤ (c + d) * (q - w)^2) :
    q' = q ∧ r' = q := by
  have hq := h q
  rw [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] at hq
  constructor
  · by_contra hne
    have hpos := mul_pos hc (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
    nlinarith only [hq, hpos, mul_nonneg hd.le (sq_nonneg (r' - q))]
  · by_contra hne
    have hpos := mul_pos hd (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
    nlinarith only [hq, hpos, mul_nonneg hc.le (sq_nonneg (q' - q))]

/-- A coefficient-only exchange with distinct centers violates pointwise descent. -/
theorem swap_coefficients {c d q r : ℝ} (hc : c ≠ d) (hq : q ≠ r) :
    ∃ w : ℝ, c * (q - w)^2 + d * (r - w)^2 <
      d * (q - w)^2 + c * (r - w)^2 := by
  by_contra! h
  have hm := ((center_potential_le_iff (c := c) (d := d)
    (q := q) (r := r) (q' := r) (r' := q)).mp (by simpa [add_comm] using h)).1
  have hz : (c - d) * (q - r) = 0 := by linarith only [hm, show
    (c - d) * (q - r) = (c * q + d * r) - (c * r + d * q) by ring]
  exact (mul_ne_zero (sub_ne_zero.mpr hc) (sub_ne_zero.mpr hq)) hz

/-- Moving both centers to their weighted mean spends only the variance and
leaves the coefficient of the comparator unchanged. -/
theorem recenter {c d q r w : ℝ} (h : c + d ≠ 0) :
    let z := (c * q + d * r) / (c + d)
    c * (q - w)^2 + d * (r - w)^2 =
      (c + d) * (z - w)^2 + c * d / (c + d) * (q - r)^2 := by
  dsimp
  field_simp
  ring

/-- Raw reuse of a certified endpoint fails after a parent tilt, even if
the successor centers may be chosen freely. The child is a convex quadratic. -/
theorem stale_child_endpoint {a L g c d : ℝ}
    (ha : 0 < a) (hL : 0 ≤ L) (hg : g ≠ 0) (hc : 0 < c) (hd : 0 < d) :
    ¬ ∃ q' r' : ℝ, ∀ w : ℝ,
      -(a * g) * w - (a * L) * w^2 / 2 ≤
        (c + d) * w^2 / 2 - (c * (q' - w)^2 + d * (r' - w)^2) / 2 := by
  rintro ⟨q', r', h⟩
  have h0 := h 0
  simp only [mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div,
    sub_zero, zero_sub] at h0
  have hq' : q' = 0 := by
    by_contra hn
    nlinarith only [h0, mul_pos hc (sq_pos_of_ne_zero hn), mul_nonneg hd.le (sq_nonneg r')]
  have hr' : r' = 0 := by
    by_contra hn
    nlinarith only [h0, mul_pos hd (sq_pos_of_ne_zero hn), mul_nonneg hc.le (sq_nonneg q')]
  subst q' r'
  have hp : 0 < 1 + a * L := by nlinarith [mul_nonneg ha.le hL]
  have hw := h (-(a * g) / (1 + a * L))
  have hrhs (w : ℝ) : (c + d) * w^2 / 2 -
      (c * (0 - w)^2 + d * (0 - w)^2) / 2 = 0 := by ring
  rw [hrhs] at hw
  have hcalc :
      -(a * g) * (-(a * g) / (1 + a * L)) -
          (a * L) * (-(a * g) / (1 + a * L))^2 / 2 =
        (a * g)^2 * (2 + a * L) / (2 * (1 + a * L)^2) := by
    field_simp
    ring
  rw [hcalc] at hw
  have hpos : 0 < (a * g)^2 * (2 + a * L) / (2 * (1 + a * L)^2) := by positivity
  exact (not_lt_of_ge hw) hpos

/-- For a quadratic, a frozen tangent leaves the difference of two
Bregman errors in the weighted increment. -/
theorem stale_quadratic_identity (L s A a y v w : ℝ) (hB : A + a ≠ 0) :
    let y' := (A * y + a * v) / (A + a)
    (A + a) * (L * y'^2 / 2 - L * w^2 / 2) -
      A * (L * y^2 / 2 - L * w^2 / 2) - a * (L * s) * (v - w) =
      L / 2 * ((A + a) * (y' - s)^2 - A * (y - s)^2 - a * (w - s)^2) := by
  dsimp
  field_simp
  ring

/-- Even zero motion of the trial center leaves a stale tangent error. -/
theorem stale_quadratic_zero_motion {L a : ℝ} (hL : 0 < L) (ha : 0 < a) :
    ¬ a * (L * (1 : ℝ)^2 / 2 - L * (0 : ℝ)^2 / 2) ≤
      a * (L * 0) * (1 - 0) + (1 - 1 : ℝ)^2 := by
  have hp := mul_pos ha hL
  nlinarith only [hp]

/-- The exact child certificate puts no unconditional bound on rejected
trial endpoints. For a parent of curvature one the secant rejects this trial. -/
theorem unbounded_rejected_trial (R : ℝ) :
    ∃ a : ℝ, R < a ∧ 1 / 2 < a ∧ ∀ w : ℝ,
      -a * (a - w) + (a ^ 2 - w ^ 2 + (a - w) ^ 2) / 2 = 0 := by
  refine ⟨max R 0 + 1, ?_, ?_, fun w => by ring⟩
  · linarith [le_max_left R 0]
  · linarith [le_max_right R 0]

/-- An unqueried tail can have unbounded curvature while every value and
slope on the observed prefix is unchanged. -/
theorem hidden_tail {R x K : ℝ} (hx : R < x) (hK : 0 ≤ K) :
    ∃ H : ℝ, 0 < H ∧
      (∀ t ≤ R, H / 2 * (max 0 (t - R))^2 = 0 ∧ H * max 0 (t - R) = 0) ∧
      K < (H * max 0 (x - R) - H * max 0 (R - R)) / (x - R) := by
  refine ⟨K + 1, by linarith, ?_, ?_⟩
  · intro t ht
    rw [max_eq_left (sub_nonpos.mpr ht)]
    simp
  · rw [sub_self R, max_self, mul_zero, sub_zero, max_eq_right (sub_nonneg.mpr hx.le),
        mul_div_cancel_right₀ _ (sub_ne_zero.mpr hx.ne')]
    linarith

/-- At the first exact proximal trial for exp(z) - z, a frozen scale
1 / (4 * G) can pass the secant test only with an exponentially large G. -/
theorem exponential_first_scale {R G : ℝ} (hG : 0 < G)
    (hcheck : let t := (Real.exp R - 1) / (4 * G)
      Real.exp R - Real.exp (R - t) ≤ G * t) :
    (Real.exp R - 1) / 4 < G := by
  let t := (Real.exp R - 1) / (4 * G)
  change Real.exp R - Real.exp (R - t) ≤ G * t at hcheck
  have ht : 4 * G * t = Real.exp R - 1 := by
    dsimp [t]
    field_simp
  have hexp : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact (div_le_iff₀ (Real.exp_pos 1)).2 (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hshort : t < 1 := by
    by_contra! hlarge
    have hR : R - t ≤ R + (-1) := by linarith
    have hle := Real.exp_le_exp.mpr hR
    rw [Real.exp_add] at hle
    have hhalf := mul_le_mul_of_nonneg_left hexp (Real.exp_pos R).le
    linarith only [hcheck, ht, hle, hhalf, Real.exp_pos R]
  have hpos := mul_pos (show 0 < 4 * G by positivity) (sub_pos.mpr hshort)
  linarith only [ht, hpos]

end Scalar

end

end LeanLab.Sliding.Multilevel

