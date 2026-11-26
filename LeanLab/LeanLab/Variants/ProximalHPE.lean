module

public import LeanLab.PathA.Guarantees
public import LeanLab.Variants.PlainStepSearch

set_option linter.style.header false

/-!
# Localized proximal HPE

Inner restart accuracy, regularization search, and the outer projected HPE bounds.
-/

@[expose] public section

namespace LeanLab.Sliding.ProximalHPE

open scoped BigOperators RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E]

/-- A correction close to the exact resolvent inherits a relative error bound
even when the exact displacement is zero. -/
theorem relative_residual {x z u e : E}
    (hprox : ‖u - z‖ ≤ ‖z - x‖ / 64)
    (hres : ‖e‖ ≤ 3 * ‖z - x‖ / 64) :
    ‖e‖ ≤ ‖u - x‖ / 21 := by
  have hsplit : z - x = (z - u) + (u - x) := by abel
  have htriangle := norm_add_le (z - u) (u - x)
  rw [← hsplit, norm_sub_rev z u] at htriangle
  linarith

/-- One certified restart contracts the distance to the exact local solution. -/
theorem half_distance {x z : E} {Γ gap : ℝ} (hΓ : 0 < Γ) {y : E}
    (hlower : Γ / 2 * ‖y - z‖ ^ 2 ≤ gap)
    (hupper : gap ≤ Γ / 8 * ‖x - z‖ ^ 2) :
    ‖y - z‖ ≤ ‖x - z‖ / 2 := by
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (by positivity)
  apply le_of_mul_le_mul_left _ hΓ
  nlinarith only [hlower, hupper]

/-- Repeated local passes preserve the exact initial distance as the prefactor. -/
theorem restarted_distance {z : E} (a : ℕ → E)
    (h : ∀ k, ‖a (k + 1) - z‖ ≤ ‖a k - z‖ / 2) (m : ℕ) :
    ‖a m - z‖ ≤ (1 / 2 : ℝ) ^ m * ‖a 0 - z‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      _ ≤ ‖a m - z‖ / 2 := h m
      _ ≤ ((1 / 2 : ℝ) ^ m * ‖a 0 - z‖) / 2 := by linarith only [ih]
      _ = _ := by rw [pow_succ]; ring

/-- The logarithmic restart count meets the scalar inner stopping rule. -/
theorem restart_budget {Γ L : ℝ} (hΓ : 0 < Γ) (hL : 0 < L) :
    (1 / 2 : ℝ) ^ ⌈Real.logb 2 (128 * L / Γ)⌉₊ ≤ Γ / (128 * L) := by
  let m := ⌈Real.logb 2 (128 * L / Γ)⌉₊
  have hbase : (1 : ℝ) < 2 := by norm_num
  have hpow := (Real.logb_le_iff_le_rpow hbase (by positivity : 0 < 128 * L / Γ)).mp
    (Nat.le_ceil (Real.logb 2 (128 * L / Γ)))
  rw [Real.rpow_natCast] at hpow
  change _ ≤ (2 : ℝ) ^ m at hpow
  change (1 / 2 : ℝ) ^ m ≤ _
  rw [div_pow, one_pow]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [one_mul, mul_comm ((2 : ℝ) ^ m) Γ] using (div_le_iff₀ hΓ).mp hpow

/-- The regularization of the k-th trial, with clipping at the floor. -/
noncomputable def trialParameter (floor initial : ℝ) (k : ℕ) : ℝ :=
  max floor (initial / 2 ^ k)

theorem trialParameter_succ {floor initial : ℝ} (hfloor : 0 ≤ floor) (k : ℕ) :
    trialParameter floor initial (k + 1) = max floor (trialParameter floor initial k / 2) := by
  unfold trialParameter
  rw [pow_succ, ← div_div, ← max_div_div_right (by norm_num : (0 : ℝ) ≤ 2),
    ← max_assoc, max_eq_left (show floor / 2 ≤ floor by linarith)]

/-- The first accepted trial exists within the logarithmic halving budget,
even if none of the computed points passes the length test. -/
theorem dyadic_search_stops {floor initial : ℝ} (hfloor : 0 < floor)
    (hstart : floor ≤ initial) (long : ℕ → Prop) :
    ∃ k ≤ ⌈Real.logb 2 (initial / floor)⌉₊,
      (long k ∨ trialParameter floor initial k = floor) ∧
      ∀ j < k, ¬long j ∧ floor < trialParameter floor initial j := by
  classical
  let N := ⌈Real.logb 2 (initial / floor)⌉₊
  have hbase : (1 : ℝ) < 2 := by norm_num
  have hpow := (Real.logb_le_iff_le_rpow hbase
    (div_pos (hfloor.trans_le hstart) hfloor)).mp (Nat.le_ceil (Real.logb 2 (initial / floor)))
  rw [Real.rpow_natCast] at hpow
  have hN : trialParameter floor initial N = floor := by
    apply max_eq_left
    apply (div_le_iff₀ (show 0 < (2 : ℝ) ^ N by positivity)).mpr
    have hh := (div_le_iff₀ hfloor).mp hpow
    change initial ≤ (2 : ℝ) ^ N * floor at hh
    simpa only [mul_comm ((2 : ℝ) ^ N) floor] using hh
  have hex : ∃ k, long k ∨ trialParameter floor initial k = floor := ⟨N, Or.inr hN⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (Or.inr hN), Nat.find_spec hex, ?_⟩
  intro j hj
  have hrejected := Nat.find_min hex hj
  exact ⟨fun h => hrejected (Or.inl h), lt_of_le_of_ne (le_max_left _ _)
    (fun h => hrejected (Or.inr h.symm))⟩

variable [InnerProductSpace ℝ E]

/-- The projection of the outer update preserves the HPE gap inequality. -/
theorem projected_step {C : Set E} (P : TwoLevel.Projection C)
    {x u v w : E} {τ gap : ℝ} (hw : w ∈ C) (hτ : 0 ≤ τ)
    (hgap : gap ≤ ⟪v, u - w⟫) :
    2 * τ * gap ≤ ‖x - w‖ ^ 2 - ‖P.apply (x - τ • v) - w‖ ^ 2
      - ‖u - x‖ ^ 2 + ‖u - x + τ • v‖ ^ 2 := by
  have hproj := projection_bound (P.normal (x - τ • v) hw)
  have hstep : (x - τ • v) - w = (x - w) - τ • v := by abel
  have hidentity :
      ‖x - w‖ ^ 2 - ‖(x - τ • v) - w‖ ^ 2 - ‖u - x‖ ^ 2
        + ‖u - x + τ • v‖ ^ 2 = 2 * τ * ⟪v, u - w⟫ := by
    rw [hstep, norm_sub_sq_real (x - w) (τ • v), norm_add_sq_real (u - x) (τ • v),
      real_inner_smul_right, real_inner_smul_right,
      real_inner_comm v (x - w), real_inner_comm v (u - x),
      inner_sub_right, inner_sub_right, inner_sub_right]
    ring
  have hweighted := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * τ by positivity)
  linarith [sq_nonneg ‖x - τ • v - P.apply (x - τ • v)‖]

/-- A point satisfying the normal inequality is the specified projection. -/
private theorem projection_eq_of_normal {D : Set E} (P : TwoLevel.Projection D)
    {a z : E} (hz : z ∈ D) (hn : ∀ w ∈ D, ⟪a - z, w - z⟫ ≤ 0) :
    P.apply a = z := by
  have h₁ := projection_bound (P.normal a hz)
  have h₂ := projection_bound (hn (P.apply a) (P.feasible a))
  rw [norm_sub_rev z (P.apply a)] at h₂
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith only [h₁, h₂]))

/-- An interior point of the local ball has the same normal inequalities
against the full convex set. -/
theorem normal_of_local_ball {C : Set E} (hC : Convex ℝ C) {x u n : E} {r : ℝ}
    (hu : u ∈ C) (hr : ‖u - x‖ < r)
    (hn : ∀ w ∈ C ∩ Metric.closedBall x r, ⟪n, w - u⟫ ≤ 0) :
    ∀ w ∈ C, ⟪n, w - u⟫ ≤ 0 := by
  intro w hw
  let t := min 1 ((r - ‖u - x‖) / (‖w - u‖ + 1))
  have ht : 0 < t := lt_min (by norm_num) (div_pos (sub_pos.mpr hr) (by positivity))
  have ht₁ : t ≤ 1 := min_le_left _ _
  have htbound : t * (‖w - u‖ + 1) ≤ r - ‖u - x‖ :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let q := (1 - t) • u + t • w
  have hqC : q ∈ C := hC hu hw (sub_nonneg.mpr ht₁) ht.le (sub_add_cancel 1 t)
  have hqu : q - u = t • (w - u) := by dsimp [q]; module
  have hqx : q - x = (q - u) + (u - x) := by abel
  have hqB : q ∈ Metric.closedBall x r := by
    rw [Metric.mem_closedBall, dist_eq_norm, hqx]
    calc
      _ ≤ ‖q - u‖ + ‖u - x‖ := norm_add_le _ _
      _ ≤ r := by
        rw [hqu, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        linarith only [htbound, ht]
  have h := hn q ⟨hqC, hqB⟩
  rw [hqu, real_inner_smul_right] at h
  exact nonpos_of_mul_nonpos_right h ht

/-- The projection correction provides the relative HPE residual and a local
normal from the distance guarantee of the inner solve. -/
theorem projection_correction {D : Set E} (P : TwoLevel.Projection D) (F : E → E)
    {x y z : E} {Γ L : ℝ} (hΓ : 0 < Γ) (hΓL : Γ ≤ L)
    (hy : y ∈ D) (hz : z ∈ D)
    (hVI : ∀ w ∈ D, 0 ≤ ⟪F z, w - z⟫)
    (hLip : ∀ a ∈ D, ∀ b ∈ D, ‖F a - F b‖ ≤ L * ‖a - b‖)
    (hinner : ‖y - z‖ ≤ Γ * ‖z - x‖ / (128 * L)) :
    let u := P.apply (y - L⁻¹ • F y)
    let n := L • (y - u) - F y
    let v := F u + n - Γ • (u - x)
    (∀ w ∈ D, ⟪n, w - u⟫ ≤ 0) ∧
      ‖u - z‖ ≤ ‖z - x‖ / 64 ∧
      ‖u - x + Γ⁻¹ • v‖ ≤ ‖u - x‖ / 21 := by
  let u := P.apply (y - L⁻¹ • F y)
  let n := L • (y - u) - F y
  let v := F u + n - Γ • (u - x)
  change (∀ w ∈ D, ⟪n, w - u⟫ ≤ 0) ∧
    ‖u - z‖ ≤ ‖z - x‖ / 64 ∧ ‖u - x + Γ⁻¹ • v‖ ≤ ‖u - x‖ / 21
  have hL := hΓ.trans_le hΓL
  have hu : u ∈ D := P.feasible _
  have hscale : L * L⁻¹ = 1 := mul_inv_cancel₀ hL.ne'
  have hΓscale : Γ⁻¹ * Γ = 1 := inv_mul_cancel₀ hΓ.ne'
  have hfix : P.apply (z - L⁻¹ • F z) = z := by
    apply projection_eq_of_normal P hz
    intro w hw
    rw [show z - L⁻¹ • F z - z = -(L⁻¹ • F z) by abel,
      inner_neg_left, real_inner_smul_left]
    exact neg_nonpos.mpr (mul_nonneg (inv_nonneg.mpr hL.le) (hVI w hw))
  have hnorm : ∀ w ∈ D, ⟪n, w - u⟫ ≤ 0 := by
    intro w hw
    have hn := P.normal (y - L⁻¹ • F y) hw
    change ⟪y - L⁻¹ • F y - u, w - u⟫ ≤ 0 at hn
    have heq : n = L • (y - L⁻¹ • F y - u) := by
      dsimp [n]
      simp only [smul_sub, smul_smul, hscale, one_smul]
      abel
    rw [heq, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos hL.le hn
  have hnear : ‖u - z‖ ≤ 2 * ‖y - z‖ := by
    have hdist := P.nonexpansive (y - L⁻¹ • F y) (z - L⁻¹ • F z)
    rw [hfix] at hdist
    have heq : y - L⁻¹ • F y - (z - L⁻¹ • F z) =
        (y - z) - L⁻¹ • (F y - F z) := by rw [smul_sub]; abel
    calc
      _ ≤ _ := hdist
      _ ≤ ‖y - z‖ + ‖L⁻¹ • (F y - F z)‖ := by rw [heq]; exact norm_sub_le _ _
      _ ≤ _ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
        have h := mul_le_mul_of_nonneg_left (hLip y hy z hz) (inv_nonneg.mpr hL.le)
        rw [← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul] at h
        linarith only [h]
  have hmove : ‖u - y‖ ≤ 3 * ‖y - z‖ := by
    have heq : u - y = (u - z) - (y - z) := by abel
    rw [heq]
    exact (norm_sub_le _ _).trans (by linarith only [hnear])
  have hscaled : 128 * (L * ‖y - z‖) ≤ Γ * ‖z - x‖ := by
    have h := (le_div_iff₀ (show 0 < 128 * L by positivity)).mp hinner
    linarith only [h]
  have hprox : ‖u - z‖ ≤ ‖z - x‖ / 64 := by
    apply le_of_mul_le_mul_left _ hL
    have h₁ := mul_le_mul_of_nonneg_left hnear hL.le
    have h₂ := mul_le_mul_of_nonneg_right hΓL (norm_nonneg (z - x))
    linarith only [hscaled, h₁, h₂]
  have hxi : ‖F u + n‖ ≤ 6 * (L * ‖y - z‖) := by
    have heq : F u + n = (F u - F y) + L • (y - u) := by dsimp [n]; abel
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL, norm_sub_rev y u]
    have h := mul_le_mul_of_nonneg_left hmove hL.le
    linarith only [hLip u hu y hy, h]
  have he : u - x + Γ⁻¹ • v = Γ⁻¹ • (F u + n) := by
    dsimp [v]
    rw [smul_sub, smul_smul, hΓscale, one_smul]
    abel
  refine ⟨hnorm, hprox, relative_residual hprox ?_⟩
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΓ)]
  apply le_of_mul_le_mul_left _ hΓ
  rw [← mul_assoc, mul_inv_cancel₀ hΓ.ne', one_mul]
  linarith only [hxi, hscaled]

/-- The original composite gap is bounded by the corrected direction. -/
theorem gap_le_direction {f : E → ℝ} {g Q : E → E} {u w n : E}
    (hsupport : ⟪g u, w - u⟫ ≤ f w - f u)
    (hmono : 0 ≤ ⟪Q u - Q w, u - w⟫)
    (hnormal : ⟪n, w - u⟫ ≤ 0) :
    gap f Q u w ≤ ⟪g u + Q u + n, u - w⟫ := by
  rw [show w - u = -(u - w) by abel, inner_neg_right] at hsupport hnormal
  simp only [gap, inner_add_left, inner_sub_left] at *
  linarith only [hsupport, hmono, hnormal]

/-- A regularized VI solution bounds the regularized gap from below. -/
theorem regularized_gap_lower {f : E → ℝ} {g Q : E → E} {x z y : E} {Γ : ℝ}
    (hsupport : ⟪g z, y - z⟫ ≤ f y - f z)
    (hVI : 0 ≤ ⟪g z + Q z + Γ • (z - x), y - z⟫) :
    Γ / 2 * ‖y - z‖ ^ 2 ≤ gap f Q y z + Γ / 2 * (‖y - x‖ ^ 2 - ‖z - x‖ ^ 2) := by
  have hsplit : y - x = (z - x) + (y - z) := by abel
  rw [hsplit, norm_add_sq_real]
  simp only [gap, inner_add_left, real_inner_smul_left] at *
  linarith only [hsupport, hVI]

/-- A sequence of certified gaps gives the accuracy required by the
projection correction. The scalar premise is the inner stopping rule. -/
theorem inner_accuracy {f : E → ℝ} {g Q : E → E} {x z : E} {Γ L : ℝ}
    (hΓ : 0 < Γ) (a : ℕ → E) (ha : a 0 = x) (m : ℕ)
    (hbudget : (1 / 2 : ℝ) ^ m ≤ Γ / (128 * L))
    (hsupport : ∀ k, ⟪g z, a (k + 1) - z⟫ ≤ f (a (k + 1)) - f z)
    (hVI : ∀ k, 0 ≤ ⟪g z + Q z + Γ • (z - x), a (k + 1) - z⟫)
    (hpass : ∀ k, gap f Q (a (k + 1)) z +
        Γ / 2 * (‖a (k + 1) - x‖ ^ 2 - ‖z - x‖ ^ 2) ≤ Γ / 8 * ‖a k - z‖ ^ 2) :
    ‖a m - z‖ ≤ Γ * ‖z - x‖ / (128 * L) := by
  have h := restarted_distance a (fun k =>
    half_distance hΓ (regularized_gap_lower (hsupport k) (hVI k)) (hpass k)) m
  rw [ha, norm_sub_rev x z] at h
  exact h.trans (by
    rw [← div_mul_eq_mul_div]
    exact mul_le_mul_of_nonneg_right hbudget (norm_nonneg _))

open PathA in
/-- The scheduled Path A pass with target Γ/24 is a contracting inner pass
when its objective and operator are those of the regularized VI. -/
theorem scheduled_pass_contracts {D : Set E} (P : TwoLevel.Projection D)
    (p : ℕ → E → ℝ) (grad op : ℕ → E → E) (Λ M L : ℕ → ℝ) (n : ℕ)
    {f : E → ℝ} {g Q : E → E} {x z s : E} {Γ : ℝ} (hΓ : 0 < Γ)
    (hs : s ∈ D) (hz : z ∈ D)
    (hL : ∀ i, 0 ≤ L i) (hΛL : ∀ i, 2 * L i ≤ Λ i)
    (hlip : ∀ i, ∀ u ∈ D, ∀ w ∈ D, ‖grad i w - grad i u‖ ≤ L i * ‖w - u‖)
    (hΛ : ∀ i, Γ / 24 ≤ Λ i) (hM : ∀ i, 0 ≤ M i)
    (hm : Monotone (fun i => scale (Γ / 24) (Λ i) (M i)))
    (hsupport : ∀ y ∈ D, ⟪g z, y - z⟫ ≤ f y - f z)
    (hVI : ∀ y ∈ D, 0 ≤ ⟪g z + Q z + Γ • (z - x), y - z⟫) :
    let pairs := scheduledPairs p grad op Λ M (fun i => scale (Γ / 24) (Λ i) (M i)) 0 (n + 1)
    (∀ pair ∈ pairs, Pair.Valid D pair.1 pair.2) →
    objective pairs = (fun y => f y + Γ / 2 * ‖y - x‖ ^ 2) →
    operatorSum pairs = Q →
    ∃ out, (adaptivePass P pairs s).outcome = .ok out ∧
      out.average ∈ D ∧ ‖out.average - z‖ ≤ ‖s - z‖ / 2 := by
  intro pairs hp hp_sum hQ_sum
  obtain ⟨out, hout⟩ := scheduled_pass_succeeds P p grad op Λ M
    (fun i => scale (Γ / 24) (Λ i) (M i)) L (n + 1) hs hp hL hlip hΛL
  have hlocal := scheduled_local_accuracy p grad op Λ M
    (show 0 < Γ / 24 by positivity) hΛ hM hm n hs P hp hout
  have hupper := hlocal.2 z hz
  change gap (objective pairs) (operatorSum pairs) out.average z ≤ _ at hupper
  rw [hp_sum, hQ_sum, norm_sub_rev z s] at hupper
  have hlower := regularized_gap_lower (hsupport out.average hlocal.1) (hVI out.average hlocal.1)
  refine ⟨out, hout, hlocal.1, half_distance hΓ hlower ?_⟩
  simp only [gap] at hupper ⊢
  linarith only [hupper]

/-- Relative residual control yields descent with a squared-move term. -/
theorem projected_descent {C : Set E} (P : TwoLevel.Projection C)
    {x u v w : E} {τ value : ℝ} (hw : w ∈ C) (hτ : 0 ≤ τ)
    (hgap : value ≤ ⟪v, u - w⟫)
    (hres : ‖u - x + τ • v‖ ≤ ‖u - x‖ / 21) :
    2 * τ * value + 3 / 4 * ‖u - x‖ ^ 2 ≤
      ‖x - w‖ ^ 2 - ‖P.apply (x - τ • v) - w‖ ^ 2 := by
  have hhalf : ‖u - x + τ • v‖ ≤ ‖u - x‖ / 2 := by
    linarith only [hres, norm_nonneg (u - x)]
  have hsq := pow_le_pow_left₀ (norm_nonneg (u - x + τ • v)) hhalf 2
  nlinarith only [projected_step P (x := x) hw hτ hgap, hsq]

/-- The starting regularization gives the initial safety margin. -/
theorem first_probe_bound {D : Set E} {F : E → E} {x z : E} {Γ r : ℝ}
    (hΓ : 0 < Γ) (hr : 0 ≤ r) (hx : x ∈ D)
    (hΓstart : 8 * ‖F x‖ ≤ Γ * r)
    (hmono : 0 ≤ ⟪F z - F x, z - x⟫)
    (hVI : ∀ w ∈ D, 0 ≤ ⟪F z + Γ • (z - x), w - z⟫) :
    ‖z - x‖ ≤ r / 8 := by
  have h := hVI x hx
  rw [show x - z = -(z - x) by abel, inner_neg_right, inner_add_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq] at h
  rw [inner_sub_left] at hmono
  have hCS := real_inner_le_norm (-(F x)) (z - x)
  rw [inner_neg_left, norm_neg] at hCS
  by_cases hdist : 0 < ‖z - x‖
  · have hprod : (Γ * ‖z - x‖) * ‖z - x‖ ≤ ‖F x‖ * ‖z - x‖ := by
      linarith only [h, hmono, hCS]
    have hle := le_of_mul_le_mul_right hprod hdist
    apply le_of_mul_le_mul_left _ hΓ
    linarith only [hle, hΓstart]
  · linarith only [le_of_not_gt hdist, hr]

omit [InnerProductSpace ℝ E] in
/-- A probe passing the length test remains long after correction. -/
theorem corrected_long {x y z u : E} {r : ℝ}
    (htrial : r / 4 ≤ ‖y - x‖)
    (hy : ‖y - z‖ ≤ r / 128) (hu : ‖u - z‖ ≤ r / 64) :
    29 * r / 128 ≤ ‖u - x‖ := by
  have h₁ := norm_add_le (y - z) (z - u)
  rw [show (y - z) + (z - u) = y - u by abel, norm_sub_rev z u] at h₁
  have h₂ := norm_add_le (y - u) (u - x)
  rw [show (y - u) + (u - x) = y - x by abel] at h₂
  linarith only [h₁, h₂, htrial, hy, hu]

/-- After a rejected trial, halving the regularization at most once
bounds the next exact displacement by the acceptance margin. -/
theorem accepted_after_rejection {D : Set E} {F : E → E} {x zOld z yOld : E}
    {Γold Γ r : ℝ} (hΓ : 0 < Γ) (horder : Γ ≤ Γold) (hhalve : Γold ≤ 2 * Γ)
    (hzOld : zOld ∈ D) (hz : z ∈ D)
    (hmono : 0 ≤ ⟪F zOld - F z, zOld - z⟫)
    (hOld : ∀ w ∈ D, 0 ≤ ⟪F zOld + Γold • (zOld - x), w - zOld⟫)
    (hNew : ∀ w ∈ D, 0 ≤ ⟪F z + Γ • (z - x), w - z⟫)
    (haccuracy : ‖yOld - zOld‖ ≤ r / 128) (hreject : ‖yOld - x‖ < r / 4) :
    ‖z - x‖ ≤ 33 * r / 64 := by
  have hΓold := hΓ.trans_le horder
  have h₁ := hOld z hz
  have h₂ := hNew zOld hzOld
  have hneg : z - zOld = -(zOld - z) := by abel
  rw [hneg, inner_neg_right] at h₁
  have hgraph : 0 ≤ ⟪Γold • (x - zOld) - Γ • (x - z), zOld - z⟫ := by
    rw [show x - zOld = -(zOld - x) by abel, show x - z = -(z - x) by abel]
    simp only [inner_add_left, inner_sub_left, smul_neg, inner_neg_left] at *
    linarith only [h₁, h₂, hmono]
  have hmove := TwoLevel.Plain.resolvent_move (inv_pos.mpr hΓold)
    ((inv_le_inv₀ hΓold hΓ).2 horder) (by simpa only [one_div, inv_inv] using hgraph)
  have hmul : Γ * ‖z - x‖ ≤ Γold * ‖zOld - x‖ := by
    have h := (div_le_div_iff₀ hΓold hΓ).mp (by simpa only [div_eq_inv_mul] using hmove.2)
    simpa only [mul_comm ‖z - x‖ Γ, mul_comm ‖zOld - x‖ Γold] using h
  have hold : ‖zOld - x‖ ≤ 33 * r / 128 := by
    have ht := norm_add_le (zOld - yOld) (yOld - x)
    rw [show (zOld - yOld) + (yOld - x) = zOld - x by abel, norm_sub_rev zOld yOld] at ht
    linarith only [ht, haccuracy, hreject]
  apply le_of_mul_le_mul_left _ hΓ
  have hcap := mul_le_mul_of_nonneg_right hhalve (norm_nonneg (zOld - x))
  have hbound := mul_le_mul_of_nonneg_left hold hΓ.le
  linarith only [hmul, hcap, hbound]

/-- An accepted local correction gives a normal on the original feasible set
and satisfies the relative error test. -/
theorem corrected_certificate {C : Set E} (hC : Convex ℝ C)
    (F : E → E) {x y z : E} {r Γ L : ℝ}
    (Dproj : TwoLevel.Projection (C ∩ Metric.closedBall x r))
    (hr : 0 < r) (hΓ : 0 < Γ) (hΓL : Γ ≤ L)
    (hy : y ∈ C ∩ Metric.closedBall x r) (hz : z ∈ C ∩ Metric.closedBall x r)
    (hVI : ∀ w ∈ C ∩ Metric.closedBall x r,
      0 ≤ ⟪F z + Γ • (z - x), w - z⟫)
    (hLip : ∀ a ∈ C ∩ Metric.closedBall x r, ∀ b ∈ C ∩ Metric.closedBall x r,
      ‖(F a + Γ • (a - x)) - (F b + Γ • (b - x))‖ ≤ L * ‖a - b‖)
    (hinner : ‖y - z‖ ≤ Γ * ‖z - x‖ / (128 * L)) (haccept : ‖z - x‖ ≤ 33 * r / 64) :
    let FΓ := fun a => F a + Γ • (a - x)
    let u := Dproj.apply (y - L⁻¹ • FΓ y)
    let n := L • (y - u) - FΓ y
    u ∈ C ∧ (∀ w ∈ C, ⟪n, w - u⟫ ≤ 0) ∧
      ‖u - x + Γ⁻¹ • (F u + n)‖ ≤ ‖u - x‖ / 21 := by
  intro FΓ u n
  have h := projection_correction Dproj FΓ hΓ hΓL hy hz hVI hLip hinner
  change (∀ w ∈ C ∩ Metric.closedBall x r, ⟪n, w - u⟫ ≤ 0) ∧
    ‖u - z‖ ≤ ‖z - x‖ / 64 ∧
    ‖u - x + Γ⁻¹ • (FΓ u + n - Γ • (u - x))‖ ≤ ‖u - x‖ / 21 at h
  have hu : u ∈ C := (Dproj.feasible _).1
  have huinside : ‖u - x‖ < r := by
    have heq : u - x = (u - z) + (z - x) := by abel
    have htri := norm_add_le (u - z) (z - x)
    rw [← heq] at htri
    linarith only [htri, h.2.1, haccept, hr]
  have hnormal := normal_of_local_ball hC hu huinside h.1
  have heq : FΓ u + n - Γ • (u - x) = F u + n := by dsimp [FΓ]; abel
  exact ⟨hu, hnormal, by simpa only [heq] using h.2.2⟩

/-- An accepted correction on the local ball certifies a projected step
against every comparison point in the original feasible set. -/
theorem corrected_descent {C : Set E} (hC : Convex ℝ C) (P : TwoLevel.Projection C)
    (f : E → ℝ) (g Q : E → E) {x y z : E} {r Γ L : ℝ}
    (Dproj : TwoLevel.Projection (C ∩ Metric.closedBall x r))
    (hr : 0 < r) (hΓ : 0 < Γ) (hΓL : Γ ≤ L)
    (hy : y ∈ C ∩ Metric.closedBall x r) (hz : z ∈ C ∩ Metric.closedBall x r)
    (hVI : ∀ w ∈ C ∩ Metric.closedBall x r,
      0 ≤ ⟪g z + Q z + Γ • (z - x), w - z⟫)
    (hLip : ∀ a ∈ C ∩ Metric.closedBall x r, ∀ b ∈ C ∩ Metric.closedBall x r,
      ‖(g a + Q a + Γ • (a - x)) - (g b + Q b + Γ • (b - x))‖ ≤ L * ‖a - b‖)
    (hinner : ‖y - z‖ ≤ Γ * ‖z - x‖ / (128 * L)) (haccept : ‖z - x‖ ≤ 33 * r / 64)
    (hsupport : ∀ u ∈ C, ∀ w ∈ C, ⟪g u, w - u⟫ ≤ f w - f u)
    (hmono : ∀ u ∈ C, ∀ w ∈ C, 0 ≤ ⟪Q u - Q w, u - w⟫) :
    let F := fun a => g a + Q a + Γ • (a - x)
    let u := Dproj.apply (y - L⁻¹ • F y)
    let n := L • (y - u) - F y
    let v := g u + Q u + n
    u ∈ C ∧ ∀ w ∈ C, 2 * Γ⁻¹ * gap f Q u w + 3 / 4 * ‖u - x‖ ^ 2 ≤
      ‖x - w‖ ^ 2 - ‖P.apply (x - Γ⁻¹ • v) - w‖ ^ 2 := by
  intro F u n v
  have h := corrected_certificate hC (fun a => g a + Q a) Dproj
    hr hΓ hΓL hy hz hVI hLip hinner haccept
  refine ⟨h.1, fun w hw => projected_descent P hw (inv_nonneg.mpr hΓ.le) ?_ h.2.2⟩
  exact gap_le_direction (hsupport u h.1 w hw) (hmono u h.1 w hw) (h.2.1 w hw)

/-- The gap is convex in the point returned by the algorithm. -/
theorem convex_gap {C : Set E} {f : E → ℝ} (hf : ConvexOn ℝ C f)
    (Q : E → E) (w : E) : ConvexOn ℝ C (fun u => gap f Q u w) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hf.2 hx hy ha hb hab
  simp only [gap, inner_sub_right, inner_add_right, real_inner_smul_right, smul_eq_mul] at *
  calc
    _ ≤ a * f x + b * f y - f w +
        (a * ⟪Q w, x⟫ + b * ⟪Q w, y⟫ - ⟪Q w, w⟫) := by linarith only [h]
    _ = _ := by
      have hc := congrArg (fun t : ℝ => t * (f w + ⟪Q w, w⟫)) hab
      nlinarith only [hc]

/-- The finite weighted HPE average has a global comparison-point guarantee. -/
theorem averaged_gap {C : Set E} {G : E → E → ℝ}
    (hC : Convex ℝ C) (hG : ∀ w ∈ C, ConvexOn ℝ C (fun u => G u w))
    (N : ℕ) (x u : ℕ → E) (τ : ℕ → ℝ)
    (hu : ∀ k < N, u k ∈ C) (hτ : ∀ k < N, 0 ≤ τ k)
    (hstep : ∀ k < N, ∀ w ∈ C, 2 * τ k * G (u k) w ≤
      ‖x k - w‖ ^ 2 - ‖x (k + 1) - w‖ ^ 2)
    (hS : 0 < ∑ k ∈ Finset.range N, τ k) :
    let S := ∑ k ∈ Finset.range N, τ k
    let avg := (Finset.range N).centerMass τ u
    avg ∈ C ∧ ∀ w ∈ C, G avg w ≤ ‖x 0 - w‖ ^ 2 / (2 * S) := by
  intro S avg
  have hweights : ∀ k ∈ Finset.range N, 0 ≤ τ k := fun k hk => hτ k (Finset.mem_range.mp hk)
  have hpoints : ∀ k ∈ Finset.range N, u k ∈ C := fun k hk => hu k (Finset.mem_range.mp hk)
  refine ⟨hC.centerMass_mem hweights hS hpoints, ?_⟩
  intro w hw
  have hj := (hG w hw).map_centerMass_le hweights hS hpoints
  change G avg w ≤ S⁻¹ * ∑ k ∈ Finset.range N, τ k * G (u k) w at hj
  refine hj.trans ?_
  have hsum : (∑ k ∈ Finset.range N, 2 * (τ k * G (u k) w)) ≤
      ∑ k ∈ Finset.range N, (‖x k - w‖ ^ 2 - ‖x (k + 1) - w‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [← mul_assoc]
    exact hstep k (Finset.mem_range.mp hk) w hw
  rw [← Finset.mul_sum, Finset.sum_range_sub'] at hsum
  apply (le_div_iff₀ (show 0 < 2 * S by positivity)).mpr
  rw [mul_comm 2 S, ← mul_assoc]
  calc
    S⁻¹ * (∑ k ∈ Finset.range N, τ k * G (u k) w) * S * 2 =
        2 * ∑ k ∈ Finset.range N, τ k * G (u k) w := by
      rw [mul_right_comm S⁻¹, inv_mul_cancel₀ hS.ne', one_mul, mul_comm]
    _ ≤ ‖x 0 - w‖ ^ 2 := by linarith only [hsum, sq_nonneg ‖x N - w‖]

/-- The weight stopping rule implies the desired relative accuracy. -/
theorem averaged_gap_at_threshold {C : Set E} {f : E → ℝ} (hf : ConvexOn ℝ C f)
    (Q : E → E) (N : ℕ) (x u : ℕ → E) (τ : ℕ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hu : ∀ k < N, u k ∈ C) (hτ : ∀ k < N, 0 ≤ τ k)
    (hstep : ∀ k < N, ∀ w ∈ C, 2 * τ k * gap f Q (u k) w ≤
      ‖x k - w‖ ^ 2 - ‖x (k + 1) - w‖ ^ 2)
    (hthreshold : 1 / (2 * ε) ≤ ∑ k ∈ Finset.range N, τ k) :
    let avg := (Finset.range N).centerMass τ u
    avg ∈ C ∧ ∀ w ∈ C, gap f Q avg w ≤ ε * ‖x 0 - w‖ ^ 2 := by
  let S := ∑ k ∈ Finset.range N, τ k
  have hS : 0 < S := (by positivity : 0 < 1 / (2 * ε)).trans_le hthreshold
  have h := averaged_gap hf.1 (fun w _ => convex_gap hf Q w) N x u τ hu hτ hstep hS
  refine ⟨h.1, fun w hw => (h.2 w hw).trans ?_⟩
  apply (div_le_iff₀ (show 0 < 2 * S by positivity)).mpr
  have hεS := (div_le_iff₀ (show 0 < 2 * ε by positivity)).mp hthreshold
  have hh := mul_le_mul_of_nonneg_right hεS (sq_nonneg ‖x 0 - w‖)
  nlinarith only [hh]

/-- A prefix still below the weight threshold consists entirely of long
steps. Their squared moves bound the length of such a prefix. -/
theorem prefix_budget {f : E → ℝ} {Q : E → E} {z : E} {r threshold : ℝ}
    (hr : 0 ≤ r) (N : ℕ) (x u : ℕ → E) (τ : ℕ → ℝ)
    (hτ : ∀ k < N, 0 ≤ τ k) (hgap : ∀ k < N, 0 ≤ gap f Q (u k) z)
    (hstep : ∀ k < N, 2 * τ k * gap f Q (u k) z + 3 / 4 * ‖u k - x k‖ ^ 2 ≤
      ‖x k - z‖ ^ 2 - ‖x (k + 1) - z‖ ^ 2)
    (hlong : ∀ k < N, threshold ≤ τ k ∨ r ≤ ‖u k - x k‖)
    (hbelow : (∑ k ∈ Finset.range N, τ k) < threshold) :
    (N : ℝ) * (3 / 4 * r ^ 2) ≤ ‖x 0 - z‖ ^ 2 := by
  have hnonneg : ∀ k ∈ Finset.range N, 0 ≤ τ k := fun k hk => hτ k (Finset.mem_range.mp hk)
  have hsum : (∑ _k ∈ Finset.range N, (3 / 4 : ℝ) * r ^ 2) ≤
      ∑ k ∈ Finset.range N, (‖x k - z‖ ^ 2 - ‖x (k + 1) - z‖ ^ 2) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkN := Finset.mem_range.mp hk
    have hweight := (Finset.single_le_sum (f := τ) (fun j hj => hnonneg j hj) hk).trans_lt hbelow
    have hmove := (hlong k hkN).resolve_left (not_le.mpr hweight)
    have hsq := pow_le_pow_left₀ hr hmove 2
    have hproduct := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hτ k hkN)) (hgap k hkN)
    linarith only [hsq, hproduct, hstep k hkN]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_range_sub'] at hsum
  linarith only [hsum, sq_nonneg ‖x N - z‖]

/-- A feasible prefix beyond the energy budget must reach the stopping
threshold. -/
theorem threshold_reached_by {f : E → ℝ} {Q : E → E} {z : E} {r threshold : ℝ}
    (hr : 0 ≤ r) (N : ℕ) (x u : ℕ → E) (τ : ℕ → ℝ)
    (hτ : ∀ k < N, 0 ≤ τ k) (hgap : ∀ k < N, 0 ≤ gap f Q (u k) z)
    (hstep : ∀ k < N, 2 * τ k * gap f Q (u k) z + 3 / 4 * ‖u k - x k‖ ^ 2 ≤
      ‖x k - z‖ ^ 2 - ‖x (k + 1) - z‖ ^ 2)
    (hlong : ∀ k < N, threshold ≤ τ k ∨ r ≤ ‖u k - x k‖)
    (hN : ‖x 0 - z‖ ^ 2 < (N : ℝ) * (3 / 4 * r ^ 2)) :
    threshold ≤ ∑ k ∈ Finset.range N, τ k := by
  exact le_of_not_gt fun hbelow =>
    (not_lt_of_ge (prefix_budget hr N x u τ hτ hgap hstep hlong hbelow)) hN

end LeanLab.Sliding.ProximalHPE
