module

public import LeanLab.Variants.ProximalHPE

set_option linter.style.header false

/-!
# Linear convergence of localized HPE

An error bound converts the computed residual into distance to the solution set.
The projected step then contracts on the regularization floor.
-/

@[expose] public section

namespace LeanLab.Sliding.ProximalHPE

open scoped BigOperators RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The normal from an accepted correction can be used against any VI solution. -/
theorem direction_nonneg_at_solution {C : Set E} {F : E → E} {u z n : E}
    (hu : u ∈ C)
    (hVI : ∀ w ∈ C, 0 ≤ ⟪F z, w - z⟫)
    (hmono : 0 ≤ ⟪F u - F z, u - z⟫)
    (hnormal : ⟪n, z - u⟫ ≤ 0) :
    0 ≤ ⟪F u + n, u - z⟫ := by
  rw [show z - u = -(u - z) by abel, inner_neg_right] at hnormal
  rw [inner_sub_left] at hmono
  rw [inner_add_left]
  linarith only [hVI u hu, hmono, hnormal]

/-- Strong monotonicity supplies an error bound for any certified direction. -/
theorem strong_monotone_error_bound {Z : Set E} {u z v : E} {μ : ℝ}
    (hz : z ∈ Z) (hμ : 0 < μ) (h : μ * ‖u - z‖ ^ 2 ≤ ⟪v, u - z⟫) :
    Metric.infDist u Z ≤ μ⁻¹ * ‖v‖ := by
  refine (Metric.infDist_le_dist_of_mem hz).trans ?_
  rw [dist_eq_norm]
  by_cases hd : 0 < ‖u - z‖
  · have hh := h.trans (real_inner_le_norm v (u - z))
    rw [pow_two, ← mul_assoc] at hh
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hμ).mpr (by
      rw [mul_comm]
      exact le_of_mul_le_mul_right hh hd)
  · have hzero : ‖u - z‖ = 0 := le_antisymm (le_of_not_gt hd) (norm_nonneg _)
    rw [hzero]
    positivity

/-- A strongly monotone VI satisfies the error bound for directions obtained
by adding a normal to its operator value. -/
theorem strong_monotone_VI_error_bound {C Z : Set E} {F : E → E} {u z n : E} {μ : ℝ}
    (hu : u ∈ C) (hz : z ∈ Z) (hμ : 0 < μ)
    (hVI : ∀ w ∈ C, 0 ≤ ⟪F z, w - z⟫)
    (hmono : μ * ‖u - z‖ ^ 2 ≤ ⟪F u - F z, u - z⟫)
    (hnormal : ⟪n, z - u⟫ ≤ 0) :
    Metric.infDist u Z ≤ μ⁻¹ * ‖F u + n‖ := by
  apply strong_monotone_error_bound hz hμ
  rw [show z - u = -(u - z) by abel, inner_neg_right] at hnormal
  rw [inner_sub_left] at hmono
  rw [inner_add_left]
  linarith only [hVI u hu, hmono, hnormal]

/-- The relative residual bounds the norm of the computed direction. -/
theorem scaled_direction_bound {x u v : E} {τ : ℝ} (hτ : 0 ≤ τ)
    (hres : ‖u - x + τ • v‖ ≤ ‖u - x‖ / 21) :
    τ * ‖v‖ ≤ (22 / 21) * ‖u - x‖ := by
  have heq : τ • v = (u - x + τ • v) - (u - x) := by abel
  have hnorm := norm_sub_le (u - x + τ • v) (u - x)
  rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ] at hnorm
  linarith only [hnorm, hres]

/-- Fejér descent transfers to squared distance from the solution set. -/
theorem projected_distance_decrease [ProperSpace E] {C Z : Set E} (P : TwoLevel.Projection C)
    (hZ : IsClosed Z) (hZn : Z.Nonempty) (hZC : Z ⊆ C)
    {x u v : E} {τ : ℝ} (hτ : 0 ≤ τ)
    (hdir : ∀ z ∈ Z, 0 ≤ ⟪v, u - z⟫)
    (hres : ‖u - x + τ • v‖ ≤ ‖u - x‖ / 21) :
    Metric.infDist (P.apply (x - τ • v)) Z ^ 2 + (440 / 441) * ‖u - x‖ ^ 2 ≤
      Metric.infDist x Z ^ 2 := by
  obtain ⟨z, hz, hdist⟩ := hZ.exists_infDist_eq_dist hZn x
  rw [dist_eq_norm] at hdist
  have hproj := projected_step P (x := x) (hZC hz) hτ (hdir z hz)
  have hnext := Metric.infDist_le_dist_of_mem (x := P.apply (x - τ • v)) hz
  rw [dist_eq_norm] at hnext
  have hnextSq := pow_le_pow_left₀ Metric.infDist_nonneg hnext 2
  have hresSq := pow_le_pow_left₀ (norm_nonneg _) hres 2
  rw [hdist]
  nlinarith only [hproj, hnextSq, hresSq]

/-- At the regularization floor Γ = 1/κ, the projected update contracts
squared distance. The computed residual is a stopping certificate. -/
theorem projected_floor_rate [ProperSpace E] {C Z : Set E} (P : TwoLevel.Projection C)
    (hZ : IsClosed Z) (hZn : Z.Nonempty) (hZC : Z ⊆ C)
    {x u v : E} {κ : ℝ} (hκ : 0 < κ)
    (hdir : ∀ z ∈ Z, 0 ≤ ⟪v, u - z⟫)
    (hres : ‖u - x + κ • v‖ ≤ ‖u - x‖ / 21)
    (herror : Metric.infDist u Z ≤ κ * ‖v‖) :
    Metric.infDist (P.apply (x - κ • v)) Z ^ 2 ≤
        (1409 / 1849) * Metric.infDist x Z ^ 2 ∧
      (κ * ‖v‖) ^ 2 ≤ (11 / 10) * Metric.infDist x Z ^ 2 := by
  have hdrop := projected_distance_decrease P hZ hZn hZC hκ.le hdir hres
  have hscaled := scaled_direction_bound hκ.le hres
  have htriangle := Metric.infDist_le_infDist_add_dist (x := x) (y := u) (s := Z)
  rw [dist_eq_norm, norm_sub_rev x u] at htriangle
  have hmove : Metric.infDist x Z ≤ (43 / 21) * ‖u - x‖ := by
    linarith only [htriangle, herror, hscaled]
  have hmoveSq := pow_le_pow_left₀ Metric.infDist_nonneg hmove 2
  have hscaledSq := pow_le_pow_left₀ (mul_nonneg hκ.le (norm_nonneg v)) hscaled 2
  refine ⟨?_, ?_⟩
  · nlinarith only [hdrop, hmoveSq]
  · nlinarith only [hdrop, hscaledSq, sq_nonneg (Metric.infDist (P.apply (x - κ • v)) Z)]

/-- Strong monotonicity gives a sharper factor by keeping the VI term
in the projected HPE descent inequality. -/
theorem projected_strong_monotone_rate {C : Set E} (P : TwoLevel.Projection C)
    {x u v z : E} {μ : ℝ} (hz : z ∈ C) (hμ : 0 < μ)
    (hvi : μ * ‖u - z‖ ^ 2 ≤ ⟪v, u - z⟫)
    (hres : ‖u - x + μ⁻¹ • v‖ ≤ ‖u - x‖ / 21) :
    ‖P.apply (x - μ⁻¹ • v) - z‖ ^ 2 ≤ (221 / 661) * ‖x - z‖ ^ 2 := by
  have hstep := projected_step P (x := x) hz (inv_nonneg.mpr hμ.le) hvi
  have hleft : 2 * μ⁻¹ * (μ * ‖u - z‖ ^ 2) = 2 * ‖u - z‖ ^ 2 := by
    rw [← mul_assoc, mul_assoc 2, inv_mul_cancel₀ hμ.ne', mul_one]
  rw [hleft] at hstep
  have hresSq := pow_le_pow_left₀ (norm_nonneg _) hres 2
  have ht := norm_add_le (x - u) (u - z)
  rw [show (x - u) + (u - z) = x - z by abel, norm_sub_rev x u] at ht
  have htSq := pow_le_pow_left₀ (norm_nonneg _) ht 2
  have hweighted : (440 / 661) * ‖x - z‖ ^ 2 ≤
      (440 / 441) * ‖u - x‖ ^ 2 + 2 * ‖u - z‖ ^ 2 := by
    nlinarith only [htSq, sq_nonneg ((440 / 441) * ‖u - x‖ - 2 * ‖u - z‖)]
  nlinarith only [hstep, hresSq, hweighted]

/-- An accepted trial stays in a local error-bound neighborhood if the
outer iterate is in a ball of one third of its radius around a solution. -/
theorem corrected_point_near_solution {C : Set E} (P : TwoLevel.Projection C)
    {x u v z : E} {τ : ℝ} (hz : z ∈ C) (hτ : 0 ≤ τ) (hdir : 0 ≤ ⟪v, u - z⟫)
    (hres : ‖u - x + τ • v‖ ≤ ‖u - x‖ / 21) :
    ‖u - z‖ ≤ 3 * ‖x - z‖ := by
  have hstep := projected_step P (x := x) hz hτ hdir
  have hresSq := pow_le_pow_left₀ (norm_nonneg _) hres 2
  have hmove : ‖u - x‖ ≤ 2 * ‖x - z‖ := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (by positivity)
    nlinarith only [hstep, hresSq, sq_nonneg ‖P.apply (x - τ • v) - z‖,
      sq_nonneg ‖u - x‖]
  have ht := norm_add_le (u - x) (x - z)
  rw [show (u - x) + (x - z) = u - z by abel] at ht
  linarith only [ht, hmove]

/-- The computed local correction at Γ = 1/κ gives the contracting HPE
step, provided the error bound holds on the original feasible set. -/
theorem corrected_floor_rate [ProperSpace E] {C Z : Set E} (hC : Convex ℝ C)
    (P : TwoLevel.Projection C) (hZ : IsClosed Z) (hZn : Z.Nonempty) (hZC : Z ⊆ C)
    (F : E → E) {x y z : E} {r κ L : ℝ}
    (Dproj : TwoLevel.Projection (C ∩ Metric.closedBall x r))
    (hr : 0 < r) (hκ : 0 < κ) (hL : κ⁻¹ ≤ L)
    (hy : y ∈ C ∩ Metric.closedBall x r) (hz : z ∈ C ∩ Metric.closedBall x r)
    (hVI : ∀ w ∈ C ∩ Metric.closedBall x r, 0 ≤ ⟪F z + κ⁻¹ • (z - x), w - z⟫)
    (hLip : ∀ a ∈ C ∩ Metric.closedBall x r, ∀ b ∈ C ∩ Metric.closedBall x r,
      ‖(F a + κ⁻¹ • (a - x)) - (F b + κ⁻¹ • (b - x))‖ ≤ L * ‖a - b‖)
    (hinner : ‖y - z‖ ≤ κ⁻¹ * ‖z - x‖ / (128 * L))
    (haccept : ‖z - x‖ ≤ 33 * r / 64)
    (hsol : ∀ s ∈ Z, ∀ w ∈ C, 0 ≤ ⟪F s, w - s⟫)
    (hmono : ∀ u ∈ C, ∀ s ∈ Z, 0 ≤ ⟪F u - F s, u - s⟫)
    (herror : ∀ u ∈ C, ∀ n, (∀ w ∈ C, ⟪n, w - u⟫ ≤ 0) →
      Metric.infDist u Z ≤ κ * ‖F u + n‖) :
    let FΓ := fun a => F a + κ⁻¹ • (a - x)
    let u := Dproj.apply (y - L⁻¹ • FΓ y)
    let v := F u + (L • (y - u) - FΓ y)
    u ∈ C ∧
      Metric.infDist (P.apply (x - κ • v)) Z ^ 2 ≤ (1409 / 1849) * Metric.infDist x Z ^ 2 ∧
      (κ * ‖v‖) ^ 2 ≤ (11 / 10) * Metric.infDist x Z ^ 2 := by
  intro FΓ u v
  obtain ⟨hu, hnormal, hres⟩ :=
    corrected_certificate hC F Dproj hr (inv_pos.mpr hκ) hL hy hz hVI hLip hinner haccept
  have hdir (s : E) (hs : s ∈ Z) : 0 ≤ ⟪v, u - s⟫ :=
    direction_nonneg_at_solution hu (hsol s hs) (hmono u hu s hs) (hnormal s (hZC hs))
  exact ⟨hu, projected_floor_rate P hZ hZn hZC hκ hdir
    (by simpa only [inv_inv] using hres) (herror u hu _ hnormal)⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A prefix contracts geometrically with the number of floor steps. Its
other steps are counted by the fixed decrease in squared distance. -/
theorem mixed_step_bounds (e : ℕ → ℝ) (floor : ℕ → Prop) [DecidablePred floor]
    {q c : ℝ} (hq : 0 ≤ q) (hq₁ : q ≤ 1) (hc : 0 ≤ c) (N : ℕ)
    (hnonneg : ∀ k, 0 ≤ e k)
    (hfloor : ∀ k < N, floor k → e (k + 1) ≤ q * e k)
    (hlong : ∀ k < N, ¬floor k → e (k + 1) + c ≤ e k) :
    e N ≤ q ^ ((Finset.range N).filter floor).card * e 0 ∧
      e N + (((Finset.range N).filter (fun k => ¬floor k)).card : ℝ) * c ≤ e 0 := by
  induction N with
  | zero => simp
  | succ n ih =>
    obtain ⟨hgeom, hcount⟩ := ih (fun k hk => hfloor k (Nat.lt_succ_of_lt hk))
      (fun k hk => hlong k (Nat.lt_succ_of_lt hk))
    have hnotFloor : n ∉ (Finset.range n).filter floor := by simp
    have hnotLong : n ∉ (Finset.range n).filter (fun k => ¬floor k) := by simp
    have hrange : Finset.range (n + 1) = insert n (Finset.range n) := by
      ext j
      simp only [Finset.mem_range, Finset.mem_insert]
      omega
    by_cases hn : floor n
    · have hstep := hfloor n (Nat.lt_succ_self _) hn
      have hqmul := mul_le_mul_of_nonneg_right hq₁ (hnonneg n)
      simp only [hrange, Finset.filter_insert, ite_eq_left hn, ite_eq_right (not_not_intro hn),
        Finset.card_insert_of_notMem hnotFloor]
      refine ⟨hstep.trans ?_, by linarith only [hstep, hcount, hqmul]⟩
      calc
        _ ≤ q * (q ^ ((Finset.range n).filter floor).card * e 0) :=
          mul_le_mul_of_nonneg_left hgeom hq
        _ = _ := by rw [pow_succ]; ring
    · have hstep := hlong n (Nat.lt_succ_self _) hn
      simp only [hrange, Finset.filter_insert, ite_eq_right hn, ite_eq_left hn,
        Finset.card_insert_of_notMem hnotLong, Nat.cast_add, Nat.cast_one]
      exact ⟨by linarith only [hstep, hgeom, hc], by linarith only [hstep, hcount]⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A prefix with room for the long steps and the prescribed number of
contractions contains a floor step with a sufficiently small residual. -/
theorem floor_residual_before (e residual : ℕ → ℝ) (floor : ℕ → Prop)
    {q c tol : ℝ} (hq : 0 ≤ q) (hq₁ : q ≤ 1) (hc : 0 ≤ c) (N B m : ℕ)
    (hnonneg : ∀ k, 0 ≤ e k)
    (hfloor : ∀ k < N, floor k → e (k + 1) ≤ q * e k)
    (hlong : ∀ k < N, ¬floor k → e (k + 1) + c ≤ e k)
    (hres : ∀ k < N, floor k → residual k ≤ (11 / 10) * e k)
    (hB : e 0 < ((B : ℝ) + 1) * c) (hN : B + m < N)
    (haccuracy : (11 / 10) * (q ^ m * e 0) ≤ tol) :
    ∃ k < N, floor k ∧ residual k ≤ tol := by
  classical
  let floors := (Finset.range N).filter floor
  let longs := (Finset.range N).filter (fun k => ¬floor k)
  have hbudget := (mixed_step_bounds e floor hq hq₁ hc N hnonneg hfloor hlong).2
  change e N + (longs.card : ℝ) * c ≤ e 0 at hbudget
  have hlongs : longs.card ≤ B := by
    by_contra! hh
    have hh' : (B : ℝ) + 1 ≤ longs.card := by exact_mod_cast (Nat.succ_le_of_lt hh)
    have hmul := mul_le_mul_of_nonneg_right hh' hc
    linarith only [hbudget, hnonneg N, hB, hmul]
  have hcards : floors.card + longs.card = N := by
    simpa only [floors, longs, Finset.card_range] using
      Finset.card_filter_add_card_filter_not (s := Finset.range N) floor
  have hfloors : m < floors.card := by omega
  have hne : floors.Nonempty := Finset.card_pos.mp (Nat.zero_lt_of_lt hfloors)
  let k := floors.max' hne
  have hk := floors.max'_mem hne
  have hkN : k < N := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  have hkfloor : floor k := (Finset.mem_filter.mp hk).2
  have hsub : floors.erase k ⊆ (Finset.range k).filter floor := by
    intro j hj
    obtain ⟨hne', hjmem⟩ := Finset.mem_erase.mp hj
    have hjle := floors.le_max' j hjmem
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_le_of_ne hjle hne'),
      (Finset.mem_filter.mp hjmem).2⟩
  have hbefore := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hk] at hbefore
  have hm : m ≤ ((Finset.range k).filter floor).card := by omega
  have he := (mixed_step_bounds e floor hq hq₁ hc k hnonneg
    (fun j hj => hfloor j (hj.trans hkN)) (fun j hj => hlong j (hj.trans hkN))).1
  have hpow := mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq hq₁ hm) (hnonneg 0)
  exact ⟨k, hkN, hkfloor, (hres k hkN hkfloor).trans
    ((mul_le_mul_of_nonneg_left (he.trans hpow) (by norm_num)).trans haccuracy)⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Explicit logarithmic number of floor contractions for the residual
certificate, measured in squared distance. -/
theorem logarithmic_floor_budget {e₀ η : ℝ} (hη : 0 < η) :
    let q : ℝ := 1409 / 1849
    let m := ⌈Real.logb q⁻¹ (max 1 ((11 / 10) * e₀ / η ^ 2))⌉₊
    (11 / 10) * (q ^ m * e₀) ≤ η ^ 2 := by
  intro q m
  have hq : 0 < q := by norm_num [q]
  have hbase : 1 < q⁻¹ := by norm_num [q]
  have harg : 0 < max 1 ((11 / 10) * e₀ / η ^ 2) :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hpow := (Real.logb_le_iff_le_rpow hbase harg).mp
    (Nat.le_ceil (Real.logb q⁻¹ (max 1 ((11 / 10) * e₀ / η ^ 2))))
  rw [Real.rpow_natCast, inv_pow] at hpow
  change max 1 ((11 / 10) * e₀ / η ^ 2) ≤ (q ^ m)⁻¹ at hpow
  have hb := (div_le_iff₀ (pow_pos hη 2)).mp ((le_max_right _ _).trans hpow)
  have hmul := mul_le_mul_of_nonneg_right hb (pow_nonneg hq.le m)
  calc
    _ = ((11 / 10) * e₀) * q ^ m := by ring
    _ ≤ (q ^ m)⁻¹ * η ^ 2 * q ^ m := hmul
    _ = _ := by rw [mul_right_comm, inv_mul_cancel₀ (pow_ne_zero m hq.ne'), one_mul]

/-- A certified HPE trajectory stops by a budget of long steps and
geometric contractions at the regularization floor. -/
theorem projected_trace_residual_before [ProperSpace E] {C Z : Set E}
    (P : TwoLevel.Projection C) (hZ : IsClosed Z) (hZn : Z.Nonempty) (hZC : Z ⊆ C)
    (x u v : ℕ → E) (τ : ℕ → ℝ) (N : ℕ) {κ ℓ η R : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ) (hη : 0 < η) (hR : Metric.infDist (x 0) Z ≤ R)
    (hτ : ∀ k < N, 0 ≤ τ k)
    (hupdate : ∀ k < N, x (k + 1) = P.apply (x k - τ k • v k))
    (hdir : ∀ k < N, ∀ z ∈ Z, 0 ≤ ⟪v k, u k - z⟫)
    (hres : ∀ k < N, ‖u k - x k + τ k • v k‖ ≤ ‖u k - x k‖ / 21)
    (herror : ∀ k < N, τ k = κ → Metric.infDist (u k) Z ≤ κ * ‖v k‖)
    (hlong : ∀ k < N, τ k ≠ κ → ℓ ≤ ‖u k - x k‖) :
    let B := ⌊R ^ 2 / ((440 / 441) * ℓ ^ 2)⌋₊
    let m := ⌈Real.logb (1849 / 1409) (max 1 ((11 / 10) * R ^ 2 / η ^ 2))⌉₊
    B + m < N → ∃ k < N, τ k = κ ∧ κ * ‖v k‖ ≤ η ∧ Metric.infDist (u k) Z ≤ η := by
  intro B m hN
  let e (k : ℕ) := Metric.infDist (x k) Z ^ 2
  have hR₂ := pow_le_pow_left₀ Metric.infDist_nonneg hR 2
  have hcost : 0 < (440 / 441 : ℝ) * ℓ ^ 2 := by positivity
  have hB : e 0 < ((B : ℝ) + 1) * ((440 / 441) * ℓ ^ 2) :=
    hR₂.trans_lt ((div_lt_iff₀ hcost).mp (Nat.lt_floor_add_one _))
  have hlog := logarithmic_floor_budget (e₀ := R ^ 2) hη
  have hbase : (1409 / 1849 : ℝ)⁻¹ = 1849 / 1409 := by norm_num
  have hlog₁ : (11 / 10) * ((1409 / 1849 : ℝ) ^ m * R ^ 2) ≤ η ^ 2 := by
    dsimp only at hlog
    rw [hbase] at hlog
    exact hlog
  have haccuracy : (11 / 10) * ((1409 / 1849 : ℝ) ^ m * e 0) ≤ η ^ 2 :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR₂ (by positivity))
      (by norm_num)).trans hlog₁
  have hfloor (k : ℕ) (hk : k < N) (h : τ k = κ) :
      e (k + 1) ≤ (1409 / 1849) * e k ∧ (κ * ‖v k‖) ^ 2 ≤ (11 / 10) * e k := by
    have he := hres k hk
    rw [h] at he
    simpa only [e, hupdate k hk, h] using
      projected_floor_rate P hZ hZn hZC hκ (hdir k hk) he (herror k hk h)
  have hdrop (k : ℕ) (hk : k < N) (h : τ k ≠ κ) :
      e (k + 1) + (440 / 441) * ℓ ^ 2 ≤ e k := by
    have hstep := projected_distance_decrease P hZ hZn hZC (hτ k hk) (hdir k hk) (hres k hk)
    have hsq := pow_le_pow_left₀ hℓ.le (hlong k hk h) 2
    simp only [e, hupdate k hk]
    linarith only [hstep, hsq]
  obtain ⟨k, hk, h, hs⟩ := floor_residual_before e (fun k => (κ * ‖v k‖) ^ 2)
    (fun k => τ k = κ) (by norm_num) (by norm_num) (by positivity) N B m
    (fun k => sq_nonneg _) (fun k hk hh => (hfloor k hk hh).1) hdrop
    (fun k hk hh => (hfloor k hk hh).2) hB hN haccuracy
  have hc : κ * ‖v k‖ ≤ η :=
    le_of_pow_le_pow_left₀ (n := 2) (by decide) hη.le hs
  exact ⟨k, hk, h, hc, (herror k hk h).trans hc⟩

end LeanLab.Sliding.ProximalHPE
