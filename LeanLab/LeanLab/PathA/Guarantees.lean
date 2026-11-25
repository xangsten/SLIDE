module

public import LeanLab.PathA.Pass
public import LeanLab.PathA.Schedule

set_option linter.style.header false

/-!
# Accuracy and query budgets for path A

The schedule is the one in (A.2). A pass may reject the curvature at any
level. Once the outer radius test accepts, the local estimate gives (A.1)
on the entire constraint set.
-/

@[expose] public section

namespace LeanLab.Sliding.PathA

open Set
open TwoLevel (Projection)
open Localized (Level Oracle region)
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def scheduledPairs (p : ℕ → E → ℝ) (g Q : ℕ → E → E) (Λ M h : ℕ → ℝ)
    (i : ℕ) : ℕ → List (Pair E)
  | 0 => []
  | n + 1 =>
    (p i, ⟨g i, Q i, Λ i, M i, steps h i - 1⟩) :: scheduledPairs p g Q Λ M h (i + 1) n

private theorem steps_pos {h : ℕ → ℝ} (h₀ : 1 ≤ h 0) (hm : Monotone h) (i : ℕ) :
    0 < steps h i := by
  have pos (r k : ℝ) (hr : 0 < r) (hk : 0 < k) : 0 < ⌈k * r⌉₊ :=
    Nat.cast_pos.mp ((mul_pos hk hr).trans_le (Nat.le_ceil _))
  have hp (j : ℕ) : 0 < h j := zero_lt_one.trans_le (h₀.trans (hm (Nat.zero_le j)))
  cases i with
  | zero => exact pos _ _ (hp 0) (by norm_num)
  | succ i => exact pos _ _ (div_pos (hp _) (hp _)) (by norm_num)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem length_scheduledPairs (p : ℕ → E → ℝ) (g Q : ℕ → E → E)
    (Λ M h : ℕ → ℝ) (i n : ℕ) : (scheduledPairs p g Q Λ M h i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [scheduledPairs, ih]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem get_scheduledPairs (p : ℕ → E → ℝ) (g Q : ℕ → E → E)
    (Λ M h : ℕ → ℝ) (i n j : ℕ) (hj : j < n) :
    (scheduledPairs p g Q Λ M h i n)[j]? =
      some (p (i + j), ⟨g (i + j), Q (i + j), Λ (i + j), M (i + j), steps h (i + j) - 1⟩) := by
  induction n generalizing i j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp [scheduledPairs]
    | succ j =>
      simpa [scheduledPairs, show i + (j + 1) = i + 1 + j by omega] using
        ih (i + 1) j (Nat.lt_of_succ_lt_succ hj)

private theorem prefixCalls_eq_prod (h : ℕ → ℝ) (i : ℕ) :
    prefixCalls h i = ∏ j ∈ Finset.range (i + 1), steps h j := by
  induction i with
  | zero => simp [prefixCalls]
  | succ i ih =>
    rw [prefixCalls, ih]
    conv_rhs => rw [Finset.prod_range_succ]

/-- The per-attempt part of (A.9), including attempts that abort at any level. -/
theorem scheduled_attempt_calls {D : Set E} (P : Projection D) (p : ℕ → E → ℝ)
    (g Q : ℕ → E → E) (Λ M : ℕ → ℝ) {h : ℕ → ℝ} (h₀ : 1 ≤ h 0)
    (hm : Monotone h) (s : E) {i n : ℕ} (hi : i < n) (o : Oracle) :
    ((adaptivePass P (scheduledPairs p g Q Λ M h 0 n) s).calls i o : ℝ) ≤
      6 * 17 ^ i * h i := by
  let pairs := scheduledPairs p g Q Λ M h 0 n
  have hn : i < (pairs.map Prod.snd).length := by simp [pairs, length_scheduledPairs, hi]
  have he := Localized.visits_eq_prod (pairs.map Prod.snd) 0 i hn
  rw [zero_add] at he
  have hprod : Localized.visits (pairs.map Prod.snd) 0 i = prefixCalls h i := by
    rw [he, prefixCalls_eq_prod]
    apply Finset.prod_congr rfl
    intro j hj
    have hj' := (Finset.mem_range.mp hj).trans_le (Nat.succ_le_of_lt hi)
    simp [pairs, List.getElem?_map, get_scheduledPairs p g Q Λ M h 0 n j hj',
      Nat.sub_add_cancel (steps_pos h₀ hm j)]
  calc
    _ ≤ ((2 * Localized.visits (pairs.map Prod.snd) 0 i : ℕ) : ℝ) :=
      Nat.cast_le.mpr (adaptivePass_calls_le P pairs s i o)
    _ = 2 * (prefixCalls h i : ℝ) := by rw [hprod, Nat.cast_mul, Nat.cast_ofNat]
    _ ≤ _ := by linarith only [prefix_calls_le h₀ hm i]

/-- Terminal product at the entrance to a position, before its own cycle. -/
def enteringWeight (h : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | i + 1 => prefixWeight h i

private theorem enteringWeight_pos (h : ℕ → ℝ) (i : ℕ) : 0 < enteringWeight h i := by
  have hp (j : ℕ) : 0 < prefixWeight h j := by
    induction j with
    | zero => exact weight_pos _
    | succ j ih => exact mul_pos ih (weight_pos _)
  cases i with
  | zero => exact zero_lt_one
  | succ i => exact hp i

private theorem enteringWeight_next (h : ℕ → ℝ) (i : ℕ) :
    enteringWeight h i * weight (steps h i - 1) = enteringWeight h (i + 1) := by
  cases i with
  | zero => simp [enteringWeight, prefixWeight]
  | succ i => rfl

omit [InnerProductSpace ℝ E] in
/-- Identify the recursive potential with the indexed coefficients of (A.2).
The identity also holds for saved centers that differ by level. -/
theorem scheduled_energy (p : ℕ → E → ℝ) (g Q : ℕ → E → E) (Λ M h : ℕ → ℝ)
    (w : E) (U : ℕ → E) (i n : ℕ) :
    enteringWeight h i ^ 2 *
        centerEnergy w U (scheduledPairs p g Q Λ M h i n) i (enteringWeight h i) =
      ∑ j ∈ Finset.range n, contribution (prefixWeight h (i + j)) (Λ (i + j)) (M (i + j)) *
        ‖U (i + j) - w‖ ^ 2 := by
  induction n generalizing i with
  | zero => simp [scheduledPairs, centerEnergy]
  | succ n ih =>
    rw [scheduledPairs, centerEnergy, Finset.sum_range_succ']
    rw [← mul_assoc, ← mul_pow, enteringWeight_next, mul_add]
    have ht : 0 < enteringWeight h (i + 1) := enteringWeight_pos h _
    have he : enteringWeight h (i + 1) ^ 2 *
        regularization (⟨g i, Q i, Λ i, M i, steps h i - 1⟩ : Level E) (enteringWeight h i) =
        contribution (prefixWeight h i) (Λ i) (M i) := by
      simp only [regularization]
      rw [enteringWeight_next]
      change _ = contribution (enteringWeight h (i + 1)) (Λ i) (M i)
      unfold contribution
      field_simp
    rw [← mul_assoc, he, ih, add_comm]
    simp only [Nat.add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [show i + (j + 1) = i + 1 + j by omega]

theorem Pair.Valid.restrict {C D : Set E} {p : E → ℝ} {l : Level E}
    (hp : Pair.Valid C p l) (hsub : D ⊆ C) (hD : Convex ℝ D) : Pair.Valid D p l :=
  ⟨hp.convex.subset hsub hD, hp.smoothness_pos, hp.lipschitz_nonneg,
    fun x hx y hy => hp.support x (hsub hx) y (hsub hy),
    fun x hx y hy => hp.monotone x (hsub hx) y (hsub hy),
    fun x hx y hy => hp.lipschitz x (hsub hx) y (hsub hy)⟩

private theorem operatorSum_monotone {D : Set E} {pairs : List (Pair E)}
    (hp : ∀ pair ∈ pairs, Pair.Valid D pair.1 pair.2) :
    ∀ x ∈ D, ∀ y ∈ D, 0 ≤ ⟪operatorSum pairs x - operatorSum pairs y, x - y⟫ := by
  induction pairs with
  | nil => simp [operatorSum]
  | cons pair tail ih =>
    rcases pair with ⟨p, l⟩
    intro x hx y hy
    have h := (hp (p, l) List.mem_cons_self).monotone x hx y hy
    have htail := ih (fun pair hm => hp pair (List.mem_cons_of_mem _ hm)) x hx y hy
    simp only [operatorSum, inner_sub_left, inner_add_left] at *
    linarith only [h, htail]

/-- (A.1) for a pass whose secant and outer radius checks have succeeded. -/
theorem scheduled_accepted_accuracy {C : Set E} (hC : Convex ℝ C)
    (p : ℕ → E → ℝ) (g Q : ℕ → E → E) (Λ M : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hΛ : ∀ i, δ ≤ Λ i) (hM : ∀ i, 0 ≤ M i)
    (hm : Monotone (fun i => scale δ (Λ i) (M i))) (n : ℕ)
    {s : E} (hs : s ∈ C) {R : ℝ} (hR : 0 < R) (P : Projection (region C s R))
    {out : Centers E} :
    let h := fun i => scale δ (Λ i) (M i)
    let pairs := scheduledPairs p g Q Λ M h 0 (n + 1)
    (∀ pair ∈ pairs, Pair.Valid C pair.1 pair.2) →
    (adaptivePass P pairs s).outcome = .ok out → ‖out.average - s‖ ≤ R / 2 →
    out.average ∈ C ∧ ∀ w ∈ C,
      gap (objective pairs) (operatorSum pairs) out.average w ≤ 3 * δ * ‖w - s‖ ^ 2 := by
  intro h pairs hp hout hradius
  have hD := hC.inter (convex_closedBall s R)
  have hl := adaptivePass_gap P pairs
    (fun pair hm => Pair.Valid.restrict (hp pair hm) inter_subset_left hD)
    ⟨hs, Metric.mem_closedBall_self hR.le⟩ hout
  have hz : out.average ∈ C := hl.1.1.1
  refine ⟨hz, global_gap_bound (convex_objective hC hp) (operatorSum_monotone hp)
    hz hR (by positivity) hradius ?_⟩
  intro w hw hdist
  have hh := hl.2 w ⟨hw, by simpa only [Metric.mem_closedBall, dist_eq_norm] using hdist⟩
  have he := scheduled_energy p g Q Λ M h w (fun _ => s) 0 (n + 1)
  simp only [enteringWeight, one_pow, one_mul, zero_add, ← Finset.sum_mul] at he
  change centerEnergy w (fun _ => s) pairs 0 1 = _ at he
  rw [he, norm_sub_rev s w] at hh
  have hb := (balance_and_accuracy hδ hΛ hM hm n).2
  refine hh.trans ?_
  have hprod := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖w - s‖)
  linarith only [hprod]

/-- Once the radius reaches twelve times the distance to a solution, a
completed pass cannot request another radius doubling. -/
theorem scheduled_radius_test {C : Set E} (hC : Convex ℝ C)
    (p : ℕ → E → ℝ) (g Q : ℕ → E → E) (Λ M : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hΛ : ∀ i, δ ≤ Λ i) (hM : ∀ i, 0 ≤ M i)
    (hm : Monotone (fun i => scale δ (Λ i) (M i))) (n : ℕ)
    {s w : E} (hs : s ∈ C) (hw : w ∈ C) {R : ℝ} (hR : 12 * ‖s - w‖ ≤ R)
    (P : Projection (region C s R)) {out : Centers E} :
    let h := fun i => scale δ (Λ i) (M i)
    let pairs := scheduledPairs p g Q Λ M h 0 (n + 1)
    (∀ pair ∈ pairs, Pair.Valid C pair.1 pair.2) →
    (∀ z ∈ C, 0 ≤ gap (objective pairs) (operatorSum pairs) z w) →
    (adaptivePass P pairs s).outcome = .ok out → ‖out.average - s‖ ≤ R / 2 := by
  intro h pairs hp hgap hout
  let tail := scheduledPairs p g Q Λ M h 1 n
  let l : Level E := ⟨g 0, Q 0, Λ 0, M 0, steps h 0 - 1⟩
  have hp' : ∀ pair ∈ (p 0, l) :: tail, Pair.Valid (region C s R) pair.1 pair.2 :=
    fun pair h => (hp pair h).restrict inter_subset_left (hC.inter (convex_closedBall s R))
  have hR₀ : 0 ≤ R := (mul_nonneg (by norm_num) (norm_nonneg _)).trans hR
  have hwR : w ∈ region C s R := by
    refine ⟨hw, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev w s]
    linarith only [hR, norm_nonneg (s - w)]
  let a := weight l.last
  have ha : 0 < a := weight_pos _
  have henergy := scheduled_energy p g Q Λ M h w (fun _ => s) 1 n
  change a ^ 2 * centerEnergy w (fun _ => s) tail 1 a =
    ∑ j ∈ Finset.range n, contribution (prefixWeight h (1 + j)) (Λ (1 + j)) (M (1 + j)) *
      ‖s - w‖ ^ 2 at henergy
  simp only [Nat.add_comm 1, ← Finset.sum_mul] at henergy
  have hroot : contribution (prefixWeight h 0) (Λ 0) (M 0) = a ^ 2 * regularization l 1 := by
    change a ^ 2 * Λ 0 + 2 * a * M 0 = a ^ 2 * (Λ 0 + 2 * M 0 / (1 * a))
    field_simp
  have htail := (balance_and_accuracy hδ hΛ hM hm n).1
  have hb : centerEnergy w (fun _ => s) tail 1 a ≤ regularization l 1 * ‖s - w‖ ^ 2 := by
    apply le_of_mul_le_mul_left _ (sq_pos_of_pos ha)
    rw [henergy, ← mul_assoc, ← hroot]
    exact mul_le_mul_of_nonneg_right htail (sq_nonneg _)
  have hrad := adaptivePass_radius P (hp' (p 0, l) List.mem_cons_self)
    (fun pair h => hp' pair (List.mem_cons_of_mem _ h))
    ⟨hs, Metric.mem_closedBall_self hR₀⟩ hwR
    (fun z hz => by rw [passGap_initial]; exact hgap z hz.1) hb hout
  have hsqrt : Real.sqrt (2 : ℝ) ≤ 3 / 2 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have HH := mul_le_mul_of_nonneg_right (show 1 + 3 * Real.sqrt 2 ≤ 6 by linarith)
    (norm_nonneg (s - w))
  exact hrad.trans (HH.trans (by linarith only [hR]))

/-- A rejected scheduled pass reports a component where the update at most
doubles the uniform secant cap for that component. -/
theorem scheduled_reject_bound {D : Set E} (P : Projection D) (p : ℕ → E → ℝ)
    (g Q : ℕ → E → E) (Λ M h L : ℕ → ℝ) (n : ℕ) {s : E} (hs : s ∈ D)
    (hp : ∀ pair ∈ scheduledPairs p g Q Λ M h 0 n, Pair.Valid D pair.1 pair.2)
    (hL : ∀ i, 0 ≤ L i)
    (hlip : ∀ i, ∀ x ∈ D, ∀ y ∈ D, ‖g i y - g i x‖ ≤ L i * ‖y - x‖)
    {req : Request} (hr : (adaptivePass P (scheduledPairs p g Q Λ M h 0 n) s).outcome =
      .error req) :
    req.level < n ∧ Λ req.level < req.threshold ∧
      max (2 * Λ req.level) req.threshold ≤ 4 * L req.level := by
  let pairs := scheduledPairs p g Q Λ M h 0 n
  obtain ⟨j, pair, x, y, hj, hindex, hx, hy, hfail, hτ⟩ :=
    runPass_error P pairs hp 0 PassFrame.initial (PassFrame.initial_valid D)
      (fun _ => s) (fun _ => hs) hr
  have hj' : j < n := by
    simpa [pairs, length_scheduledPairs] using (List.getElem?_eq_some_iff.mp hj).1
  have he : pair = (p j, ⟨g j, Q j, Λ j, M j, steps h j - 1⟩) := by
    rw [show pairs = _ from rfl, get_scheduledPairs p g Q Λ M h 0 n j hj', zero_add] at hj
    exact (Option.some.inj hj).symm
  have hrj : req.level = j := by simpa only [zero_add] using hindex
  rw [he] at hfail hτ
  change Λ j < req.threshold at hfail
  have hcheck : req.threshold ≤ 2 * L j := by
    rw [hτ]
    exact secant_le_of_lipschitz (hL j) (hlip j x hx y hy)
  rw [hrj]
  exact ⟨hj', hfail, max_le (by linarith only [hfail, hcheck]) (by linarith [hL j])⟩

private def enteringCalls (h : ℕ → ℝ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => prefixCalls h j

private theorem enteringCalls_next (h : ℕ → ℝ) (i : ℕ) :
    enteringCalls h i * steps h i = prefixCalls h i := by
  cases i with
  | zero => simp [enteringCalls, prefixCalls]
  | succ i => rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
private theorem scheduled_projection_budget (p : ℕ → E → ℝ) (g Q : ℕ → E → E)
    (Λ M : ℕ → ℝ) {h : ℕ → ℝ} (h₀ : 1 ≤ h 0) (hm : Monotone h) (i n : ℕ) :
    enteringCalls h i * projectionBudget (scheduledPairs p g Q Λ M h i n) =
      enteringCalls h (i + n) + ∑ j ∈ Finset.range n, prefixCalls h (i + j) := by
  induction n generalizing i with
  | zero => simp [scheduledPairs, projectionBudget]
  | succ n ih =>
    rw [scheduledPairs, projectionBudget, Nat.sub_add_cancel (steps_pos h₀ hm i),
      ← Nat.mul_assoc, enteringCalls_next, Nat.mul_add, Nat.mul_one, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    change enteringCalls h (i + 1) * _ + _ = _
    rw [ih]
    rw [show i + (n + 1) = i + 1 + n by omega]
    conv_lhs => rw [Nat.add_assoc]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [show i + (j + 1) = i + 1 + j by omega]

/-- A scheduled pass pays for one leaf per full prefix and one correction
per completed visit. An aborted pass uses at most the same budget. -/
theorem scheduled_attempt_projections {D : Set E} (P : Projection D) (p : ℕ → E → ℝ)
    (g Q : ℕ → E → E) (Λ M : ℕ → ℝ) {h : ℕ → ℝ} (h₀ : 1 ≤ h 0)
    (hm : Monotone h) (s : E) (n : ℕ) :
    (adaptivePass P (scheduledPairs p g Q Λ M h 0 (n + 1)) s).projections ≤
      prefixCalls h n + ∑ i ∈ Finset.range (n + 1), prefixCalls h i := by
  have hb := runPass_projections_le P (scheduledPairs p g Q Λ M h 0 (n + 1))
    0 PassFrame.initial (fun _ => s)
  have he := scheduled_projection_budget p g Q Λ M h₀ hm 0 (n + 1)
  simp only [enteringCalls, Nat.zero_add, one_mul] at he
  have hn : Nat.add 0 n = n := Nat.zero_add n
  rw [hn] at he
  exact hb.trans_eq he

end

end LeanLab.Sliding.PathA
