module

public import LeanLab.Common.SymmetricSmoothness
public import LeanLab.PathA.Guarantees

set_option linter.style.header false

/-!
# Restart budget of path A

A failed attempt updates one positive parameter. The radius and the
original component curvatures are coordinates of the parameter vector.
The trace includes the parameters for every attempted pass.
-/

@[expose] public section

namespace LeanLab.Sliding.PathA

noncomputable section

variable {ι A : Type*}

inductive Decision (ι A : Type*)
  | accept (out : A)
  | increase (index : ι) (threshold : ℝ)

structure SearchResult (ι A : Type*) where
  outcome : Option ((ι → ℝ) × A)
  attempts : List (ι → ℝ)

def increase [DecidableEq ι] (a : ι → ℝ) (i : ι) (τ : ℝ) : ι → ℝ :=
  Function.update a i (max (2 * a i) τ)

def restart [DecidableEq ι] (attempt : (ι → ℝ) → Decision ι A) :
    ℕ → (ι → ℝ) → SearchResult ι A
  | 0, _ => ⟨none, []⟩
  | n + 1, a =>
    match attempt a with
    | .accept out => ⟨some (a, out), [a]⟩
    | .increase i τ =>
      let next := restart attempt n (increase a i τ)
      ⟨next.outcome, a :: next.attempts⟩

def remaining [Fintype ι] (cap a : ι → ℝ) : ℕ :=
  ∑ i, ⌊Real.logb 2 (cap i / a i)⌋₊

private theorem increase_mono [DecidableEq ι] {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (j : ι) (τ : ℝ) : ∀ i, a i ≤ increase a j τ i := by
  intro i
  by_cases he : i = j
  · subst i
    simpa only [increase, Function.update_self] using
      (show a j ≤ max (2 * a j) τ from (by linarith [ha j] : a j ≤ 2 * a j).trans (le_max_left ..))
  · simp [increase, Function.update_of_ne he]

private theorem increase_bounded [DecidableEq ι] {a cap : ι → ℝ}
    (ha : ∀ i, a i ≤ cap i) {j : ι} {τ : ℝ} (hj : max (2 * a j) τ ≤ cap j) :
    ∀ i, increase a j τ i ≤ cap i := by
  intro i
  by_cases he : i = j
  · subst i
    simpa only [increase, Function.update_self] using hj
  · simpa only [increase, Function.update_of_ne he] using ha i

private theorem remaining_decreases [Fintype ι] [DecidableEq ι] {a cap : ι → ℝ}
    (ha : ∀ i, 0 < a i) {j : ι} {τ : ℝ} (hj : max (2 * a j) τ ≤ cap j) :
    remaining cap (increase a j τ) < remaining cap a := by
  let b := max (2 * a j) τ
  have hb : 0 < b := (mul_pos (by norm_num) (ha j)).trans_le (le_max_left ..)
  have hcap : 0 < cap j := hb.trans_le hj
  have htwo : 1 < (2 : ℝ) := by norm_num
  have hlog := Real.logb_le_logb_of_le htwo (mul_pos (by norm_num) (ha j))
    (le_max_left (2 * a j) τ)
  rw [Real.logb_mul (by norm_num) (ha j).ne', Real.logb_self_eq_one htwo] at hlog
  have hratio : 0 ≤ Real.logb 2 (cap j / b) :=
    Real.logb_nonneg htwo ((one_le_div hb).mpr hj)
  have hfloor :
      ⌊Real.logb 2 (cap j / b)⌋₊ + 1 ≤ ⌊Real.logb 2 (cap j / a j)⌋₊ := by
    rw [← Nat.floor_add_one hratio]
    apply Nat.floor_mono
    rw [Real.logb_div hcap.ne' hb.ne', Real.logb_div hcap.ne' (ha j).ne']
    linarith only [hlog]
  unfold remaining
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  have hrest :
      (∑ i ∈ Finset.univ.erase j, ⌊Real.logb 2 (cap i / increase a j τ i)⌋₊) =
        ∑ i ∈ Finset.univ.erase j, ⌊Real.logb 2 (cap i / a i)⌋₊ := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [increase, (Finset.mem_erase.mp hi).1]
  rw [hrest, increase, Function.update_self]
  dsimp only [b] at hfloor
  omega

/-- The exact logarithmic budget (A.8) for a bounded restart controller.
Every recorded attempt uses parameters bounded by those of the successful pass. -/
theorem restart_success [Fintype ι] [DecidableEq ι]
    (attempt : (ι → ℝ) → Decision ι A) {base cap : ι → ℝ}
    (hstep : ∀ a, (∀ i, base i ≤ a i) → (∀ i, 0 < a i) → (∀ i, a i ≤ cap i) →
      ∀ {j τ}, attempt a = .increase j τ → max (2 * a j) τ ≤ cap j)
    (fuel : ℕ) {a : ι → ℝ} (hbase : ∀ i, base i ≤ a i)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, a i ≤ cap i)
    (hf : remaining cap a < fuel) :
    ∃ (b : ι → ℝ) (out : A), (restart attempt fuel a).outcome = some (b, out) ∧
      attempt b = .accept out ∧ (restart attempt fuel a).attempts.length ≤ fuel ∧
      (∀ i, 0 < b i) ∧ (∀ i, b i ≤ cap i) ∧ (∀ i, a i ≤ b i) ∧
      ∀ v ∈ (restart attempt fuel a).attempts, ∀ i, a i ≤ v i ∧ v i ≤ b i := by
  induction fuel generalizing a with
  | zero => omega
  | succ n ih =>
    cases h : attempt a with
    | accept out =>
      refine ⟨a, out, by simp [restart, h], h, by simp [restart, h], ha, hb, fun _ => le_rfl, ?_⟩
      simp [restart, h]
    | increase j τ =>
      let a' := increase a j τ
      have hcap := hstep a hbase ha hb h
      have hmono := increase_mono ha j τ
      have ha' : ∀ i, 0 < a' i := fun i => (ha i).trans_le (hmono i)
      have hb' : ∀ i, a' i ≤ cap i := increase_bounded hb hcap
      have hdec : remaining cap a' < remaining cap a := remaining_decreases ha hcap
      have hf' : remaining cap a' < n := by omega
      obtain ⟨b, out, hout, haccept, hn, hpb, hbb, hab, hv⟩ :=
        ih (fun i => (hbase i).trans (hmono i)) ha' hb' hf'
      refine ⟨b, out, by simpa only [restart, h] using hout, haccept,
        by simpa only [restart, h, List.length_cons] using Nat.succ_le_succ hn,
        hpb, hbb, fun i => (hmono i).trans (hab i), ?_⟩
      intro v hm i
      simp only [restart, h, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact ⟨le_rfl, (hmono i).trans (hab i)⟩
      · exact ⟨(hmono i).trans (hv v hm i).1, (hv v hm i).2⟩

/-- Sum any per-attempt oracle count, including the costs of failed attempts. -/
theorem sum_attempt_cost_le (attempts : List (ι → ℝ)) (cost : (ι → ℝ) → ℝ)
    {B : ℝ} (h : ∀ a ∈ attempts, cost a ≤ B) :
    (attempts.map cost).sum ≤ attempts.length * B := by
  induction attempts with
  | nil => simp
  | cons a tail ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
    linarith only [ha, ht]

open Set
open TwoLevel (Projection)
open Localized (Level Oracle region)
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original numbering of the pairs never changes across restarts. -/
structure Family (E : Type*) (n : ℕ) where
  value : Fin n → E → ℝ
  gradient : Fin n → E → E
  operator : Fin n → E → E
  lipschitz : Fin n → ℝ

def Family.Valid {n : ℕ} (F : Family E n) (C : Set E) : Prop :=
  ∀ i, Pair.Valid C (F.value i) ⟨F.gradient i, F.operator i, 1, F.lipschitz i, 0⟩

abbrev Parameters (n : ℕ) := Option (Fin n) → ℝ

def initialParameters {n : ℕ} (δ R : ℝ) (Λ : Fin n → ℝ) : Parameters n
  | none => R
  | some i => max δ (Λ i)

def parameterCaps {n : ℕ} (a : Parameters n) (r : ℝ) (L : Fin n → ℝ) : Parameters n
  | none => max (a none) (24 * r)
  | some i => max (a (some i)) (4 * L i)

def clipped (n i : ℕ) : Fin (n + 1) := ⟨min i n, Nat.lt_succ_of_le (min_le_right ..)⟩

def Family.order {n : ℕ} (F : Family E n) (δ : ℝ) (a : Parameters n) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => scale δ (a (some i)) (F.lipschitz i))

def Family.orig {n : ℕ} (F : Family E (n + 1)) (δ : ℝ) (a : Parameters (n + 1))
    (i : ℕ) : Fin (n + 1) := F.order δ a (clipped n i)

def Family.pairs {n : ℕ} (F : Family E (n + 1)) (δ : ℝ) (a : Parameters (n + 1)) :
    List (Pair E) :=
  let o := F.orig δ a
  scheduledPairs (F.value ∘ o) (F.gradient ∘ o) (F.operator ∘ o)
    (fun i => a (some (o i))) (F.lipschitz ∘ o)
    (fun i => scale δ (a (some (o i))) (F.lipschitz (o i))) 0 (n + 1)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
private theorem Family.order_mono {n : ℕ} (F : Family E (n + 1)) (δ : ℝ) (a : Parameters (n + 1)) :
    Monotone (fun i => scale δ (a (some (F.orig δ a i))) (F.lipschitz (F.orig δ a i))) :=
  (Tuple.monotone_sort (fun i => scale δ (a (some i)) (F.lipschitz i))).comp
    (fun _ _ h => min_le_min_right n h)

private theorem Family.pairs_valid {n : ℕ} {F : Family E (n + 1)} {C : Set E} (h : F.Valid C)
    (δ : ℝ) {a : Parameters (n + 1)} (ha : ∀ i, 0 < a i) :
    ∀ pair ∈ F.pairs δ a, Pair.Valid C pair.1 pair.2 := by
  intro pair hpair
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hpair
  have hi' : i < n + 1 := by
    simpa [Family.pairs, length_scheduledPairs] using (List.getElem?_eq_some_iff.mp hi).1
  dsimp only [Family.pairs] at hi
  rw [get_scheduledPairs _ _ _ _ _ _ _ _ _ hi', zero_add] at hi
  cases Option.some.inj hi
  let j := F.orig δ a i
  exact ⟨(h j).convex, ha _, (h j).lipschitz_nonneg, (h j).support, (h j).monotone, (h j).lipschitz⟩

private theorem scheduled_sum {E : Type*} {B : Type*} [AddCommMonoid B]
    (p : ℕ → E → ℝ) (g Q : ℕ → E → E) (Λ M h : ℕ → ℝ)
    (eval : Pair E → B) (i n : ℕ) :
    ((scheduledPairs p g Q Λ M h i n).map eval).sum =
      ∑ j ∈ Finset.range n, eval (p (i + j),
        ⟨g (i + j), Q (i + j), Λ (i + j), M (i + j), steps h (i + j) - 1⟩) := by
  induction n generalizing i with
  | zero => simp [scheduledPairs]
  | succ n ih =>
    rw [scheduledPairs, List.map_cons, List.sum_cons, ih, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [show i + (j + 1) = i + 1 + j by omega]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
private theorem Family.pairs_sum {n : ℕ} (F : Family E (n + 1)) (δ : ℝ)
    (a : Parameters (n + 1)) {B : Type*} [AddCommMonoid B]
    (eval : (E → ℝ) → (E → E) → B) :
    ((F.pairs δ a).map (fun pair => eval pair.1 pair.2.operator)).sum =
      ∑ i, eval (F.value i) (F.operator i) := by
  unfold Family.pairs
  rw [scheduled_sum]
  simp only [zero_add, Function.comp_apply]
  rw [← Fin.sum_univ_eq_sum_range]
  have he (i : Fin (n + 1)) : clipped n i = i := by
    apply Fin.ext
    exact min_eq_left (Nat.le_of_lt_succ i.isLt)
  simp only [Family.orig, he]
  exact Equiv.sum_comp (F.order δ a) (fun i => eval (F.value i) (F.operator i))

private theorem Family.pairs_gap {n : ℕ} (F : Family E (n + 1)) (δ : ℝ)
    (a : Parameters (n + 1)) (z w : E) :
    gap (objective (F.pairs δ a)) (operatorSum (F.pairs δ a)) z w =
      gap (fun t => ∑ i, F.value i t) (fun t => ∑ i, F.operator i t) z w := by
  have hp (t : E) (pairs : List (Pair E)) :
      objective pairs t = (pairs.map (fun pair => pair.1 t)).sum := by
    induction pairs with
    | nil => rfl
    | cons pair tail ih => cases pair; simp [objective, ih]
  have hq (t : E) (pairs : List (Pair E)) :
      operatorSum pairs t = (pairs.map (fun pair => pair.2.operator t)).sum := by
    induction pairs with
    | nil => rfl
    | cons pair tail ih => cases pair; simp [operatorSum, ih]
  simp only [gap, hp, hq]
  rw [F.pairs_sum δ a (fun p _ => p z), F.pairs_sum δ a (fun p _ => p w),
    F.pairs_sum δ a (fun _ Q => Q w)]

/-- Attempt once using the sorted scale. A request is translated back to
the original index before updating the curvature. -/
def Family.attempt {n : ℕ} (F : Family E (n + 1)) (δ : ℝ) {C : Set E} (s : E)
    (project : ∀ R, 0 < R → Projection (region C s R))
    (a : Parameters (n + 1)) : Decision (Option (Fin (n + 1))) E :=
  if h : 0 < a none then
    let attempt := adaptivePass (project (a none) h) (F.pairs δ a) s
    match attempt.outcome with
    | .error req => .increase (some (F.orig δ a req.level)) req.threshold
    | .ok out =>
      if ‖out.average - s‖ ≤ a none / 2 then .accept out.average else .increase none 0
  else .increase none 0

def Family.attemptCalls {n : ℕ} (F : Family E (n + 1)) (δ : ℝ) {C : Set E} (s : E)
    (project : ∀ R, 0 < R → Projection (region C s R))
    (a : Parameters (n + 1)) (i : Fin (n + 1)) (o : Oracle) : ℕ :=
  if h : 0 < a none then
    (adaptivePass (project (a none) h) (F.pairs δ a) s).calls ((F.order δ a).symm i) o
  else 0

private theorem Family.attemptCalls_le {n : ℕ} (F : Family E (n + 1)) (δ : ℝ) (hδ : 0 < δ)
    {C : Set E} (s : E) (project : ∀ R, 0 < R → Projection (region C s R))
    {a : Parameters (n + 1)} (ha : ∀ i, 0 < a i) (hΛ : ∀ i, δ ≤ a (some i))
    (i : Fin (n + 1)) (o : Oracle) :
    (F.attemptCalls δ s project a i o : ℝ) ≤ 6 * 17 ^ n * scale δ (a (some i)) (F.lipschitz i) := by
  let j := (F.order δ a).symm i
  let o' := F.orig δ a
  have hr : o' j = i := by
    have he : clipped n j = j := Fin.ext (min_eq_left (Nat.le_of_lt_succ j.isLt))
    unfold o' Family.orig
    rw [he]
    exact (F.order δ a).apply_symm_apply i
  let h := fun i => scale δ (a (some (o' i))) (F.lipschitz (o' i))
  have h₀ : 1 ≤ h 0 := by
    apply le_max_of_le_left
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ((le_div_iff₀ hδ).mpr (by simpa using hΛ (o' 0)))
  have hh := scheduled_attempt_calls (project (a none) (ha none)) (F.value ∘ o')
    (F.gradient ∘ o') (F.operator ∘ o') (fun k => a (some (o' k))) (F.lipschitz ∘ o')
    (h := h) h₀ (F.order_mono δ a) s j.isLt o
  simp only [Family.attemptCalls, dite_eq_left (ha none)]
  refine hh.trans ?_
  change 6 * 17 ^ (j : ℕ) * scale δ (a (some (o' j))) (F.lipschitz (o' j)) ≤ _
  rw [hr]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt_succ j.isLt))
      (by norm_num)) (le_trans (Real.sqrt_nonneg _) (le_max_left ..))

private theorem Family.attempt_bounded {n : ℕ} (F : Family E (n + 1)) {C : Set E}
    (hC : Convex ℝ C) (hvalid : F.Valid C) {s w : E} (hs : s ∈ C) (hw : w ∈ C)
    (hsol : ∀ z ∈ C, 0 ≤ gap (fun t => ∑ i, F.value i t) (fun t => ∑ i, F.operator i t) z w)
    (project : ∀ R, 0 < R → Projection (region C s R)) {δ : ℝ} (hδ : 0 < δ)
    (base : Parameters (n + 1)) (L : Fin (n + 1) → ℝ) (hL : ∀ i, 0 ≤ L i)
    (hlip : ∀ i, ∀ x ∈ region C s (max (base none) (24 * ‖s - w‖)),
      ∀ y ∈ region C s (max (base none) (24 * ‖s - w‖)),
        ‖F.gradient i y - F.gradient i x‖ ≤ L i * ‖y - x‖)
    {a : Parameters (n + 1)} (ha : ∀ j, 0 < a j) (hΛ : ∀ i, δ ≤ a (some i))
    (hc : ∀ j, a j ≤ parameterCaps base ‖s - w‖ L j)
    {j τ} (he : F.attempt δ s project a = .increase j τ) :
    max (2 * a j) τ ≤ parameterCaps base ‖s - w‖ L j := by
  let o := F.orig δ a
  let P := project (a none) (ha none)
  let D := region C s (a none)
  have hD : Convex ℝ D := hC.inter (convex_closedBall _ _)
  have hsD : s ∈ D := ⟨hs, Metric.mem_closedBall_self (ha none).le⟩
  have hsub : D ⊆ region C s (max (base none) (24 * ‖s - w‖)) := by
    intro x hx
    exact ⟨hx.1, Metric.closedBall_subset_closedBall (hc none) hx.2⟩
  have hp := F.pairs_valid hvalid δ ha
  have hm := F.order_mono δ a
  simp only [Family.attempt, dite_eq_left (ha none)] at he
  split at he
  · rename_i req hreq
    injection he with hindex hthreshold
    rw [← hindex, ← hthreshold]
    have hcheck := scheduled_reject_bound P (F.value ∘ o) (F.gradient ∘ o) (F.operator ∘ o)
      (fun i => a (some (o i))) (F.lipschitz ∘ o)
      (fun i => scale δ (a (some (o i))) (F.lipschitz (o i))) (L ∘ o) (n + 1) hsD
      (fun pair h => (hp pair h).restrict inter_subset_left hD)
      (fun i => hL (o i)) (fun i x hx y hy => hlip (o i) x (hsub hx) y (hsub hy)) hreq
    exact hcheck.2.2.trans (le_max_right ..)
  · rename_i out hout
    split at he
    · contradiction
    · rename_i hrad
      injection he with hindex hthreshold
      rw [← hindex, ← hthreshold]
      have hr : a none < 12 * ‖s - w‖ := by
        by_contra! hb
        apply hrad
        exact scheduled_radius_test hC (F.value ∘ o) (F.gradient ∘ o) (F.operator ∘ o)
          (fun i => a (some (o i))) (F.lipschitz ∘ o) hδ
          (fun _ => hΛ _) (fun _ => (hvalid _).lipschitz_nonneg) hm n hs hw hb P hp
          (fun z hz => (F.pairs_gap δ a z w).symm ▸ hsol z hz) hout
      apply max_le
      · exact (show 2 * a none ≤ 24 * ‖s - w‖ by linarith).trans (le_max_right ..)
      · exact (ha none).le.trans (hc none)

private theorem Family.attempt_accuracy {n : ℕ} (F : Family E (n + 1)) {C : Set E}
    (hC : Convex ℝ C) (hvalid : F.Valid C) {s : E} (hs : s ∈ C)
    (project : ∀ R, 0 < R → Projection (region C s R)) {δ : ℝ} (hδ : 0 < δ)
    {a : Parameters (n + 1)} (ha : ∀ j, 0 < a j) (hΛ : ∀ i, δ ≤ a (some i))
    {z : E} (he : F.attempt δ s project a = .accept z) :
    z ∈ C ∧ ∀ w ∈ C, gap (fun t => ∑ i, F.value i t) (fun t => ∑ i, F.operator i t) z w ≤
      3 * δ * ‖w - s‖ ^ 2 := by
  let o := F.orig δ a
  let P := project (a none) (ha none)
  simp only [Family.attempt, dite_eq_left (ha none)] at he
  split at he
  · contradiction
  · rename_i out hout
    split at he
    · rename_i hrad
      cases Decision.accept.inj he
      have hh := scheduled_accepted_accuracy hC (F.value ∘ o) (F.gradient ∘ o)
        (F.operator ∘ o) (fun i => a (some (o i))) (F.lipschitz ∘ o) hδ
        (fun _ => hΛ _) (fun _ => (hvalid _).lipschitz_nonneg) (F.order_mono δ a) n
        hs (ha none) P (F.pairs_valid hvalid δ ha) hout hrad
      exact ⟨hh.1, fun w hw => (F.pairs_gap δ a _ w) ▸ hh.2 w hw⟩
    · contradiction

private theorem scale_mono_curvature {δ a b M : ℝ} (hδ : 0 < δ) (h : a ≤ b) :
    scale δ a M ≤ scale δ b M :=
  max_le_max (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right h hδ.le)) le_rfl

/-- Count the projections performed by the leaf solver and by corrections. -/
def Family.attemptProjections {n : ℕ} (F : Family E (n + 1)) (δ : ℝ) {C : Set E} (s : E)
    (project : ∀ R, 0 < R → Projection (region C s R)) (a : Parameters (n + 1)) : ℕ :=
  if h : 0 < a none then (adaptivePass (project (a none) h) (F.pairs δ a) s).projections
  else 0

private theorem Family.attemptProjections_le {n : ℕ} (F : Family E (n + 1)) (δ : ℝ) (hδ : 0 < δ)
    {C : Set E} (s : E) (project : ∀ R, 0 < R → Projection (region C s R))
    {a : Parameters (n + 1)} (ha : ∀ i, 0 < a i) (hΛ : ∀ i, δ ≤ a (some i)) {H : ℝ}
    (hH : ∀ i, scale δ (a (some i)) (F.lipschitz i) ≤ H) :
    (F.attemptProjections δ s project a : ℝ) ≤
      3 * 17 ^ n * (H + ∑ i, scale δ (a (some i)) (F.lipschitz i)) := by
  let o := F.orig δ a
  let h := fun i => scale δ (a (some (o i))) (F.lipschitz (o i))
  have h₀ : 1 ≤ h 0 := by
    apply le_max_of_le_left
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ((le_div_iff₀ hδ).mpr (by simpa using hΛ (o 0)))
  have hsum : ∑ j ∈ Finset.range (n + 1), h j = ∑ i, scale δ (a (some i)) (F.lipschitz i) := by
    rw [← Fin.sum_univ_eq_sum_range]
    have he (i : Fin (n + 1)) : clipped n i = i :=
      Fin.ext (min_eq_left (Nat.le_of_lt_succ i.isLt))
    simp only [h, o, Family.orig, he]
    exact Equiv.sum_comp (F.order δ a) (fun i => scale δ (a (some i)) (F.lipschitz i))
  have hco (i : ℕ) (hi : i ≤ n) : (prefixCalls h i : ℝ) ≤ 3 * 17 ^ n * h i :=
    (prefix_calls_le h₀ (F.order_mono δ a) i).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hi) (by norm_num))
        ((Real.sqrt_nonneg _).trans (le_max_left ..)))
  have hproj := scheduled_attempt_projections (project (a none) (ha none)) (F.value ∘ o)
    (F.gradient ∘ o) (F.operator ∘ o) (fun j => a (some (o j))) (F.lipschitz ∘ o)
    (h := h) h₀ (F.order_mono δ a) s n
  simp only [Family.attemptProjections, dite_eq_left (ha none)]
  refine (Nat.cast_le.mpr hproj).trans ?_
  rw [Nat.cast_add, Nat.cast_sum, ← hsum, mul_add, Finset.mul_sum]
  exact add_le_add ((hco n le_rfl).trans (mul_le_mul_of_nonneg_left (hH (o n)) (by positivity)))
    (Finset.sum_le_sum fun j hj => hco j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))

/-- Path A terminates within (A.8), attains (A.1), and satisfies (A.9) for
both oracles at each original component index. The cap is only used to
prove that a finite prefix of the adaptive search succeeds. -/
theorem Family.pathA {n : ℕ} (F : Family E (n + 1)) {C : Set E} (hC : Convex ℝ C)
    (hvalid : F.Valid C) {s w : E} (hs : s ∈ C) (hw : w ∈ C)
    (hsol : ∀ z ∈ C, 0 ≤ gap (fun t => ∑ i, F.value i t) (fun t => ∑ i, F.operator i t) z w)
    (project : ∀ R, 0 < R → Projection (region C s R))
    {ε R₀ : ℝ} (hε : 0 < ε) (hR₀ : 0 < R₀) (Λ₀ L : Fin (n + 1) → ℝ)
    (hL : ∀ i, 0 ≤ L i)
    (hlip : ∀ i, ∀ x ∈ region C s (max R₀ (24 * ‖s - w‖)),
      ∀ y ∈ region C s (max R₀ (24 * ‖s - w‖)),
        ‖F.gradient i y - F.gradient i x‖ ≤ L i * ‖y - x‖) :
    let δ := ε / 3
    let a := initialParameters δ R₀ Λ₀
    let cap := parameterCaps a ‖s - w‖ L
    let B := remaining cap a + 1
    let result := restart (F.attempt δ s project) B a
    ∃ (b : Parameters (n + 1)) (z : E), result.outcome = some (b, z) ∧ z ∈ C ∧
      (∀ i, a i ≤ b i ∧ b i ≤ cap i) ∧ result.attempts.length ≤ B ∧
      (∀ v ∈ C, gap (fun t => ∑ i, F.value i t) (fun t => ∑ i, F.operator i t) z v ≤
        ε * ‖v - s‖ ^ 2) ∧
      (∀ (i : Fin (n + 1)) (o : Oracle),
        (result.attempts.map (fun v => (F.attemptCalls δ s project v i o : ℝ))).sum ≤
          6 * 17 ^ n * result.attempts.length * scale δ (b (some i)) (F.lipschitz i)) ∧
      ∀ H : ℝ, (∀ i, scale δ (b (some i)) (F.lipschitz i) ≤ H) →
        (result.attempts.map (fun v => (F.attemptProjections δ s project v : ℝ))).sum ≤
          3 * 17 ^ n * result.attempts.length *
            (H + ∑ i, scale δ (b (some i)) (F.lipschitz i)) := by
  dsimp only
  let δ := ε / 3
  let a := initialParameters δ R₀ Λ₀
  let cap := parameterCaps a ‖s - w‖ L
  let B := remaining cap a + 1
  let attempt := F.attempt δ s project
  let result := restart attempt B a
  have hδ : 0 < δ := by positivity
  have hpos : ∀ i, 0 < a i := by
    intro i
    cases i with
    | none => exact hR₀
    | some j => exact hδ.trans_le (le_max_left ..)
  have hcap : ∀ i, a i ≤ cap i := fun i => by cases i <;> exact le_max_left ..
  have hinvariant (v : Parameters (n + 1)) (h : ∀ i, a i ≤ v i) (i : Fin (n + 1)) :
      δ ≤ v (some i) := (le_max_left ..).trans (h (some i))
  have hstep (v : Parameters (n + 1)) (hv : ∀ i, a i ≤ v i) (hvp : ∀ i, 0 < v i)
      (hvc : ∀ i, v i ≤ cap i) {j τ} (he : attempt v = .increase j τ) :
      max (2 * v j) τ ≤ cap j :=
    F.attempt_bounded hC hvalid hs hw hsol project hδ a L hL hlip hvp (hinvariant v hv) hvc he
  obtain ⟨b, z, hout, haccept, hlen, hbpos, hbcap, hab, htrace⟩ :=
    restart_success attempt hstep B (fun _ => le_rfl) hpos hcap (Nat.lt_succ_self _)
  have hg := F.attempt_accuracy hC hvalid hs project hδ hbpos (hinvariant b hab) haccept
  refine ⟨b, z, hout, hg.1, fun i => ⟨hab i, hbcap i⟩, hlen, ?_, ?_, ?_⟩
  · intro v hv
    refine (hg.2 v hv).trans_eq ?_
    dsimp only [δ]
    ring
  · intro i o
    let K := 6 * 17 ^ n * scale δ (b (some i)) (F.lipschitz i)
    have hcost (v : Parameters (n + 1)) (hv : v ∈ result.attempts) :
        (F.attemptCalls δ s project v i o : ℝ) ≤ K := by
      have hlo (j : Option (Fin (n + 1))) := (htrace v hv j).1
      have hpositive (j : Option (Fin (n + 1))) := (hpos j).trans_le (hlo j)
      refine (F.attemptCalls_le δ hδ s project hpositive (hinvariant v hlo) i o).trans ?_
      exact mul_le_mul_of_nonneg_left (scale_mono_curvature hδ (htrace v hv (some i)).2)
        (by positivity)
    refine (sum_attempt_cost_le result.attempts _ hcost).trans_eq ?_
    dsimp only [K]
    ring
  · intro H hH
    let K := 3 * 17 ^ n * (H + ∑ i, scale δ (b (some i)) (F.lipschitz i))
    have hcost (v : Parameters (n + 1)) (hv : v ∈ result.attempts) :
        (F.attemptProjections δ s project v : ℝ) ≤ K := by
      have hlo (j : Option (Fin (n + 1))) := (htrace v hv j).1
      have hpositive (j : Option (Fin (n + 1))) := (hpos j).trans_le (hlo j)
      have hmono (i : Fin (n + 1)) :=
        scale_mono_curvature (M := F.lipschitz i) hδ (htrace v hv (some i)).2
      refine (F.attemptProjections_le δ hδ s project hpositive (hinvariant v hlo)
        (fun i => (hmono i).trans (hH i))).trans ?_
      exact mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (Finset.sum_le_sum fun i _ => hmono i)) (by positivity)
    refine (sum_attempt_cost_le result.attempts _ hcost).trans_eq ?_
    dsimp only [K]
    ring

/-- The radius contributes one summand and each original component contributes
one summand to the logarithmic budget. -/
theorem parameter_remaining {n : ℕ} (cap a : Parameters n) :
    remaining cap a = ⌊Real.logb 2 (cap none / a none)⌋₊ +
      ∑ i : Fin n, ⌊Real.logb 2 (cap (some i) / a (some i))⌋₊ := by
  rw [remaining, Fintype.sum_option]

/-- The original variational inequality implies the nonnegative comparison
gap used to control every successful prefix. -/
theorem Family.solution_gap {n : ℕ} {F : Family E n} {C : Set E} (hF : F.Valid C)
    {w : E} (hw : w ∈ C)
    (hvi : ∀ z ∈ C, 0 ≤
      ⟪(∑ i, F.gradient i w) + (∑ i, F.operator i w), z - w⟫) :
    ∀ z ∈ C, 0 ≤ gap (fun t => ∑ i, F.value i t) (fun t => ∑ i, F.operator i t) z w := by
  intro z hz
  have hsum : (∑ i, (F.value i w + ⟪F.gradient i w, z - w⟫)) ≤ ∑ i, F.value i z :=
    Finset.sum_le_sum fun i _ => (hF i).support w hw z hz
  rw [Finset.sum_add_distrib, ← sum_inner] at hsum
  have h := hvi z hz
  rw [inner_add_left] at h
  unfold gap
  linarith only [hsum, h]

/-- The coefficients \(A_i(R)\) from the manuscript, used solely in the
proof of termination. -/
def Family.smoothCaps {n : ℕ} (F : Family E n) (L₀ L₁ : Fin n → ℝ)
    (C : Set E) (s : E) (R : ℝ) (i : Fin n) : ℝ :=
  sSup ((fun z => L₀ i + L₁ i * ‖F.gradient i z‖) '' region C s R)

/-- In a proper space (in particular, finite-dimensional Euclidean space),
symmetric generalized smoothness gives the analytic caps used in path A. -/
theorem Family.smoothCaps_spec [ProperSpace E] {n : ℕ} (F : Family E n)
    {C : Set E} (hclosed : IsClosed C) (hC : Convex ℝ C)
    (L₀ L₁ : Fin n → ℝ)
    (hF : ∀ i, SymmetricSmoothOn C (F.gradient i) (L₀ i) (L₁ i))
    {s : E} (hs : s ∈ C) {R : ℝ} (hR : 0 ≤ R) (i : Fin n) :
    0 ≤ F.smoothCaps L₀ L₁ C s R i ∧
      ∀ x ∈ region C s R, ∀ y ∈ region C s R,
        ‖F.gradient i y - F.gradient i x‖ ≤ F.smoothCaps L₀ L₁ C s R i * ‖y - x‖ := by
  have hD : IsCompact (region C s R) :=
    (isCompact_closedBall s R).of_isClosed_subset
      (hclosed.inter Metric.isClosed_closedBall) inter_subset_right
  have hc : ContinuousOn (fun z => L₀ i + L₁ i * ‖F.gradient i z‖) (region C s R) :=
    continuousOn_const.add
      (continuousOn_const.mul ((hF i).continuousOn.mono inter_subset_left).norm)
  have hcompact := hD.image_of_continuousOn hc
  have hbound (z : E) (hz : z ∈ region C s R) :
      L₀ i + L₁ i * ‖F.gradient i z‖ ≤ F.smoothCaps L₀ L₁ C s R i :=
    le_csSup hcompact.bddAbove ⟨z, hz, rfl⟩
  have hsD : s ∈ region C s R := ⟨hs, Metric.mem_closedBall_self hR⟩
  refine ⟨(add_nonneg (hF i).zero_nonneg
    (mul_nonneg (hF i).one_nonneg (norm_nonneg _))).trans (hbound s hsD), ?_⟩
  intro x hx y hy
  have hseg := (hC.inter (convex_closedBall s R)).segment_subset hx hy
  exact (hF i).norm_sub_le hx.1 hy.1 (hseg.trans inter_subset_left)
    (fun z hz => hbound z (hseg hz))

/-- Differentiability and convexity give the supporting planes consumed by
the checked pass. -/
theorem Family.valid_of_gradient [CompleteSpace E] {n : ℕ} {F : Family E n}
    {C : Set E} (hp : ∀ i, ConvexOn ℝ C (F.value i))
    (hg : ∀ i, ∀ x ∈ C, HasGradientWithinAt (F.value i) (F.gradient i x) C x)
    (hQ : ∀ i, TwoLevel.MonotoneLipschitz C (F.operator i) (F.lipschitz i)) : F.Valid C := by
  intro i
  refine ⟨hp i, zero_lt_one, (hQ i).nonneg, ?_,
    fun _ hx _ hy => (hQ i).monotone hx hy,
    fun _ hx _ hy => (hQ i).lipschitz hx hy⟩
  intro x hx y hy
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hmaps : MapsTo line (Icc 0 1) C := (hp i).1.mapsTo_lineMap hx hy
  have hconv := ((hp i).comp_affineMap line).subset hmaps (convex_Icc 0 1)
  have hzero : line 0 = x := AffineMap.lineMap_apply_zero ..
  have hd : HasDerivWithinAt (F.value i ∘ line) ⟪F.gradient i x, y - x⟫ (Icc 0 1) 0 := by
    have hgrad := (hg i x hx).hasFDerivWithinAt
    rw [← hzero] at hgrad
    simpa only [InnerProductSpace.toDual_apply_apply, hzero] using
      hgrad.comp_hasDerivWithinAt 0 AffineMap.hasDerivWithinAt_lineMap hmaps
  have h := hconv.le_slope_of_hasDerivWithinAt (by simp) (by simp) zero_lt_one hd
  have hh : ⟪F.gradient i x, y - x⟫ ≤ F.value i y - F.value i x := by
    simpa [slope_def_field, line] using h
  linarith only [hh]

/-- Path A under symmetric generalized smoothness and the usual variational
inequality hypotheses. The compact-ball caps and the solution are used only
to bound the length of the successful search prefix. -/
theorem Family.pathA_of_symmetric [ProperSpace E] [CompleteSpace E] {n : ℕ}
    (F : Family E (n + 1)) {C : Set E} (hclosed : IsClosed C) (hC : Convex ℝ C)
    (hp : ∀ i, ConvexOn ℝ C (F.value i))
    (hg : ∀ i, ∀ x ∈ C, HasGradientWithinAt (F.value i) (F.gradient i x) C x)
    (hQ : ∀ i, TwoLevel.MonotoneLipschitz C (F.operator i) (F.lipschitz i))
    (L₀ L₁ : Fin (n + 1) → ℝ)
    (hsmooth : ∀ i, SymmetricSmoothOn C (F.gradient i) (L₀ i) (L₁ i))
    {s w : E} (hs : s ∈ C) (hw : w ∈ C)
    (hvi : ∀ z ∈ C, 0 ≤ ⟪(∑ i, F.gradient i w) + (∑ i, F.operator i w), z - w⟫)
    (project : ∀ R, 0 < R → Projection (region C s R))
    {ε R₀ : ℝ} (hε : 0 < ε) (hR₀ : 0 < R₀) (Λ₀ : Fin (n + 1) → ℝ) :
    let δ := ε / 3
    let a := initialParameters δ R₀ Λ₀
    let L := F.smoothCaps L₀ L₁ C s (max R₀ (24 * ‖s - w‖))
    let cap := parameterCaps a ‖s - w‖ L
    let B := remaining cap a + 1
    let result := restart (F.attempt δ s project) B a
    ∃ (b : Parameters (n + 1)) (z : E), result.outcome = some (b, z) ∧ z ∈ C ∧
      (∀ i, a i ≤ b i ∧ b i ≤ cap i) ∧ result.attempts.length ≤ B ∧
      (∀ v ∈ C, gap (fun t => ∑ i, F.value i t) (fun t => ∑ i, F.operator i t) z v ≤
        ε * ‖v - s‖ ^ 2) ∧
      (∀ (i : Fin (n + 1)) (o : Oracle),
        (result.attempts.map (fun v => (F.attemptCalls δ s project v i o : ℝ))).sum ≤
          6 * 17 ^ n * result.attempts.length * scale δ (b (some i)) (F.lipschitz i)) ∧
      ∀ H : ℝ, (∀ i, scale δ (b (some i)) (F.lipschitz i) ≤ H) →
        (result.attempts.map (fun v => (F.attemptProjections δ s project v : ℝ))).sum ≤
          3 * 17 ^ n * result.attempts.length *
            (H + ∑ i, scale δ (b (some i)) (F.lipschitz i)) := by
  let L := F.smoothCaps L₀ L₁ C s (max R₀ (24 * ‖s - w‖))
  have hR : 0 ≤ max R₀ (24 * ‖s - w‖) := hR₀.le.trans (le_max_left ..)
  have hcap := F.smoothCaps_spec hclosed hC L₀ L₁ hsmooth hs hR
  have hvalid := Family.valid_of_gradient hp hg hQ
  exact F.pathA hC hvalid hs hw (Family.solution_gap hvalid hw hvi) project hε hR₀ Λ₀ L
    (fun i => (hcap i).1) (fun i => (hcap i).2)

end

end LeanLab.Sliding.PathA
