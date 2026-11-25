module

public import LeanLab.Common.Recursive
public import LeanLab.Common.SymmetricSmoothness

set_option linter.style.header false

/-!
# Localized recursive sliding

Algorithm 1 of Borodich, Gasnikov and Kovalev with the leaf and the
correction projected onto the working set. Function arguments are
composed through the recursion. Operator queries use the unscaled points.
-/

@[expose] public section

namespace LeanLab.Sliding.Localized

open Set
open TwoLevel (Projection mix mix_mem weight_antitone weight_le_one)
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The current function argument and the two curvature scales. -/
structure Frame (E : Type*) where
  argument : E → E
  smoothScale : ℝ
  operatorScale : ℝ
  model : Model E

structure Result (E : Type*) where
  average : E
  centers : ℕ → E
  queries : List (Query E)

/-- Curvature of the active quadratic at iteration `t`. -/
def Level.curvature (l : Level E) (f : Frame E) (t : ℕ) : ℝ :=
  f.smoothScale * weight t * l.smoothness +
    f.operatorScale * (weight t / weight l.last) * l.lipschitz

/-- Descend after replacing the active component with its quadratic model. -/
def Frame.descend (f : Frame E) (l : Level E) (t : ℕ) (average center slope : E) :
    Frame E :=
  let H := l.curvature f t
  ⟨f.argument ∘ mix (weight t) average,
    f.smoothScale * weight t,
    f.operatorScale * (weight t / weight l.last),
    ⟨f.model.curvature + H, f.model.linear + (slope - H • center)⟩⟩

/-- A single iteration, running the child from the saved deeper centers. -/
def step {D : Set E} (P : Projection D) (l : Level E) (f : Frame E) (k t : ℕ)
    (child : Frame E → (ℕ → E) → Result E) (s : Result E) : Result E :=
  let center := s.centers k
  let x := f.argument (mix (weight t) s.average center)
  let q := l.operator center
  let nextFrame := f.descend l t s.average center (l.gradient x + q)
  let inner := child nextFrame s.centers
  let v := inner.average
  let z := P.apply (v + (l.curvature f t)⁻¹ • (q - l.operator v))
  ⟨mix (weight t) s.average v, Function.update inner.centers k z,
    s.queries ++ [⟨k, .gradient, x⟩, ⟨k, .operator, center⟩] ++
      inner.queries ++ [⟨k, .operator, v⟩]⟩

/-- Run the fixed number of iterations at one level. -/
def cycle {D : Set E} (P : Projection D) (l : Level E) (f : Frame E) (k : ℕ)
    (child : Frame E → (ℕ → E) → Result E) (centers : ℕ → E) : ℕ → Result E
  | 0 => ⟨centers k, centers, []⟩
  | t + 1 => step P l f k t child (cycle P l f k child centers t)

/-- Each position of the list is one recursion level. The empty list solves
the projected sum of the frozen quadratic models. -/
def run {D : Set E} (P : Projection D) :
    List (Level E) → ℕ → Frame E → (ℕ → E) → Result E
  | [], _, f, centers =>
    ⟨P.apply (-(f.model.curvature)⁻¹ • f.model.linear), centers, []⟩
  | l :: ls, k, f, centers =>
    cycle P l f k (run P ls (k + 1)) centers (l.last + 1)

def Frame.initial : Frame E := ⟨id, 1, 1, ⟨0, 0⟩⟩

/-- One pass from a common starting point, in the working Hilbert norm. -/
def pass {D : Set E} (P : Projection D) (levels : List (Level E)) (s : E) : Result E :=
  run P levels 0 Frame.initial (fun _ => s)

/-- Localized curvature from symmetric generalized smoothness, with the
gradient at the initial point passed explicitly so it can be cached. -/
def localCurvature (L₀ L₁ R : ℝ) (gs : E) : ℝ :=
  (L₀ + L₁ * ‖gs‖) * Real.exp (L₁ * R)

theorem localized_secant {C : Set E} {g : E → E} {L₀ L₁ : ℝ}
    (hg : SymmetricSmoothOn C g L₀ L₁) (hC : Convex ℝ C) {s : E} (hs : s ∈ C)
    {R : ℝ} {x y : E} (hx : x ∈ region C s R) (hy : y ∈ region C s R) :
    ‖g y - g x‖ ≤ localCurvature L₀ L₁ R (g s) * ‖y - x‖ :=
  hg.local_norm_sub_le hC hs R hx hy

def Result.Feasible (D : Set E) (s : Result E) : Prop :=
  s.average ∈ D ∧ (∀ i, s.centers i ∈ D) ∧ (∀ q ∈ s.queries, q.point ∈ D)

theorem Frame.descend_mapsTo {D : Set E} (f : Frame E) (hf : MapsTo f.argument D D)
    (hD : Convex ℝ D) (l : Level E) (t : ℕ) {a c slope : E} (ha : a ∈ D) :
    MapsTo (f.descend l t a c slope).argument D D :=
  fun _ hx => hf (mix_mem hD (weight_pos t).le (weight_le_one t) ha hx)

private theorem step_feasible {D : Set E} (P : Projection D) (hD : Convex ℝ D)
    (l : Level E) (f : Frame E) (hf : MapsTo f.argument D D) (k t : ℕ)
    (child : Frame E → (ℕ → E) → Result E)
    (hchild : ∀ f' centers, MapsTo f'.argument D D → (∀ i, centers i ∈ D) →
      (child f' centers).Feasible D) (s : Result E) (hs : s.Feasible D) :
    (step P l f k t child s).Feasible D := by
  let center := s.centers k
  let x := f.argument (mix (weight t) s.average center)
  let q := l.operator center
  let f' := f.descend l t s.average center (l.gradient x + q)
  let inner := child f' s.centers
  have hc : center ∈ D := hs.2.1 k
  have hx : x ∈ D := hf (mix_mem hD (weight_pos t).le (weight_le_one t) hs.1 hc)
  have hi : inner.Feasible D :=
    hchild f' s.centers (f.descend_mapsTo hf hD l t hs.1) hs.2.1
  refine ⟨mix_mem hD (weight_pos t).le (weight_le_one t) hs.1 hi.1, ?_, ?_⟩
  · intro j
    classical
    by_cases hj : j = k
    · subst j
      simpa only [step, Function.update_self] using
        P.feasible (inner.average + (l.curvature f t)⁻¹ • (q - l.operator inner.average))
    · simpa only [step, Function.update_of_ne hj] using hi.2.1 j
  · intro query hquery
    change query ∈ s.queries ++ [⟨k, .gradient, x⟩, ⟨k, .operator, center⟩] ++
      inner.queries ++ [⟨k, .operator, inner.average⟩] at hquery
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hquery
    rcases hquery with (((h | h | h) | h) | h)
    · exact hs.2.2 _ h
    · subst query
      exact hx
    · subst query
      exact hc
    · exact hi.2.2 _ h
    · subst query
      exact hi.1

private theorem cycle_feasible {D : Set E} (P : Projection D) (hD : Convex ℝ D)
    (l : Level E) (f : Frame E) (hf : MapsTo f.argument D D) (k : ℕ)
    (child : Frame E → (ℕ → E) → Result E)
    (hchild : ∀ f' centers, MapsTo f'.argument D D → (∀ i, centers i ∈ D) →
      (child f' centers).Feasible D)
    (centers : ℕ → E) (hs : ∀ i, centers i ∈ D) (t : ℕ) :
    (cycle P l f k child centers t).Feasible D := by
  induction t with
  | zero => exact ⟨hs k, hs, by simp [cycle]⟩
  | succ t ht => exact step_feasible P hD l f hf k t child hchild _ ht

theorem run_feasible {D : Set E} (P : Projection D) (hD : Convex ℝ D)
    (levels : List (Level E)) (k : ℕ) (f : Frame E) (centers : ℕ → E)
    (hf : MapsTo f.argument D D) (hs : ∀ i, centers i ∈ D) :
    (run P levels k f centers).Feasible D := by
  induction levels generalizing k f centers with
  | nil => exact ⟨P.feasible _, hs, by simp [run]⟩
  | cons l ls ih =>
    exact cycle_feasible P hD l f hf k _ (fun f' c hf' hc => ih _ f' c hf' hc) centers hs _

/-- Every output, saved center and recorded query remains in the localized
working set. This holds for any number of components. -/
theorem pass_feasible {C : Set E} (hC : Convex ℝ C) {s : E} {R : ℝ}
    (P : Projection (region C s R)) (levels : List (Level E)) (hs : s ∈ C) (hR : 0 ≤ R) :
    (pass P levels s).Feasible (region C s R) :=
  run_feasible P (hC.inter (convex_closedBall s R)) levels 0 _ _ (fun _ hx => hx)
    (fun _ => ⟨hs, Metric.mem_closedBall_self hR⟩)

/-- Number of recorded queries of the given oracle at a level. -/
def calls (result : Result E) (i : ℕ) (o : Oracle) : ℕ :=
  result.queries.countP fun q => decide (q.level = i ∧ q.oracle = o)

def Oracle.perVisit : Oracle → ℕ
  | .gradient => 1
  | .operator => 2

theorem run_calls {D : Set E} (P : Projection D) (levels : List (Level E))
    (k : ℕ) (f : Frame E) (centers : ℕ → E) (i : ℕ) (o : Oracle) :
    calls (run P levels k f centers) i o = visits levels k i * o.perVisit := by
  induction levels generalizing k f centers with
  | nil => simp [calls, run, visits]
  | cons l ls ih =>
    have hcycle (t : ℕ) :
        calls (cycle P l f k (run P ls (k + 1)) centers t) i o =
          t * ((if k = i then 1 else 0) + visits ls (k + 1) i) * o.perVisit := by
      induction t with
      | zero => simp [calls, cycle]
      | succ t ht =>
        simp only [cycle, step, calls, List.countP_append, List.countP_cons, List.countP_nil]
        simp only [calls] at ht ih
        rw [ht, ih]
        by_cases hk : k = i <;> cases o <;> simp [hk, Oracle.perVisit] <;> ring
    exact hcycle _

theorem pass_calls {D : Set E} (P : Projection D) (levels : List (Level E)) (s : E)
    (i : ℕ) (o : Oracle) :
    calls (pass P levels s) i o = visits levels 0 i * o.perVisit :=
  run_calls P levels 0 _ _ i o

/-- The schedule in the edited variant A, with two as the common multiplier. -/
def scheduledLength (h : ℕ → ℝ) : ℕ → ℕ
  | 0 => ⌈2 * h 0⌉₊
  | j + 1 => ⌈2 * (h (j + 1) / h j)⌉₊

private theorem scheduledLength_pos {h : ℕ → ℝ} (h₀ : 1 ≤ h 0) (hm : Monotone h) (j : ℕ) :
    0 < scheduledLength h j := by
  have ht (r : ℝ) (hr : 1 ≤ r) : 0 < ⌈2 * r⌉₊ := by
    exact Nat.cast_pos.mp ((show (0 : ℝ) < 2 * r by linarith).trans_le (Nat.le_ceil _))
  cases j with
  | zero => exact ht _ h₀
  | succ j =>
    have hp : 0 < h j := by linarith [hm (Nat.zero_le j)]
    exact ht _ ((le_div_iff₀ hp).mpr (by simpa using hm (Nat.le_succ j)))

/-- A list with the prescribed gradients, operators and curvatures, sorted
in the order used to define the scale `h`. -/
def scheduledLevels (n : ℕ) (g Q : ℕ → E → E) (Λ M h : ℕ → ℝ) : List (Level E) :=
  List.ofFn (fun i : Fin n => ⟨g i, Q i, Λ i, M i, scheduledLength h i - 1⟩)

/-- Exact count for the scheduled pass, including both operator calls per visit. -/
theorem scheduled_calls {D : Set E} (P : Projection D) (n : ℕ) (g Q : ℕ → E → E)
    (Λ M : ℕ → ℝ) {h : ℕ → ℝ} (h₀ : 1 ≤ h 0) (hm : Monotone h) (s : E)
    {i : ℕ} (hi : i < n) (o : Oracle) :
    calls (pass P (scheduledLevels n g Q Λ M h) s) i o =
      (∏ j ∈ Finset.range (i + 1), scheduledLength h j) * o.perVisit := by
  rw [pass_calls, ← zero_add i, visits_eq_prod _ _ i (by simpa [scheduledLevels] using hi),
    zero_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hj' : j < n := (Finset.mem_range.mp hj).trans_le (Nat.succ_le_of_lt hi)
  have hpos := scheduledLength_pos h₀ hm j
  simpa [scheduledLevels, hj'] using Nat.sub_add_cancel hpos

/-- The scheduled prefix is between the two geometric multiples in the
edited proof of variant A. -/
theorem scheduled_prefix_bounds {h : ℕ → ℝ} (h₀ : 1 ≤ h 0) (hm : Monotone h) (i : ℕ) :
    2 ^ (i + 1) * h i ≤ (∏ j ∈ Finset.range (i + 1), scheduledLength h j : ℕ) ∧
      (∏ j ∈ Finset.range (i + 1), scheduledLength h j : ℕ) ≤ 3 ^ (i + 1) * h i := by
  have ceiling (r : ℝ) (hr : 1 ≤ r) :
      2 * r ≤ (⌈2 * r⌉₊ : ℝ) ∧ (⌈2 * r⌉₊ : ℝ) ≤ 3 * r := by
    exact ⟨Nat.le_ceil _, by linarith [Nat.ceil_lt_add_one (show 0 ≤ 2 * r by linarith)]⟩
  induction i with
  | zero => simpa [scheduledLength] using ceiling _ h₀
  | succ i ih =>
    have hp : 0 < h i := by linarith [hm (Nat.zero_le i)]
    have hr : 1 ≤ h (i + 1) / h i := (le_div_iff₀ hp).mpr (by simpa using hm (Nat.le_succ i))
    obtain ⟨hlo, hhi⟩ := ceiling _ hr
    rw [Finset.prod_range_succ, Nat.cast_mul, scheduledLength]
    refine ⟨?_, ?_⟩
    · calc
        _ = (2 ^ (i + 1) * h i) * (2 * (h (i + 1) / h i)) := by
          rw [pow_succ (2 : ℝ) (i + 1)]; field_simp
        _ ≤ _ := mul_le_mul ih.1 hlo (by positivity) (by positivity)
    · calc
        _ ≤ (3 ^ (i + 1) * h i) * (3 * (h (i + 1) / h i)) :=
          mul_le_mul ih.2 hhi (by positivity) (by positivity)
        _ = _ := by rw [pow_succ (3 : ℝ) (i + 1)]; field_simp

/-- One gradient and two operator calls per visit give the separate budgets
for the scheduled pass. Computing the input curvature can consume one
additional initial gradient query per component. -/
theorem scheduled_calls_le {D : Set E} (P : Projection D) (n : ℕ) (g Q : ℕ → E → E)
    (Λ M : ℕ → ℝ) {h : ℕ → ℝ} (h₀ : 1 ≤ h 0) (hm : Monotone h) (s : E)
    {i : ℕ} (hi : i < n) (o : Oracle) :
    (calls (pass P (scheduledLevels n g Q Λ M h) s) i o : ℝ) ≤
      3 ^ (i + 1) * h i * o.perVisit := by
  rw [scheduled_calls P n g Q Λ M h₀ hm s hi o, Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right (scheduled_prefix_bounds h₀ hm i).2 (Nat.cast_nonneg _)

/-- The scale used by the edited variant A, including the unit floor. -/
def accuracyScale (τ Λ M : ℝ) : ℝ := max 1 (PathA.scale τ Λ M)

/-- The product of the terminal weights down to position `i`. -/
def terminalWeight (h : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (i + 1), weight (scheduledLength h j - 1)

theorem terminalWeight_le {h : ℕ → ℝ} (h₀ : 1 ≤ h 0) (hm : Monotone h) (i : ℕ) :
    terminalWeight h i ≤ 1 / h i := by
  have ht (j : ℕ) : 0 < scheduledLength h j := scheduledLength_pos h₀ hm j
  have hp : 0 < h i := by linarith [hm (Nat.zero_le i)]
  have hprod : 0 < (∏ j ∈ Finset.range (i + 1), (scheduledLength h j : ℝ)) :=
    Finset.prod_pos fun j _ => Nat.cast_pos.mpr (ht j)
  have hlo := (scheduled_prefix_bounds h₀ hm i).1
  rw [Nat.cast_prod] at hlo
  unfold terminalWeight
  calc
    _ ≤ ∏ j ∈ Finset.range (i + 1), 2 / (scheduledLength h j : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => (weight_pos _).le)
      intro j _
      have heq : ((scheduledLength h j - 1 : ℕ) : ℝ) + 1 = scheduledLength h j := by
        exact_mod_cast (Nat.sub_add_cancel (ht j))
      apply (weight_upper _).trans
      exact div_le_div_of_nonneg_left (by norm_num) (Nat.cast_pos.mpr (ht j)) (by linarith)
    _ = 2 ^ (i + 1) / ∏ j ∈ Finset.range (i + 1), (scheduledLength h j : ℝ) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
    _ ≤ 1 / h i := (div_le_div_iff₀ hprod hp).mpr (by simpa using hlo)

/-- The terminal weights convert the pass coefficient into the target
bound `n * τ` in the edited variant A. -/
theorem scheduled_coefficient_le {τ : ℝ} (hτ : 0 < τ) (Λ M : ℕ → ℝ)
    (hΛ : ∀ i, 0 ≤ Λ i)
    (hm : Monotone (fun i => accuracyScale τ (Λ i) (M i))) (n : ℕ) :
    let h := fun i => accuracyScale τ (Λ i) (M i)
    (∑ i ∈ Finset.range n, (terminalWeight h i ^ 2 * Λ i + terminalWeight h i * M i)) / 2
      ≤ n * τ := by
  let h := fun i => accuracyScale τ (Λ i) (M i)
  have h₁ (i : ℕ) : 1 ≤ h i := le_max_left ..
  have hpos (i : ℕ) : 0 < h i := zero_lt_one.trans_le (h₁ i)
  have hterm (i : ℕ) : terminalWeight h i ^ 2 * Λ i + terminalWeight h i * M i ≤ 2 * τ := by
    let β := terminalWeight h i
    have hβ : 0 ≤ β := Finset.prod_nonneg fun _ _ => (weight_pos _).le
    have hb := terminalWeight_le (h₁ 0) hm i
    have hb' : β * h i ≤ 1 := (le_div_iff₀ (hpos i)).mp hb
    have hL' : Real.sqrt (Λ i / τ) ≤ h i := (le_max_left ..).trans (le_max_right ..)
    have hM' : M i / τ ≤ h i := (le_max_right ..).trans (le_max_right ..)
    have hLg : β * Real.sqrt (Λ i / τ) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hL' hβ).trans (by simpa [mul_comm] using hb')
    have hLsq := pow_le_pow_left₀ (mul_nonneg hβ (Real.sqrt_nonneg _)) hLg 2
    rw [mul_pow, Real.sq_sqrt (div_nonneg (hΛ i) hτ.le), one_pow, ← mul_div_assoc] at hLsq
    have hLl : β ^ 2 * Λ i ≤ τ := by simpa using (div_le_iff₀ hτ).mp hLsq
    have hm' : β * (M i / τ) ≤ 1 := (mul_le_mul_of_nonneg_left hM' hβ).trans hb'
    rw [← mul_div_assoc] at hm'
    have hMl : β * M i ≤ τ := by simpa using (div_le_iff₀ hτ).mp hm'
    linarith only [hLl, hMl]
  change (∑ i ∈ Finset.range n, (terminalWeight h i ^ 2 * Λ i + terminalWeight h i * M i)) / 2
    ≤ n * τ
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun i _ => hterm i)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  linarith only [hsum]

/-- The oracle budgets of variant A with the specified accuracy scale. -/
theorem accuracy_calls_le {D : Set E} (P : Projection D) (n : ℕ) (g Q : ℕ → E → E)
    (τ : ℝ) (Λ M : ℕ → ℝ) (hm : Monotone (fun i => accuracyScale τ (Λ i) (M i))) (s : E)
    {i : ℕ} (hi : i < n) (o : Oracle) :
    let h := fun j => accuracyScale τ (Λ j) (M j)
    (calls (pass P (scheduledLevels n g Q Λ M h) s) i o : ℝ) ≤
      3 ^ (i + 1) * h i * o.perVisit :=
  scheduled_calls_le P n g Q Λ M (le_max_left ..) hm s hi o

/-- The recursive base case realizes the minimum of the accumulated model. -/
theorem run_nil_bound {D : Set E} (P : Projection D) (k : ℕ) (f : Frame E)
    (centers : ℕ → E) (hH : 0 < f.model.curvature) {w : E} (hw : w ∈ D) :
    let v := (run P [] k f centers).average
    let H := f.model.curvature
    let m := model H (0 : E) f.model.linear
    m v - m w + H / 2 * ‖v - w‖ ^ 2 ≤ 0 := by
  simpa [run, smul_neg] using projected_model_bound P hH 0 f.model.linear hw

/-- At the root with one component, the projected model and the weight
recurrence give a telescoping bound for the actual program. -/
theorem single_level_gap {D : Set E} (P : Projection D) (l : Level E) {p : E → ℝ}
    (hp : ConvexOn ℝ D p) (hΛ : 0 < l.smoothness) (hM : 0 ≤ l.lipschitz)
    (hupper : ∀ x ∈ D, ∀ y ∈ D, p y ≤
      p x + ⟪l.gradient x, y - x⟫ + l.smoothness / 2 * ‖y - x‖ ^ 2)
    (hsupport : ∀ x ∈ D, ∀ y ∈ D, p x + ⟪l.gradient x, y - x⟫ ≤ p y)
    (hmono : ∀ x ∈ D, ∀ y ∈ D, 0 ≤ ⟪l.operator x - l.operator y, x - y⟫)
    (hlip : ∀ x ∈ D, ∀ y ∈ D, ‖l.operator x - l.operator y‖ ≤ l.lipschitz * ‖y - x‖)
    {s w : E} (hs : s ∈ D) (hw : w ∈ D) :
    gap p l.operator (pass P [l] s).average w ≤
      (weight l.last ^ 2 * l.smoothness + weight l.last * l.lipschitz) / 2 *
        ‖s - w‖ ^ 2 := by
  let A := fun t => cycle P l Frame.initial 0 (run P [] 1) (fun _ => s) t
  let C := l.smoothness + l.lipschitz / weight l.last
  have hC : 0 < C := add_pos_of_pos_of_nonneg hΛ (div_nonneg hM (weight_pos _).le)
  have hfeas (t : ℕ) : (A t).Feasible D :=
    cycle_feasible P hp.1 l Frame.initial (fun _ hx => hx) 0 (run P [] 1)
      (fun f centers hf hcenters => run_feasible P hp.1 [] 1 f centers hf hcenters)
      (fun _ => s) (fun _ => hs) t
  have hiter (t : ℕ) (ht : t ≤ l.last) :
      (gap p l.operator (A (t + 1)).average w -
        (1 - weight t) * gap p l.operator (A t).average w) / weight t ^ 2 ≤
      (C / 2 * ‖(A t).centers 0 - w‖ ^ 2) -
        (C / 2 * ‖(A (t + 1)).centers 0 - w‖ ^ 2) := by
    let α := weight t
    have hα : 0 < α := weight_pos t
    have hα' : α ≤ 1 := weight_le_one t
    let a := (A t).average
    let u := (A t).centers 0
    let T := mix α a
    let x := T u
    let H := l.curvature (Frame.initial : Frame E) t
    let q := l.operator u
    let f' := Frame.initial.descend l t a u (l.gradient x + q)
    let v := (run P [] 1 f' (A t).centers).average
    let z := P.apply (v + H⁻¹ • (q - l.operator v))
    let p' : E → ℝ := fun y => p (T y) / α
    have hH : H = α * C := by dsimp [H, Level.curvature, Frame.initial, C, α]; ring
    have hHpos : 0 < H := hH.symm ▸ mul_pos hα hC
    have ha : a ∈ D := (hfeas t).1
    have hu : u ∈ D := (hfeas t).2.1 0
    have hv : v ∈ D := P.feasible _
    have hT {y : E} (hy : y ∈ D) : T y ∈ D := mix_mem hp.1 hα.le hα' ha hy
    have hdiff (y : E) : T y - x = α • (y - u) := by
      dsimp [T, x, mix]
      module
    have hmodel : p' v ≤ p' u + ⟪l.gradient x, v - u⟫ +
        (α * l.smoothness) / 2 * ‖v - u‖ ^ 2 := by
      have he := hupper x (hT hu) (T v) (hT hv)
      rw [hdiff, real_inner_smul_right, norm_smul_of_nonneg hα.le] at he
      apply (div_le_iff₀ hα).mpr
      dsimp [p']
      have hc := (div_mul_cancel₀ (p x) hα.ne')
      rw [add_mul, add_mul]
      change p (T v) ≤ p x / α * α + _ + _
      rw [hc]
      nlinarith only [he]
    have hsupp : p' u + ⟪l.gradient x, w - u⟫ ≤ p' w := by
      have he := hsupport x (hT hu) (T w) (hT hw)
      rw [hdiff, real_inner_smul_right] at he
      apply (le_div_iff₀ hα).mpr
      dsimp [p']
      rw [add_mul, div_mul_cancel₀ _ hα.ne']
      linarith only [he]
    have hcurv : α * l.smoothness + l.lipschitz ≤ H := by
      have hratio : 1 ≤ α / weight l.last :=
        (le_div_iff₀ (weight_pos _)).mpr (by simpa [α] using weight_antitone ht)
      have hh := mul_le_mul_of_nonneg_right hratio hM
      dsimp [H, Level.curvature, Frame.initial, α] at *
      linarith only [hh]
    have hproj := P.normal (v + H⁻¹ • (q - l.operator v)) hw
    have hcomp := model_comparison_of_curvature hHpos (mul_nonneg hα.le hΛ.le) hM
      hcurv hmodel hsupp (hmono v hv w hw) (hlip u hu v hv) hproj
    have hvform : v = P.apply (H⁻¹ • (H • u - (l.gradient x + q))) := by
      dsimp [v, run, f', Frame.descend, Frame.initial, H]
      simp only [zero_add, neg_smul, smul_sub]
      congr 1
      abel
    have hmin := projected_model_bound P hHpos u (l.gradient x + q) hw
    dsimp only at hmin
    rw [← hvform] at hmin
    have hchild := hcomp.trans hmin
    let r : E → ℝ := fun y => ⟪l.operator w, y⟫
    have hr : ConvexOn ℝ D r :=
      (innerSL ℝ (l.operator w)).toLinearMap.convexOn hp.1
    have htrans := transfer (f := p) (r := r)
      hp hr ha hv hw hα hα' (child := 0)
      (correction := H / 2 * (‖z - w‖ ^ 2 - ‖u - w‖ ^ 2)) (by
        dsimp [gap, p', r] at hchild ⊢
        rw [sub_div, ← inner_sub_right]
        exact hchild)
    have hgap (y : E) : p y + r y - (p w + r w) = gap p l.operator y w := by
      simp only [gap, r, inner_sub_right]
      ring
    rw [hgap, hgap] at htrans
    have hh := iteration_bound (α := α) (β := 1) (c := C) (tail := 0) (tailNext := 0) hα
      (by simpa [hH] using htrans) (by simp)
    change (gap p l.operator (T v) w - (1 - α) * gap p l.operator a w) / α ^ 2 ≤ _
    have hz : (A (t + 1)).centers 0 = z := by
      simp [A, cycle, step, z, v, f', x, T, a, u, q, H, α, Frame.initial]
    rw [hz]
    calc
      _ ≤ (1 : ℝ) / 2 * ((C * ‖u - w‖ ^ 2 + 0) - (C * ‖z - w‖ ^ 2 + 0)) := hh
      _ = _ := by change _ = C / 2 * ‖u - w‖ ^ 2 - C / 2 * ‖z - w‖ ^ 2; ring
  have htel := telescope (α := weight) (F := fun t => gap p l.operator (A t).average w)
    (P := fun t => C / 2 * ‖(A t).centers 0 - w‖ ^ 2)
    weight_pos weight_zero weight_recurrence l.last hiter
  have hlast : 0 ≤ C / 2 * ‖(A (l.last + 1)).centers 0 - w‖ ^ 2 := by positivity
  have hbound := htel.trans (mul_le_mul_of_nonneg_left (sub_le_self _ hlast) (sq_nonneg _))
  change gap p l.operator (pass P [l] s).average w ≤ _ at hbound
  calc
    _ ≤ weight l.last ^ 2 * (C / 2 * ‖s - w‖ ^ 2) := hbound
    _ = _ := by dsimp [C]; field_simp [ne_of_gt (weight_pos _)]

end

end LeanLab.Sliding.Localized
