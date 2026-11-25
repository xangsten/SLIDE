module

public import LeanLab.Variants.TwoLevel

set_option linter.style.header false

/-!
# Restarts and oracle budgets for two-level sliding

A retry doubles either the radius or the curvature. The inner length is
computed directly from the balance inequality, using an integer ceiling.
-/

@[expose] public section

namespace LeanLab.Sliding.TwoLevel

open Set
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Schedule where
  outerLast : ℕ
  baseInnerLast : ℕ
  L₀ : ℝ
  L₁ : ℝ
  M : ℝ
  check : Check

/-- A direct choice satisfying the draft's balance test. -/
def Schedule.config (p : Schedule) (Λ : ℝ) : Config :=
  let a := weight p.outerLast
  let j := max p.baseInnerLast ⌈4 * p.M / (a * Λ)⌉₊
  ⟨p.L₀, p.L₁, Λ, 2 * p.M / (a * weight j), j, p.check⟩

theorem Schedule.curvature_pos (p : Schedule) {Λ : ℝ} (hM : 0 < p.M) :
    0 < (p.config Λ).operatorCurvature := by
  unfold Schedule.config
  exact div_pos (by positivity) (mul_pos (weight_pos _) (weight_pos _))

theorem Schedule.curvature_eq (p : Schedule) (Λ : ℝ) :
    weight (p.config Λ).innerLast * scale (p.config Λ) p.outerLast = 2 * p.M := by
  unfold scale Schedule.config
  dsimp only
  rw [← mul_assoc, mul_comm (weight _)]
  exact mul_div_cancel₀ _ (mul_ne_zero (weight_pos _).ne' (weight_pos _).ne')

theorem Schedule.balance (p : Schedule) {Λ : ℝ} (hM : 0 < p.M) (hΛ : 0 < Λ) :
    weight (p.config Λ).innerLast ^ 2 * (p.config Λ).operatorCurvature ≤ Λ := by
  let a := weight p.outerLast
  let j := (p.config Λ).innerLast
  have ha : 0 < a := weight_pos _
  have hb : 0 < weight j := weight_pos _
  have hj : 4 * p.M / (a * Λ) ≤ (j : ℝ) := (Nat.le_ceil _).trans
    (Nat.cast_le.mpr (le_max_right ..))
  have hj' := (div_le_iff₀ (mul_pos ha hΛ)).mp hj
  have hweight := (le_div_iff₀ (show 0 < (j : ℝ) + 2 by positivity)).mp (weight_upper j)
  have hm := mul_le_mul_of_nonneg_left hweight (show 0 ≤ 2 * p.M by positivity)
  have hbound : 2 * p.M * weight j ≤ a * Λ := by
    apply le_of_mul_le_mul_right _ (show 0 < (j : ℝ) + 2 by positivity)
    have hn : 0 ≤ a * Λ := by positivity
    nlinarith only [hj', hm, hn]
  change weight j ^ 2 * (2 * p.M / (a * weight j)) ≤ Λ
  have heq : weight j ^ 2 * (2 * p.M / (a * weight j)) = (2 * p.M * weight j) / a := by
    field_simp
  rw [heq]
  exact (div_le_iff₀ ha).mpr (by linarith only [hbound])

theorem Schedule.inner_antitone (p : Schedule) (hM : 0 ≤ p.M) {Λ₁ Λ₂ : ℝ}
    (h₁ : 0 < Λ₁) (h : Λ₁ ≤ Λ₂) : (p.config Λ₂).innerLast ≤ (p.config Λ₁).innerLast := by
  unfold Schedule.config
  exact max_le_max_left _ (Nat.ceil_mono (div_le_div_of_nonneg_left (by positivity)
    (mul_pos (weight_pos _) h₁) (mul_le_mul_of_nonneg_left h (weight_pos _).le)))

structure Parameters where
  radius : ℝ
  curvature : ℝ

def region (C : Set E) (zin : E) (R : ℝ) : Set E :=
  C ∩ Metric.closedBall zin (max 0 R)

def Projectors (C : Set E) (zin : E) :=
  ∀ R, Projection (region C zin R)

def attempt (p : Schedule) {C : Set E} {zin : E} (P : Projectors C zin)
    (g Q : E → E) (a : Parameters) : Except Parameters E × Calls :=
  let cfg := p.config a.curvature
  let run := outerRun (P a.radius) g Q cfg zin (p.outerLast + 1)
  let res := match run.result with
    | .error τ => .error { a with curvature := max (2 * a.curvature) τ }
    | .ok s => if ‖s.average - zin‖ ≤ a.radius / 2 then .ok s.average
      else .error { a with radius := 2 * a.radius }
  (res, run.calls)

def Calls.add (a b : Calls) : Calls := ⟨a.gradients + b.gradients, a.operators + b.operators⟩

/-- A finite prefix of the unbounded retry loop. A successful prefix
returns the final parameters alongside its output and all accrued calls. -/
def search (trial : Parameters → Except Parameters E × Calls) :
    ℕ → Parameters → Option (Parameters × E) × Calls
  | 0, _ => (none, ⟨0, 0⟩)
  | n + 1, a =>
    let (outcome, calls) := trial a
    match outcome with
    | .ok z => (some (a, z), calls)
    | .error b =>
      let (result, more) := search trial n b
      (result, calls.add more)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
private theorem search_failure_growth (trial : Parameters → Except Parameters E × Calls)
    (Good : Parameters → Prop)
    (hstep : ∀ {a b}, Good a → (trial a).1 = .error b →
      Good b ∧ 2 * (a.radius * a.curvature) ≤ b.radius * b.curvature)
    (n : ℕ) {a : Parameters} (ha : Good a) (hout : (search trial n a).1 = none) :
    ∃ b, Good b ∧ (2 : ℝ) ^ n * (a.radius * a.curvature) ≤ b.radius * b.curvature := by
  induction n generalizing a with
  | zero => exact ⟨a, ha, by simp⟩
  | succ n ih =>
    cases ht : (trial a).1 with
    | ok z => simp [search, ht] at hout
    | error b =>
      have hout' : (search trial n b).1 = none := by simpa [search, ht] using hout
      obtain ⟨hb, hgrowth⟩ := hstep ha ht
      obtain ⟨c, hc, hprod⟩ := ih hb hout'
      exact ⟨c, hc, by
        rw [pow_succ, mul_assoc]
        exact (mul_le_mul_of_nonneg_left hgrowth (by positivity)).trans hprod⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem search_terminates (trial : Parameters → Except Parameters E × Calls)
    (Good : Parameters → Prop) {B : ℝ} {a : Parameters} (ha : Good a)
    (hpos : 0 < a.radius * a.curvature)
    (hbound : ∀ b, Good b → b.radius * b.curvature ≤ B)
    (hstep : ∀ {a b}, Good a → (trial a).1 = .error b →
      Good b ∧ 2 * (a.radius * a.curvature) ≤ b.radius * b.curvature) :
    ∃ n b z, (search trial n a).1 = some (b, z) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B / (a.radius * a.curvature))
    (show (1 : ℝ) < 2 by norm_num)
  cases hs : (search trial n a).1 with
  | some output => exact ⟨n, output.1, output.2, hs⟩
  | none =>
    obtain ⟨b, hb, hg⟩ := search_failure_growth trial Good hstep n ha hs
    exact (not_lt_of_ge (hg.trans (hbound b hb)) ((div_lt_iff₀ hpos).mp hn)).elim

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Counts include unsuccessful attempts. The per-attempt bound can be
taken at the initial curvature, since the prescribed inner length is antitone. -/
theorem search_calls (trial : Parameters → Except Parameters E × Calls)
    (Good : Parameters → Prop) (budget : Calls)
    (hstep : ∀ {a b}, Good a → (trial a).1 = .error b → Good b)
    (hbudget : ∀ a, Good a → (trial a).2.gradients ≤ budget.gradients ∧
      (trial a).2.operators ≤ budget.operators) (n : ℕ) {a : Parameters} (ha : Good a) :
    (search trial n a).2.gradients ≤ n * budget.gradients ∧
      (search trial n a).2.operators ≤ n * budget.operators := by
  induction n generalizing a with
  | zero => simp [search]
  | succ n ih =>
    have hb := hbudget a ha
    cases ht : (trial a).1 with
    | ok z =>
      simpa [search, ht, Nat.succ_mul] using
        (show _ ≤ n * budget.gradients + budget.gradients ∧
            _ ≤ n * budget.operators + budget.operators from
          ⟨hb.1.trans (Nat.le_add_left ..), hb.2.trans (Nat.le_add_left ..)⟩)
    | error b =>
      have hc := ih (hstep ha ht)
      simpa [search, ht, Calls.add, Nat.succ_mul, Nat.add_comm] using
        And.intro (Nat.add_le_add hb.1 hc.1) (Nat.add_le_add hb.2 hc.2)

private theorem region_convex {C : Set E} {zin : E} {R : ℝ} (hC : Convex ℝ C) :
    Convex ℝ (region C zin R) := hC.inter (convex_closedBall ..)

omit [InnerProductSpace ℝ E] in
private theorem region_start {C : Set E} {zin : E} (hz : zin ∈ C) (R : ℝ) :
    zin ∈ region C zin R := by
  exact ⟨hz, Metric.mem_closedBall_self (le_max_left ..)⟩

private theorem region_operator {C : Set E} {zin : E} {R M : ℝ} {Q : E → E}
    (hQ : MonotoneLipschitz C Q M) : MonotoneLipschitz (region C zin R) Q M :=
  ⟨hQ.nonneg, fun a b => hQ.monotone a.1 b.1, fun a b => hQ.lipschitz a.1 b.1⟩

/-- Radius and curvature invariants, including monotonicity relative to the start. -/
structure InBounds (initial a : Parameters) (maxRadius maxCurvature : ℝ) : Prop where
  radius_ge : initial.radius ≤ a.radius
  curvature_ge : initial.curvature ≤ a.curvature
  radius_le : a.radius ≤ maxRadius
  curvature_le : a.curvature ≤ maxCurvature

/-- Assumptions used by the retry loop. The threshold bound only needs
to hold on the visited working sets. -/
structure Problem (p : Schedule) (C : Set E) (zin solution : E)
    (f : E → ℝ) (g Q : E → E) (maxRadius cap : ℝ) : Prop where
  convex : ConvexOn ℝ C f
  initial_feasible : zin ∈ C
  solution_feasible : solution ∈ C
  solution_gap {z : E} : z ∈ C → 0 ≤ gap f Q z solution
  operator : MonotoneLipschitz C Q p.M
  operator_pos : 0 < p.M
  functionModel (a : Parameters) :
    FunctionOracle (region C zin a.radius) f g (p.config a.curvature)
  bounded (a : Parameters) : 0 < a.radius → a.radius ≤ maxRadius →
    ∃ A, ThresholdBounds (region C zin a.radius) g (p.config a.curvature) A (2 * a.radius) ∧
      thresholdCap (p.config a.curvature) A (2 * a.radius) ≤ cap

theorem attempt_retry (p : Schedule) {C : Set E} {zin solution : E}
    (P : Projectors C zin) {f : E → ℝ} {g Q : E → E}
    {initial a b : Parameters} {cap : ℝ}
    (hr : 0 < initial.radius) (hInitialCurvature : 0 < initial.curvature)
    (pb : Problem p C zin solution f g Q (max initial.radius (10 * ‖zin - solution‖)) cap)
    (ha : InBounds initial a (max initial.radius (10 * ‖zin - solution‖))
      (max initial.curvature (2 * cap)))
    (hretry : (attempt p P g Q a).1 = .error b) :
    InBounds initial b (max initial.radius (10 * ‖zin - solution‖))
      (max initial.curvature (2 * cap)) ∧
      2 * (a.radius * a.curvature) ≤ b.radius * b.curvature := by
  have hR := hr.trans_le ha.radius_ge
  have hΛ := hInitialCurvature.trans_le ha.curvature_ge
  let cfg := p.config a.curvature
  let run := outerRun (P a.radius) g Q cfg zin (p.outerLast + 1)
  have hz' := region_start pb.initial_feasible a.radius
  change (match run.result with
    | .error τ => Except.error { a with curvature := max (2 * a.curvature) τ }
    | .ok s => if ‖s.average - zin‖ ≤ a.radius / 2 then Except.ok s.average
      else Except.error { a with radius := 2 * a.radius }) = .error b at hretry
  cases hout : run.result with
  | error τ =>
    have hb : { a with curvature := max (2 * a.curvature) τ } = b := by
      simpa only [hout, Except.error.injEq] using hretry
    subst b
    obtain ⟨A, hth, hcap⟩ := pb.bounded a hR ha.radius_le
    have hvalid := run_outcome (P a.radius) g Q cfg (region_convex pb.convex.1)
      hth hz' (p.outerLast + 1)
    change ValidOutcome _ _ _ run.result at hvalid
    rw [hout] at hvalid
    have hupdate := curvature_update hvalid.1 (hvalid.2.trans hcap) hΛ.le
    change 2 * a.curvature ≤ max (2 * a.curvature) τ ∧
      max (2 * a.curvature) τ ≤ 2 * cap at hupdate
    have hcurv_ge := (show a.curvature ≤ 2 * a.curvature by linarith).trans hupdate.1
    exact ⟨⟨ha.radius_ge, ha.curvature_ge.trans hcurv_ge,
      ha.radius_le, hupdate.2.trans (le_max_right ..)⟩, by
        dsimp only
        linarith only [mul_le_mul_of_nonneg_left hupdate.1 hR.le]⟩
  | ok s =>
    by_cases hnear : ‖s.average - zin‖ ≤ a.radius / 2
    · simp [hout, hnear] at hretry
    have hb : { a with radius := 2 * a.radius } = b := by
      simpa only [hout, ite_eq_right hnear, Except.error.injEq] using hretry
    subst b
    have hsmall : a.radius < 5 * ‖zin - solution‖ := by
      by_contra! hlarge
      have hsolution : solution ∈ region C zin a.radius := by
        refine ⟨pb.solution_feasible, ?_⟩
        rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev solution zin, max_eq_right hR.le]
        linarith [norm_nonneg (zin - solution)]
      have hbound := run_radius (P a.radius) (pb.functionModel a) (region_operator pb.operator)
        hΛ (p.curvature_pos pb.operator_pos) (p.balance pb.operator_pos hΛ) hz' hsolution
        (fun z hz => pb.solution_gap hz.1) p.outerLast (p.curvature_eq _).ge hout
      have htriangle : ‖s.average - zin‖ ≤
          ‖s.average - solution‖ + ‖zin - solution‖ := by
        have heq : s.average - zin = (s.average - solution) - (zin - solution) := by abel
        rw [heq]
        exact norm_sub_le _ _
      have hsqrt : Real.sqrt 2 ≤ (3 : ℝ) / 2 := by
        apply le_of_sq_le_sq _ (by norm_num)
        rw [Real.sq_sqrt (by norm_num)]
        norm_num
      have hm := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg (zin - solution))
      exact hnear (by linarith only [htriangle, hbound, hm, hlarge])
    exact ⟨⟨ha.radius_ge.trans (by linarith), ha.curvature_ge,
      (show 2 * a.radius ≤ 10 * ‖zin - solution‖ by linarith).trans (le_max_right ..),
      ha.curvature_le⟩, by dsimp; ring_nf; exact le_rfl⟩

/-- The accepted output has the sharpened global gap bound. -/
theorem attempt_gap (p : Schedule) {C : Set E} {zin solution : E}
    (P : Projectors C zin) {f : E → ℝ} {g Q : E → E}
    {a : Parameters} {maxRadius cap : ℝ}
    (pb : Problem p C zin solution f g Q maxRadius cap)
    (hR : 0 < a.radius) (hΛ : 0 < a.curvature)
    {z : E} (hok : (attempt p P g Q a).1 = .ok z) :
    z ∈ C ∧ ∀ w ∈ C,
      gap f Q z w ≤ gapCoefficient (p.config a.curvature) p.outerLast * ‖w - zin‖ ^ 2 := by
  let cfg := p.config a.curvature
  let run := outerRun (P a.radius) g Q cfg zin (p.outerLast + 1)
  have hz' := region_start pb.initial_feasible a.radius
  change (match run.result with
    | .error τ => Except.error { a with curvature := max (2 * a.curvature) τ }
    | .ok s => if ‖s.average - zin‖ ≤ a.radius / 2 then Except.ok s.average
      else Except.error { a with radius := 2 * a.radius }) = .ok z at hok
  cases hout : run.result with
  | error τ => simp [hout] at hok
  | ok s =>
    by_cases hnear : ‖s.average - zin‖ ≤ a.radius / 2
    · have heq : s.average = z := by simpa only [hout, ite_eq_left hnear, Except.ok.injEq] using hok
      subst z
      have hf := pb.functionModel a
      have hQ := region_operator (R := a.radius) (zin := zin) pb.operator
      have hc := p.curvature_pos (Λ := a.curvature) pb.operator_pos
      have hcurv := (p.curvature_eq a.curvature).ge
      have hs := (run_energy (P a.radius) hf hQ hΛ hc hz' p.outerLast hcurv hout).1.1.1
      refine ⟨hs, ?_⟩
      intro w hw
      apply global_gap_bound pb.convex (fun x hx y hy => pb.operator.monotone hx hy) hs hR
        (show 0 ≤ gapCoefficient cfg p.outerLast from by
          change 0 ≤ weight p.outerLast ^ 2 *
            (a.curvature + weight cfg.innerLast ^ 2 * cfg.operatorCurvature) / 2
          exact div_nonneg (mul_nonneg (sq_nonneg _)
            (add_nonneg hΛ.le (mul_nonneg (sq_nonneg _) hc.le))) (by norm_num))
        hnear _ w hw
      intro v hv hdist
      have hregion : v ∈ region C zin a.radius := by
        exact ⟨hv, by simpa [Metric.mem_closedBall, dist_eq_norm, max_eq_right hR.le] using hdist⟩
      rw [norm_sub_rev v zin]
      exact run_gap (P a.radius) hf hQ hΛ hc hz' p.outerLast hcurv hout hregion
    · simp [hout, hnear] at hok

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
private theorem search_result (trial : Parameters → Except Parameters E × Calls)
    (Good : Parameters → Prop)
    (hstep : ∀ {a b}, Good a → (trial a).1 = .error b → Good b)
    (n : ℕ) {a b : Parameters} {z : E} (ha : Good a)
    (hout : (search trial n a).1 = some (b, z)) :
    Good b ∧ (trial b).1 = .ok z := by
  induction n generalizing a with
  | zero => simp [search] at hout
  | succ n ih =>
    cases h : (trial a).1 with
    | ok x =>
      have heq : a = b ∧ x = z := by simpa [search, h] using hout
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨ha, h⟩
    | error c =>
      exact ih (hstep ha h) (by simpa [search, h] using hout)

theorem attempt_calls (p : Schedule) {C : Set E} {zin : E} (P : Projectors C zin)
    (g Q : E → E) {a : Parameters} {Λ₀ : ℝ} (hM : 0 ≤ p.M) (hΛ₀ : 0 < Λ₀)
    (hΛ : Λ₀ ≤ a.curvature) :
    (attempt p P g Q a).2.gradients ≤ (p.outerLast + 1) * gradientsPerStep (p.config Λ₀) ∧
      (attempt p P g Q a).2.operators ≤
        (p.outerLast + 1) * (2 * ((p.config Λ₀).innerLast + 1)) := by
  have h := run_calls (P a.radius) g Q (p.config a.curvature) zin (p.outerLast + 1)
  refine ⟨h.1, h.2.trans ?_⟩
  gcongr
  exact p.inner_antitone hM hΛ₀ hΛ

/-- End-to-end certificate with a user-supplied attempt limit. Any limit
whose power of two exceeds the ratio of the bounding and starting
products suffices, and all calls up to that limit are covered. -/
theorem run_with_retries (p : Schedule) {C : Set E} {zin solution : E}
    (P : Projectors C zin) {f : E → ℝ} {g Q : E → E}
    (initial : Parameters) {cap : ℝ}
    (hr : 0 < initial.radius) (hInitialCurvature : 0 < initial.curvature)
    (pb : Problem p C zin solution f g Q (max initial.radius (10 * ‖zin - solution‖)) cap)
    (n : ℕ)
    (hn : max initial.radius (10 * ‖zin - solution‖) * max initial.curvature (2 * cap) <
      (2 : ℝ) ^ n * (initial.radius * initial.curvature)) :
    ∃ b z,
      (search (attempt p P g Q) n initial).1 = some (b, z) ∧ z ∈ C ∧
      (∀ w ∈ C, gap f Q z w ≤ gapCoefficient (p.config b.curvature) p.outerLast *
        ‖w - zin‖ ^ 2) ∧
      b.curvature ≤ max initial.curvature (2 * cap) ∧
      (search (attempt p P g Q) n initial).2.gradients ≤
        n * ((p.outerLast + 1) * gradientsPerStep (p.config initial.curvature)) ∧
      (search (attempt p P g Q) n initial).2.operators ≤
        n * ((p.outerLast + 1) * (2 * ((p.config initial.curvature).innerLast + 1))) := by
  let Rmax := max initial.radius (10 * ‖zin - solution‖)
  let Λmax := max initial.curvature (2 * cap)
  let Good := fun a => InBounds initial a Rmax Λmax
  let trial := attempt p P g Q
  have hgood : Good initial := ⟨le_rfl, le_rfl, le_max_left .., le_max_left ..⟩
  have hstep {a b : Parameters} (ha : Good a) (he : (trial a).1 = .error b) :
      Good b ∧ 2 * (a.radius * a.curvature) ≤ b.radius * b.curvature :=
    attempt_retry p P hr hInitialCurvature pb ha he
  have hbound {b : Parameters} (hb : Good b) : b.radius * b.curvature ≤ Rmax * Λmax :=
    mul_le_mul hb.radius_le hb.curvature_le (hInitialCurvature.le.trans hb.curvature_ge)
      (hr.le.trans (le_max_left ..))
  have hout : (search trial n initial).1 ≠ none := by
    intro hnone
    obtain ⟨b, hb, hg⟩ := search_failure_growth trial Good (fun ha he => hstep ha he) n hgood hnone
    exact (not_lt_of_ge (hg.trans (hbound hb))) hn
  cases he : (search trial n initial).1 with
  | none => exact (hout he).elim
  | some bz =>
    obtain ⟨b, z⟩ := bz
    obtain ⟨hb, hok⟩ := search_result trial Good (fun h₁ h₂ => (hstep h₁ h₂).1) n hgood he
    have hg := attempt_gap p P pb (hr.trans_le hb.radius_ge)
      (hInitialCurvature.trans_le hb.curvature_ge) hok
    let budget : Calls :=
      ⟨(p.outerLast + 1) * gradientsPerStep (p.config initial.curvature),
        (p.outerLast + 1) * (2 * ((p.config initial.curvature).innerLast + 1))⟩
    have hc := search_calls trial Good budget (fun h₁ h₂ => (hstep h₁ h₂).1)
      (fun _ h => attempt_calls p P g Q pb.operator_pos.le hInitialCurvature h.curvature_ge) n hgood
    exact ⟨b, z, rfl, hg.1, hg.2, hb.curvature_le, hc.1, hc.2⟩

/-- The secant variant only requires a Lipschitz bound on the largest
working set to certify the uniform curvature cap 4A. -/
theorem secant_problem (p : Schedule) {C : Set E} {zin solution : E}
    {f : E → ℝ} {g Q : E → E} {Rmax A : ℝ} (hmode : p.check = .secant)
    (hf : ConvexOn ℝ C f) (hz : zin ∈ C) (hs : solution ∈ C)
    (hsol : ∀ z ∈ C, 0 ≤ gap f Q z solution)
    (hQ : MonotoneLipschitz C Q p.M) (hM : 0 < p.M)
    (hsupport : ∀ x ∈ C, ∀ y ∈ C, f x + ⟪g x, y - x⟫ ≤ f y)
    (hA : 0 ≤ A) (hscale : ∀ x ∈ region C zin Rmax, p.L₀ + p.L₁ * ‖g x‖ ≤ A)
    (hlip : ∀ x ∈ region C zin Rmax, ∀ y ∈ region C zin Rmax,
      ‖g y - g x‖ ≤ A * ‖y - x‖) :
    Problem p C zin solution f g Q Rmax (4 * A) := by
  refine ⟨hf, hz, hs, hsol _, hQ, hM, ?_, ?_⟩
  · intro a
    refine ⟨hf.subset inter_subset_left (region_convex hf.1),
      fun hx hy => hsupport _ hx.1 _ hy.1, ?_⟩
    intro x y h
    change p.check = .exponential at h
    rw [hmode] at h
    contradiction
  · intro a _ hR
    have hsub : region C zin a.radius ⊆ region C zin Rmax := fun _ hx =>
      ⟨hx.1, Metric.closedBall_subset_closedBall (max_le_max_left 0 hR) hx.2⟩
    refine ⟨A, ⟨hA, fun hx => hscale _ (hsub hx), ?_,
      fun _ hx hy => hlip _ (hsub hx) _ (hsub hy)⟩, ?_⟩
    · intro x y h
      change p.check = .exponential at h
      rw [hmode] at h
      contradiction
    · unfold thresholdCap
      change (match p.check with
        | .exponential => max 4 _ * A
        | .secant => 4 * A) ≤ 4 * A
      simp [hmode]

/-- Standard separated orders in terms of the numbers of outer and
inner steps. -/
theorem schedule_rate (p : Schedule) {Λ : ℝ} (hΛ : 0 ≤ Λ) (hM : 0 ≤ p.M) :
    gapCoefficient (p.config Λ) p.outerLast ≤
      2 * Λ / ((p.outerLast : ℝ) + 2) ^ 2 +
        4 * p.M / (((p.outerLast : ℝ) + 2) * (((p.config Λ).innerLast : ℝ) + 2)) := by
  rw [gapCoefficient_split _ _ _ rfl]
  let a := (p.outerLast : ℝ) + 2
  let b := ((p.config Λ).innerLast : ℝ) + 2
  have h₁ := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (weight_pos p.outerLast).le (weight_upper p.outerLast) 2)
    (show 0 ≤ Λ by exact hΛ)
  have h₂ := mul_le_mul_of_nonneg_right
    (mul_le_mul (weight_upper p.outerLast) (weight_upper (p.config Λ).innerLast)
      (weight_pos _).le (show 0 ≤ 2 / a by dsimp [a]; positivity)) hM
  change weight p.outerLast ^ 2 * Λ ≤ (2 / a) ^ 2 * Λ at h₁
  change weight p.outerLast * weight (p.config Λ).innerLast * p.M ≤
    (2 / a) * (2 / b) * p.M at h₂
  have he₁ : (2 / a) ^ 2 * Λ / 2 = 2 * Λ / a ^ 2 := by rw [div_pow]; ring
  have he₂ : (2 / a) * (2 / b) * p.M = 4 * p.M / (a * b) := by rw [div_mul_div_comm]; ring
  change weight p.outerLast ^ 2 * Λ / 2 + weight p.outerLast *
    weight (p.config Λ).innerLast * p.M ≤ 2 * Λ / a ^ 2 + 4 * p.M / (a * b)
  rw [← he₁, ← he₂]
  linarith only [h₁, h₂]

/-- The balance rule also bounds the entire coefficient in terms of the
outer length. This lets one prescribe the outer budget from a curvature cap. -/
theorem balanced_rate (p : Schedule) {Λ : ℝ} (hΛ : 0 < Λ) (hM : 0 < p.M) :
    gapCoefficient (p.config Λ) p.outerLast ≤ 4 * Λ / ((p.outerLast : ℝ) + 2) ^ 2 := by
  let T := (p.outerLast : ℝ) + 2
  have hbalance := p.balance hM hΛ
  calc
    gapCoefficient (p.config Λ) p.outerLast ≤ weight p.outerLast ^ 2 * Λ := by
      have hc : (Λ + weight (p.config Λ).innerLast ^ 2 * (p.config Λ).operatorCurvature) /
          2 ≤ Λ := by linarith only [hbalance]
      calc
        _ = weight p.outerLast ^ 2 *
            ((Λ + weight (p.config Λ).innerLast ^ 2 * (p.config Λ).operatorCurvature) / 2) := by
          unfold gapCoefficient
          change weight p.outerLast ^ 2 *
            (Λ + weight (p.config Λ).innerLast ^ 2 * (p.config Λ).operatorCurvature) / 2 = _
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ ≤ (2 / T) ^ 2 * Λ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (weight_pos _).le (weight_upper p.outerLast) 2) hΛ.le
    _ = _ := by change (2 / T) ^ 2 * Λ = 4 * Λ / T ^ 2; rw [div_pow]; ring

/-- The retry loop reaches a successful finite prefix even when the
bounds used to prove termination are unavailable to the algorithm. -/
theorem finite_run (p : Schedule) {C : Set E} {zin solution : E}
    (P : Projectors C zin) {f : E → ℝ} {g Q : E → E}
    (initial : Parameters) {cap : ℝ}
    (hr : 0 < initial.radius) (hInitialCurvature : 0 < initial.curvature)
    (pb : Problem p C zin solution f g Q (max initial.radius (10 * ‖zin - solution‖)) cap) :
    ∃ n b z, (search (attempt p P g Q) n initial).1 = some (b, z) := by
  let B := max initial.radius (10 * ‖zin - solution‖) * max initial.curvature (2 * cap)
  have hstart := mul_pos hr hInitialCurvature
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B / (initial.radius * initial.curvature))
    (show (1 : ℝ) < 2 by norm_num)
  obtain ⟨b, z, h, _⟩ := run_with_retries p P initial hr hInitialCurvature pb n
    ((div_lt_iff₀ hstart).mp hn)
  exact ⟨n, b, z, h⟩

end

end LeanLab.Sliding.TwoLevel
