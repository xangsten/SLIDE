module

public import LeanLab.Common.Recursive

set_option linter.style.header false

/-!
# The secant-checked recursive pass of path A

The recursion keeps the affine argument of the remaining functions and the
sum of the frozen quadratic models. A failed secant check returns its level,
threshold and the queries already made.
-/

@[expose] public section

namespace LeanLab.Sliding.PathA

open Set
open TwoLevel (Projection mix mix_mem weight_antitone weight_le_one)
open Localized (Level Model Oracle Query)
open scoped RealInnerProductSpace

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The properties of a pair used to certify a pass on its working set. -/
structure Pair.Valid (D : Set E) (p : E → ℝ) (l : Level E) : Prop where
  convex : ConvexOn ℝ D p
  smoothness_pos : 0 < l.smoothness
  lipschitz_nonneg : 0 ≤ l.lipschitz
  support : ∀ x ∈ D, ∀ y ∈ D, p x + ⟪l.gradient x, y - x⟫ ≤ p y
  monotone : ∀ x ∈ D, ∀ y ∈ D, 0 ≤ ⟪l.operator x - l.operator y, x - y⟫
  lipschitz : ∀ x ∈ D, ∀ y ∈ D, ‖l.operator x - l.operator y‖ ≤ l.lipschitz * ‖y - x‖

/-- The proof-only functions and their computational oracles in the same order. -/
abbrev Pair (E : Type*) := (E → ℝ) × Level E

structure PassFrame (E : Type*) where
  scale : ℝ
  shift : E
  terminal : ℝ
  model : Model E

def PassFrame.arg (f : PassFrame E) (x : E) : E := f.scale • x + f.shift

def PassFrame.initial : PassFrame E := ⟨1, 0, 1, ⟨0, 0⟩⟩

def regularization (l : Level E) (terminal : ℝ) : ℝ :=
  l.smoothness + 2 * l.lipschitz / (terminal * weight l.last)

def PassFrame.changeArgument (f : PassFrame E) (l : Level E) (t : ℕ) (y : E) :
    PassFrame E :=
  ⟨f.scale * weight t, f.shift + (f.scale * (1 - weight t)) • y,
    f.terminal * weight l.last, f.model⟩

def PassFrame.descend (f : PassFrame E) (l : Level E) (t : ℕ)
    (y u slope : E) : PassFrame E :=
  let f' := f.changeArgument l t y
  let H := f'.scale * regularization l f.terminal
  { f' with model := ⟨f.model.curvature + H, f.model.linear + (slope - H • u)⟩ }

@[simp] theorem PassFrame.changeArgument_arg (f : PassFrame E) (l : Level E) (t : ℕ)
    (y u : E) : (f.changeArgument l t y).arg u = f.arg (mix (weight t) y u) := by
  simp only [PassFrame.changeArgument, PassFrame.arg, mix, smul_add, mul_smul]
  abel

structure Centers (E : Type*) where
  average : E
  atLevel : ℕ → E

structure Request where
  level : ℕ
  threshold : ℝ

structure Attempt (E : Type*) where
  outcome : Except Request (Centers E)
  queries : List (Query E)
  projections : ℕ

def secant (l : Level E) (x y : E) (g : E) : ℝ :=
  if x = y then 0 else 2 * ⟪l.gradient y - g, y - x⟫ / ‖y - x‖ ^ 2

/-- State after a successful correction, using the centers returned by the child. -/
def corrected {D : Set E} (P : Projection D) (l : Level E) (f : PassFrame E)
    (k t : ℕ) (s child : Centers E) (q : E) : Centers E :=
  let v := child.average
  let H := (f.changeArgument l t s.average).scale * regularization l f.terminal
  ⟨mix (weight t) s.average v,
    Function.update child.atLevel k (P.apply (v + H⁻¹ • (q - l.operator v)))⟩

def passStep {D : Set E} (P : Projection D) (l : Level E) (f : PassFrame E) (k t : ℕ)
    (child : PassFrame E → (ℕ → E) → Attempt E) (s : Centers E) : Attempt E :=
  let u := s.atLevel k
  let f' := f.changeArgument l t s.average
  let x := f'.arg u
  let g := l.gradient x
  let q := l.operator u
  let inner := child (f.descend l t s.average u (g + q)) s.atLevel
  let before := [⟨k, Oracle.gradient, x⟩, ⟨k, Oracle.operator, u⟩] ++ inner.queries
  match inner.outcome with
  | .error request => ⟨.error request, before, inner.projections⟩
  | .ok next =>
    let x' := f'.arg next.average
    let checked := if x = x' then before else before ++ [⟨k, Oracle.gradient, x'⟩]
    let τ := secant l x x' g
    if l.smoothness < τ then ⟨.error ⟨k, τ⟩, checked, inner.projections⟩
    else ⟨.ok (corrected P l f k t s next q), checked ++ [⟨k, Oracle.operator, next.average⟩],
      inner.projections + 1⟩

def passCycle {D : Set E} (P : Projection D) (l : Level E) (f : PassFrame E) (k : ℕ)
    (child : PassFrame E → (ℕ → E) → Attempt E) (centers : ℕ → E) : ℕ → Attempt E
  | 0 => ⟨.ok ⟨centers k, centers⟩, [], 0⟩
  | t + 1 =>
    let prev := passCycle P l f k child centers t
    match prev.outcome with
    | .error _ => prev
    | .ok s =>
      let next := passStep P l f k t child s
      ⟨next.outcome, prev.queries ++ next.queries, prev.projections + next.projections⟩

def runPass {D : Set E} (P : Projection D) :
    List (Pair E) → ℕ → PassFrame E → (ℕ → E) → Attempt E
  | [], _, f, centers =>
    ⟨.ok ⟨P.apply (-(f.model.curvature)⁻¹ • f.model.linear), centers⟩, [], 1⟩
  | (_, l) :: tail, k, f, centers =>
    passCycle P l f k (runPass P tail (k + 1)) centers (l.last + 1)

def adaptivePass {D : Set E} (P : Projection D) (pairs : List (Pair E)) (s : E) : Attempt E :=
  runPass P pairs 0 PassFrame.initial (fun _ => s)

/-- Successful steps expose the accepted secant and the precise child state. -/
private theorem passStep_ok {D : Set E} (P : Projection D) (l : Level E) (f : PassFrame E)
    (k t : ℕ) (child : PassFrame E → (ℕ → E) → Attempt E) {s out : Centers E}
    (h : (passStep P l f k t child s).outcome = .ok out) :
    let u := s.atLevel k
    let f' := f.changeArgument l t s.average
    let x := f'.arg u
    ∃ v, (child (f.descend l t s.average u (l.gradient x + l.operator u)) s.atLevel).outcome =
        .ok v ∧ secant l x (f'.arg v.average) (l.gradient x) ≤ l.smoothness ∧
        out = corrected P l f k t s v (l.operator u) := by
  dsimp only [passStep] at h ⊢
  split at h
  · simp at h
  · rename_i v hv
    split at h
    · simp at h
    · rename_i hτ
      exact ⟨v, hv, le_of_not_gt hτ, by simpa only [Except.ok.injEq] using h.symm⟩

private theorem cycle_ok_succ {D : Set E} (P : Projection D) (l : Level E) (f : PassFrame E)
    (k : ℕ) (child : PassFrame E → (ℕ → E) → Attempt E) (centers : ℕ → E) (t : ℕ)
    {out : Centers E} (h : (passCycle P l f k child centers (t + 1)).outcome = .ok out) :
    ∃ s, (passCycle P l f k child centers t).outcome = .ok s ∧
      (passStep P l f k t child s).outcome = .ok out := by
  cases hp : (passCycle P l f k child centers t).outcome with
  | error req => simp [passCycle, hp] at h
  | ok s => exact ⟨s, rfl, by simpa only [passCycle, hp] using h⟩

/-- A prefix of a successful cycle has a successful state. -/
private theorem cycle_ok_prefix {D : Set E} (P : Projection D) (l : Level E)
    (f : PassFrame E) (k : ℕ) (child : PassFrame E → (ℕ → E) → Attempt E)
    (centers : ℕ → E) {n m : ℕ} (hm : m ≤ n) {out : Centers E}
    (h : (passCycle P l f k child centers n).outcome = .ok out) :
    ∃ s, (passCycle P l f k child centers m).outcome = .ok s := by
  induction n generalizing out with
  | zero => cases Nat.eq_zero_of_le_zero hm; exact ⟨out, h⟩
  | succ n ih =>
    rcases eq_or_lt_of_le hm with rfl | hlt
    · exact ⟨out, h⟩
    · obtain ⟨s, hs, _⟩ := cycle_ok_succ P l f k child centers n h
      exact ih (Nat.le_of_lt_succ hlt) hs

/-- The point transformations and the accumulated quadratic stay admissible. -/
structure PassFrame.Valid (D : Set E) (f : PassFrame E) : Prop where
  scale_pos : 0 < f.scale
  terminal_pos : 0 < f.terminal
  terminal_le_scale : f.terminal ≤ f.scale
  maps : MapsTo f.arg D D
  model_nonneg : 0 ≤ f.model.curvature
  model_zero : f.model.curvature = 0 → f.model.linear = 0

theorem PassFrame.initial_valid (D : Set E) : PassFrame.Valid D (PassFrame.initial : PassFrame E) :=
  ⟨zero_lt_one, zero_lt_one, le_rfl, by simp [PassFrame.initial, PassFrame.arg, MapsTo],
    le_rfl, fun _ => rfl⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
private theorem regularization_pos (l : Level E) {terminal : ℝ} (hterminal : 0 < terminal)
    (hΛ : 0 < l.smoothness) (hM : 0 ≤ l.lipschitz) : 0 < regularization l terminal :=
  add_pos_of_pos_of_nonneg hΛ
    (div_nonneg (by positivity) (mul_nonneg hterminal.le (weight_pos _).le))

private theorem PassFrame.descend_valid {D : Set E} {f : PassFrame E} (hf : f.Valid D)
    {p : E → ℝ} {l : Level E} (hp : Pair.Valid D p l) {t : ℕ} (ht : t ≤ l.last)
    {y : E} (hy : y ∈ D) (u slope : E) : (f.descend l t y u slope).Valid D := by
  have hscale := mul_pos hf.scale_pos (weight_pos t)
  have hcurv := add_pos_of_nonneg_of_pos hf.model_nonneg
    (mul_pos hscale (regularization_pos l hf.terminal_pos hp.smoothness_pos hp.lipschitz_nonneg))
  refine ⟨hscale, mul_pos hf.terminal_pos (weight_pos _),
    mul_le_mul hf.terminal_le_scale (weight_antitone ht) (weight_pos _).le hf.scale_pos.le,
    ?_, hcurv.le, fun hz => (hcurv.ne' hz).elim⟩
  change MapsTo (f.changeArgument l t y).arg D D
  intro x hx
  rw [PassFrame.changeArgument_arg]
  exact hf.maps (mix_mem hp.convex.1 (weight_pos _).le (weight_le_one _) hy hx)

def objective : List (Pair E) → E → ℝ
  | [], _ => 0
  | (p, _) :: tail, x => p x + objective tail x

def operatorSum : List (Pair E) → E → E
  | [], _ => 0
  | (_, l) :: tail, x => l.operator x + operatorSum tail x

def scaledObjective (pairs : List (Pair E)) (f : PassFrame E) (z : E) : ℝ :=
  objective pairs (f.arg z) / f.scale

def carried (pairs : List (Pair E)) (f : PassFrame E) (w z : E) : ℝ :=
  model f.model.curvature (0 : E) f.model.linear z +
    f.model.curvature / 2 * ‖z - w‖ ^ 2 + ⟪operatorSum pairs w, z⟫

/-- The mixed gap in (A.7), including the frozen quadratics. -/
def passGap (pairs : List (Pair E)) (f : PassFrame E) (z w : E) : ℝ :=
  scaledObjective pairs f z + carried pairs f w z -
    (scaledObjective pairs f w + carried pairs f w w)

theorem passGap_initial (pairs : List (Pair E)) (z w : E) :
    passGap pairs PassFrame.initial z w = gap (objective pairs) (operatorSum pairs) z w := by
  simp [passGap, scaledObjective, carried, model, PassFrame.initial, PassFrame.arg, gap,
    inner_sub_right]
  ring

theorem convex_objective {D : Set E} (hD : Convex ℝ D)
    {pairs : List (Pair E)} (h : ∀ pair ∈ pairs, Pair.Valid D pair.1 pair.2) :
    ConvexOn ℝ D (objective pairs) := by
  induction pairs with
  | nil => exact convexOn_const _ hD
  | cons pair tail ih =>
    exact (h pair List.mem_cons_self).convex.add
      (ih fun p hp => h p (List.mem_cons_of_mem _ hp))

private theorem convex_scaled {D : Set E} (hD : Convex ℝ D) {pairs : List (Pair E)}
    (h : ∀ pair ∈ pairs, Pair.Valid D pair.1 pair.2) {f : PassFrame E} (hf : f.Valid D) :
    ConvexOn ℝ D (scaledObjective pairs f) := by
  let T : E →ᵃ[ℝ] E := f.scale • AffineMap.id ℝ E + AffineMap.const ℝ E f.shift
  have hT : MapsTo T D D := hf.maps
  have hc := ((convex_objective hD h).comp_affineMap T).subset hT hD
  change ConvexOn ℝ D (fun z => objective pairs (T z) / f.scale)
  simpa only [div_eq_inv_mul, smul_eq_mul, Function.comp_apply] using
    hc.smul (inv_nonneg.mpr hf.scale_pos.le)

private theorem convex_carried {D : Set E} (hD : Convex ℝ D) {pairs : List (Pair E)}
    {f : PassFrame E} (hf : f.Valid D) (w : E) : ConvexOn ℝ D (carried pairs f w) := by
  have hsq (a : E) : ConvexOn ℝ D (fun z => ‖z - a‖ ^ 2) := by
    change ConvexOn ℝ D ((fun z => ‖z - a‖) ^ (2 : ℕ))
    simpa only [dist_eq_norm] using (convexOn_dist a hD).pow (fun _ _ => dist_nonneg) 2
  have hlin (a : E) : ConvexOn ℝ D (fun z => ⟪a, z⟫) :=
    (innerSL ℝ a).toLinearMap.convexOn hD
  have hH : 0 ≤ f.model.curvature / 2 := by positivity [hf.model_nonneg]
  exact ((((hsq 0).smul hH).add (hlin f.model.linear)).add ((hsq w).smul hH)).add
    (hlin (operatorSum pairs w))

/-- Weights for the outgoing centers in (A.7), before multiplication by β/2. -/
def centerEnergy (w : E) (U : ℕ → E) : List (Pair E) → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | (_, l) :: tail, k, terminal =>
    weight l.last ^ 2 * (regularization l terminal * ‖U k - w‖ ^ 2 +
      centerEnergy w U tail (k + 1) (terminal * weight l.last))

omit [InnerProductSpace ℝ E] in
private theorem centerEnergy_update_before (w : E) (U : ℕ → E) (pairs : List (Pair E))
    {j k : ℕ} (hjk : j < k) (z : E) (terminal : ℝ) :
    centerEnergy w (Function.update U j z) pairs k terminal =
      centerEnergy w U pairs k terminal := by
  induction pairs generalizing k terminal with
  | nil => rfl
  | cons l tail ih =>
    rcases l with ⟨p, l⟩
    simp only [centerEnergy, Function.update_of_ne (ne_of_gt hjk),
      ih (hjk.trans (Nat.lt_succ_self k))]

private theorem centerEnergy_nonneg {D : Set E} {pairs : List (Pair E)}
    (hp : ∀ pair ∈ pairs, Pair.Valid D pair.1 pair.2) (w : E) (U : ℕ → E) (k : ℕ)
    {terminal : ℝ} (ht : 0 < terminal) : 0 ≤ centerEnergy w U pairs k terminal := by
  induction pairs generalizing k terminal with
  | nil => exact le_rfl
  | cons pair tail ih =>
    rcases pair with ⟨p, l⟩
    have hv := hp (p, l) List.mem_cons_self
    have hr := regularization_pos l ht hv.smoothness_pos hv.lipschitz_nonneg
    have he := ih (fun pair h => hp pair (List.mem_cons_of_mem _ h)) (k + 1)
      (mul_pos ht (weight_pos l.last))
    exact mul_nonneg (sq_nonneg _) (add_nonneg (mul_nonneg hr.le (sq_nonneg _)) he)

private theorem scaled_part_step (pairs : List (Pair E)) (f : PassFrame E) (l : Level E)
    (t : ℕ) (y z : E) :
    scaledObjective pairs (f.changeArgument l t y) z =
      scaledObjective pairs f (mix (weight t) y z) / weight t := by
  unfold scaledObjective
  rw [PassFrame.changeArgument_arg, div_div]
  rfl

private theorem upper_of_check {D : Set E} {p : E → ℝ} {l : Level E} (hp : Pair.Valid D p l)
    {x y : E} (hx : x ∈ D) (hy : y ∈ D) (hτ : secant l x y (l.gradient x) ≤ l.smoothness) :
    p y ≤ p x + ⟪l.gradient x, y - x⟫ + l.smoothness / 2 * ‖y - x‖ ^ 2 := by
  by_cases he : x = y
  · subst y
    simp
  have hpos : 0 < ‖y - x‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm he)))
  simp only [secant, ite_eq_right he] at hτ
  have hτ' := (div_le_iff₀ hpos).mp hτ
  have hs := hp.support y hy x hx
  rw [show x - y = -(y - x) by abel, inner_neg_right] at hs
  rw [inner_sub_left] at hτ'
  linarith only [hτ', hs]

private theorem model_recenter (H : ℝ) (u d z : E) :
    model H 0 (d - H • u) z = model H u d z - H / 2 * ‖u‖ ^ 2 := by
  simp only [model, sub_zero, inner_sub_left, real_inner_smul_left, norm_sub_sq_real,
    real_inner_comm z u]
  ring

private theorem carried_descend (p : E → ℝ) (l : Level E) (tail : List (Pair E))
    (f : PassFrame E) (t : ℕ) (y u d w z : E) :
    let H := (f.changeArgument l t y).scale * regularization l f.terminal
    carried tail (f.descend l t y u d) w z + ⟪l.operator w, z⟫ =
      carried ((p, l) :: tail) f w z + model H u d z + H / 2 * ‖z - w‖ ^ 2 -
        H / 2 * ‖u‖ ^ 2 := by
  let H := (f.changeArgument l t y).scale * regularization l f.terminal
  have hh := model_recenter H u d z
  dsimp only [carried, PassFrame.descend, PassFrame.changeArgument, operatorSum] at *
  simp only [model, inner_add_left] at hh ⊢
  dsimp only [H, PassFrame.changeArgument] at hh
  linear_combination hh

/-- The parent comparison (A.5) and convex transfer for an accepted step. -/
private theorem pass_transfer {D : Set E} (P : Projection D) {p : E → ℝ} {l : Level E}
    {tail : List (Pair E)} (hpair : Pair.Valid D p l)
    (htail : ∀ pair ∈ tail, Pair.Valid D pair.1 pair.2)
    {f : PassFrame E} (hf : f.Valid D) {t : ℕ} (ht : t ≤ l.last)
    {y u v w : E} (hy : y ∈ D) (hu : u ∈ D) (hv : v ∈ D) (hw : w ∈ D)
    (hτ : secant l ((f.changeArgument l t y).arg u) ((f.changeArgument l t y).arg v)
      (l.gradient ((f.changeArgument l t y).arg u)) ≤ l.smoothness) :
    let α := weight t
    let f' := f.changeArgument l t y
    let g := l.gradient (f'.arg u)
    let d := g + l.operator u
    let H := f'.scale * regularization l f.terminal
    let z := P.apply (v + H⁻¹ • (l.operator u - l.operator v))
    (passGap ((p, l) :: tail) f (mix α y v) w -
      (1 - α) * passGap ((p, l) :: tail) f y w) / α +
      H / 2 * (‖z - w‖ ^ 2 - ‖u - w‖ ^ 2) ≤
      passGap tail (f.descend l t y u d) v w := by
  let α := weight t
  let F := f.changeArgument l t y
  let g := l.gradient (F.arg u)
  let d := g + l.operator u
  let H := F.scale * regularization l f.terminal
  let z := P.apply (v + H⁻¹ • (l.operator u - l.operator v))
  let G := f.descend l t y u d
  let p' := fun z => p (F.arg z) / F.scale
  let correction := H / 2 * (‖z - w‖ ^ 2 - ‖u - w‖ ^ 2)
  have hg := PassFrame.descend_valid hf hpair ht hy u d
  have hβ : 0 < F.scale := hg.scale_pos
  have hH : 0 < H := mul_pos hβ
    (regularization_pos l hf.terminal_pos hpair.smoothness_pos hpair.lipschitz_nonneg)
  have hcurv : F.scale * l.smoothness + 2 * l.lipschitz ≤ H :=
    accepted_curvature hg.terminal_pos hg.terminal_le_scale le_rfl hpair.lipschitz_nonneg
  have hm (a : E) (ha : a ∈ D) : F.arg a ∈ D := hg.maps ha
  have hupper : p' v ≤ p' u + ⟪g, v - u⟫ + (F.scale * l.smoothness) / 2 * ‖v - u‖ ^ 2 :=
    affine_model hβ (upper_of_check hpair (hm u hu) (hm v hv) hτ)
  have hsupp : p' u + ⟪g, w - u⟫ ≤ p' w := by
    have hsub : F.arg w - F.arg u = F.scale • (w - u) := by
      unfold PassFrame.arg
      module
    have hs := hpair.support (F.arg u) (hm u hu) (F.arg w) (hm w hw)
    rw [hsub, real_inner_smul_right] at hs
    apply (le_div_iff₀ hβ).mpr
    dsimp only [p', g]
    rw [add_mul, div_mul_cancel₀ _ hβ.ne']
    linarith only [hs]
  have hcomp := model_comparison hH (mul_nonneg hβ.le hpair.smoothness_pos.le)
    hpair.lipschitz_nonneg hcurv hupper hsupp (hpair.monotone v hv w hw)
    (hpair.lipschitz u hu v hv) (P.normal (v + H⁻¹ • (l.operator u - l.operator v)) hw)
  change gap p' l.operator v w + correction ≤ _ at hcomp
  have he (b : E) :
      scaledObjective ((p, l) :: tail) F b = p' b + scaledObjective tail G b := by
    unfold scaledObjective p'
    change (p (F.arg b) + objective tail (F.arg b)) / F.scale = _
    rw [add_div]
    rfl
  have hcv := carried_descend p l tail f t y u d w v
  have hcw := carried_descend p l tail f t y u d w w
  dsimp only at hcv hcw
  change carried tail G w v + _ = carried ((p, l) :: tail) f w v +
    model H u d v + H / 2 * ‖v - w‖ ^ 2 - _ at hcv
  change carried tail G w w + _ = carried ((p, l) :: tail) f w w +
    model H u d w + H / 2 * ‖w - w‖ ^ 2 - _ at hcw
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hcw
  have hstep : scaledObjective ((p, l) :: tail) F v - scaledObjective ((p, l) :: tail) F w +
      (carried ((p, l) :: tail) f w v - carried ((p, l) :: tail) f w w) + correction ≤
      passGap tail G v w := by
    rw [he v, he w]
    simp only [gap, inner_sub_right] at hcomp
    unfold passGap
    linarith only [hcomp, hcv, hcw]
  have hvalid : ∀ pair ∈ (p, l) :: tail, Pair.Valid D pair.1 pair.2 := by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hpair
    · exact htail pair hm
  have htransfer := transfer
    (convex_scaled hpair.convex.1 hvalid hf)
    (convex_carried (pairs := (p, l) :: tail) hpair.convex.1 hf w)
    hy hv hw (weight_pos t) (weight_le_one t) (child := passGap tail G v w)
    (correction := correction) (by
      change (scaledObjective ((p, l) :: tail) f (mix α y v) -
        scaledObjective ((p, l) :: tail) f (mix α y w)) / α +
        (carried ((p, l) :: tail) f w v - carried ((p, l) :: tail) f w w) +
        correction ≤ passGap tail G v w
      dsimp only [F] at hstep
      rw [scaled_part_step, scaled_part_step] at hstep
      simpa only [sub_div, α] using hstep)
  exact htransfer

def Centers.Feasible (D : Set E) (s : Centers E) : Prop :=
  s.average ∈ D ∧ ∀ i, s.atLevel i ∈ D

/-- Feasibility and the mixed-gap estimate for successful outcomes of a level. -/
def PassCertificate (D : Set E) (pairs : List (Pair E)) (k : ℕ)
    (run : PassFrame E → (ℕ → E) → Attempt E) : Prop :=
  ∀ f, f.Valid D → ∀ U, (∀ i, U i ∈ D) → ∀ out, (run f U).outcome = .ok out →
    out.Feasible D ∧ ∀ w ∈ D, passGap pairs f out.average w ≤ f.scale / 2 *
      (centerEnergy w U pairs k f.terminal - centerEnergy w out.atLevel pairs k f.terminal)

/-- The potential for a prefix of one cycle, before its last weight is applied. -/
def cycleEnergy (p : Pair E) (tail : List (Pair E)) (k : ℕ)
    (f : PassFrame E) (w : E) (U : ℕ → E) : ℝ :=
  f.scale / 2 * (regularization p.2 f.terminal * ‖U k - w‖ ^ 2 +
    centerEnergy w U tail (k + 1) (f.terminal * weight p.2.last))

private theorem passStep_correct {D : Set E} (P : Projection D) {p : E → ℝ} {l : Level E}
    {tail : List (Pair E)} (hp : Pair.Valid D p l)
    (htail : ∀ pair ∈ tail, Pair.Valid D pair.1 pair.2)
    {f : PassFrame E} (hf : f.Valid D) {k t : ℕ} (ht : t ≤ l.last)
    {child : PassFrame E → (ℕ → E) → Attempt E} (hc : PassCertificate D tail (k + 1) child)
    {s out : Centers E} (hs : s.Feasible D)
    (hout : (passStep P l f k t child s).outcome = .ok out) :
    out.Feasible D ∧ ∀ w ∈ D,
      (passGap ((p, l) :: tail) f out.average w -
        (1 - weight t) * passGap ((p, l) :: tail) f s.average w) / weight t ^ 2 ≤
        cycleEnergy (p, l) tail k f w s.atLevel - cycleEnergy (p, l) tail k f w out.atLevel := by
  let u := s.atLevel k
  let F := f.changeArgument l t s.average
  let q := l.operator u
  let d := l.gradient (F.arg u) + q
  let G := f.descend l t s.average u d
  obtain ⟨v, hv, hτ, rfl⟩ := passStep_ok P l f k t child hout
  have hG := PassFrame.descend_valid hf hp ht hs.1 u d
  have hvf := hc G hG s.atLevel hs.2 v hv
  refine ⟨?_, ?_⟩
  · refine ⟨mix_mem hp.convex.1 (weight_pos _).le (weight_le_one _) hs.1 hvf.1.1, ?_⟩
    intro i
    by_cases hi : i = k
    · subst i
      simpa only [corrected, Function.update_self] using
        P.feasible (v.average + (F.scale * regularization l f.terminal)⁻¹ •
          (q - l.operator v.average))
    · simpa only [corrected, Function.update_of_ne hi] using hvf.1.2 i
  · intro w hw
    have htransfer := pass_transfer P hp htail hf ht hs.1 (hs.2 k) hvf.1.1 hw hτ
    dsimp only at htransfer
    have hchild := hvf.2 w hw
    change passGap tail G v.average w ≤ f.scale * weight t / 2 *
      (centerEnergy w s.atLevel tail (k + 1) (f.terminal * weight l.last) -
        centerEnergy w v.atLevel tail (k + 1) (f.terminal * weight l.last)) at hchild
    have hh := iteration_bound (β := f.scale) (c := regularization l f.terminal)
      (weight_pos t) htransfer hchild
    change _ ≤ cycleEnergy (p, l) tail k f w s.atLevel -
      cycleEnergy (p, l) tail k f w (corrected P l f k t s v q).atLevel
    simp only [cycleEnergy, corrected, Function.update_self,
      centerEnergy_update_before w v.atLevel tail (Nat.lt_succ_self k)]
    rw [mul_sub] at hh
    exact hh

private theorem passCycle_correct {D : Set E} (P : Projection D) {p : E → ℝ} {l : Level E}
    {tail : List (Pair E)} (hp : Pair.Valid D p l)
    (htail : ∀ pair ∈ tail, Pair.Valid D pair.1 pair.2)
    {f : PassFrame E} (hf : f.Valid D) (k : ℕ)
    {child : PassFrame E → (ℕ → E) → Attempt E} (hc : PassCertificate D tail (k + 1) child)
    (U : ℕ → E) (hU : ∀ i, U i ∈ D) {n : ℕ} (hn : n ≤ l.last)
    {out : Centers E} (hout : (passCycle P l f k child U (n + 1)).outcome = .ok out) :
    out.Feasible D ∧ ∀ w ∈ D, passGap ((p, l) :: tail) f out.average w ≤
      weight n ^ 2 * (cycleEnergy (p, l) tail k f w U -
        cycleEnergy (p, l) tail k f w out.atLevel) := by
  let C := passCycle P l f k child U
  have feasible (m : ℕ) (hm : m ≤ l.last + 1) (s : Centers E) (hs : (C m).outcome = .ok s) :
      s.Feasible D := by
    induction m generalizing s with
    | zero =>
      have hh : s = ⟨U k, U⟩ := by simpa only [C, passCycle, Except.ok.injEq] using hs.symm
      rw [hh]
      exact ⟨hU k, hU⟩
    | succ m ih =>
      obtain ⟨prev, hprev, hstep⟩ := cycle_ok_succ P l f k child U m hs
      have hm' : m ≤ l.last := Nat.le_of_succ_le_succ hm
      exact (passStep_correct P hp htail hf hm' hc
        (ih (hm'.trans (Nat.le_succ _)) prev hprev) hstep).1
  refine ⟨feasible _ (Nat.succ_le_succ hn) out hout, ?_⟩
  intro w hw
  let S : ℕ → Centers E := fun t => ((C t).outcome.toOption).getD ⟨U k, U⟩
  have select {m : ℕ} {s : Centers E} (hs : (C m).outcome = .ok s) : S m = s := by
    dsimp only [S]
    rw [hs]
    rfl
  have hbase : S 0 = ⟨U k, U⟩ := rfl
  have hend : S (n + 1) = out := select hout
  have htel := telescope (α := weight)
    (F := fun t => passGap ((p, l) :: tail) f (S t).average w)
    (P := fun t => cycleEnergy (p, l) tail k f w (S t).atLevel)
    weight_pos weight_zero weight_recurrence n (by
      intro j hj
      obtain ⟨next, hnext⟩ := cycle_ok_prefix P l f k child U (Nat.succ_le_succ hj) hout
      obtain ⟨prev, hprev, hstep⟩ := cycle_ok_succ P l f k child U j hnext
      rw [select hprev, select hnext]
      have hj' := hj.trans hn
      have hprev' := feasible j (hj'.trans (Nat.le_succ _)) prev hprev
      exact (passStep_correct P hp htail hf hj' hc hprev' hstep).2 w hw)
  simpa only [hbase, hend] using htel

/-- The accepted recursive pass satisfies (A.7) at arbitrary depth. -/
theorem runPass_correct {D : Set E} (P : Projection D)
    (pairs : List (Pair E)) (hp : ∀ pair ∈ pairs, Pair.Valid D pair.1 pair.2) (k : ℕ) :
    PassCertificate D pairs k (runPass P pairs k) := by
  induction pairs generalizing k with
  | nil =>
    intro f hf U hU out hout
    have he : out = ⟨P.apply (-(f.model.curvature)⁻¹ • f.model.linear), U⟩ := by
      simpa only [runPass, Except.ok.injEq] using hout.symm
    subst out
    refine ⟨⟨P.feasible _, hU⟩, ?_⟩
    intro w hw
    simp only [centerEnergy, sub_self, mul_zero]
    rcases eq_or_lt_of_le hf.model_nonneg with hzero | hpos
    · simp [passGap, scaledObjective, objective, carried, operatorSum, model,
        ← hzero, hf.model_zero hzero.symm]
    · have hh := Localized.projected_model_bound P hpos 0 f.model.linear hw
      simp [model, smul_neg] at hh
      simp [passGap, scaledObjective, objective, carried, operatorSum, model]
      linarith only [hh]
  | cons pair tail ih =>
    rcases pair with ⟨p, l⟩
    intro f hf U hU out hout
    have htail (pair : Pair E) (h : pair ∈ tail) := hp pair (List.mem_cons_of_mem _ h)
    have hh := passCycle_correct P (hp (p, l) List.mem_cons_self) htail hf k
      (ih htail (k + 1)) U hU (le_refl l.last) hout
    refine ⟨hh.1, ?_⟩
    intro w hw
    refine (hh.2 w hw).trans_eq ?_
    simp only [cycleEnergy, centerEnergy]
    ring

/-- Accepted passes certify the gap on the working set with the path-A center weights. -/
theorem adaptivePass_gap {D : Set E} (P : Projection D)
    (pairs : List (Pair E)) (hp : ∀ pair ∈ pairs, Pair.Valid D pair.1 pair.2)
    {s : E} (hs : s ∈ D) {out : Centers E} (ho : (adaptivePass P pairs s).outcome = .ok out) :
    out.Feasible D ∧ ∀ w ∈ D, gap (objective pairs) (operatorSum pairs) out.average w ≤
      centerEnergy w (fun _ => s) pairs 0 1 / 2 := by
  have hh := runPass_correct P pairs hp 0 PassFrame.initial (PassFrame.initial_valid D)
    (fun _ => s) (fun _ => hs) out ho
  refine ⟨hh.1, ?_⟩
  intro w hw
  have he := centerEnergy_nonneg hp w out.atLevel 0 (show (0 : ℝ) < 1 by norm_num)
  have h := hh.2 w hw
  rw [passGap_initial] at h
  change _ ≤ 1 / 2 * (centerEnergy w (fun _ => s) pairs 0 1 -
    centerEnergy w out.atLevel pairs 0 1) at h
  linarith only [h, he]

/-- The completed pass remains close enough to the solution for the radius
test, provided the tail of the initial potential is balanced by the root. -/
theorem adaptivePass_radius {D : Set E} (P : Projection D) {p : E → ℝ} {l : Level E}
    {tail : List (Pair E)} (hp : Pair.Valid D p l)
    (htail : ∀ pair ∈ tail, Pair.Valid D pair.1 pair.2)
    {s w : E} (hs : s ∈ D) (hw : w ∈ D)
    (hgap : ∀ z ∈ D, 0 ≤ passGap ((p, l) :: tail) PassFrame.initial z w)
    (hbalance : centerEnergy w (fun _ => s) tail 1 (weight l.last) ≤
      regularization l 1 * ‖s - w‖ ^ 2)
    {out : Centers E} (hout : (adaptivePass P ((p, l) :: tail) s).outcome = .ok out) :
    ‖out.average - s‖ ≤ (1 + 3 * Real.sqrt 2) * ‖s - w‖ := by
  let F : PassFrame E := PassFrame.initial
  let U : ℕ → E := fun _ => s
  let child := runPass P tail 1
  let A := passCycle P l F 0 child U
  let c := regularization l 1
  let r := ‖s - w‖
  have hF : F.Valid D := PassFrame.initial_valid D
  have hchild : PassCertificate D tail 1 child := runPass_correct P tail htail 1
  have hc : 0 < c := regularization_pos l zero_lt_one hp.smoothness_pos hp.lipschitz_nonneg
  have hr : 0 ≤ r := norm_nonneg _
  have hsqrt : 1 ≤ Real.sqrt 2 := by
    simp
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsmall : r ≤ Real.sqrt 2 * r := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hsqrt)]
  have hcenter (t : ℕ) (ht : t ≤ l.last + 1) {state : Centers E}
      (hstate : (A t).outcome = .ok state) :
      state.Feasible D ∧ ‖state.atLevel 0 - w‖ ≤ Real.sqrt 2 * r := by
    cases t with
    | zero =>
      have he : state = ⟨s, U⟩ := by simpa only [A, passCycle, Except.ok.injEq] using hstate.symm
      rw [he]
      exact ⟨⟨hs, fun _ => hs⟩, hsmall⟩
    | succ j =>
      have hj : j ≤ l.last := Nat.le_of_succ_le_succ ht
      have hh := passCycle_correct P hp htail hF 0 hchild U (fun _ => hs) hj hstate
      refine ⟨hh.1, ?_⟩
      have hnon := hgap _ hh.1.1
      have hE := (mul_nonneg_iff_of_pos_left (sq_pos_of_pos (weight_pos j))).mp
        (hnon.trans (hh.2 w hw))
      have htail' := centerEnergy_nonneg htail w state.atLevel 1 (weight_pos l.last)
      change 0 ≤ 1 / 2 * (c * r ^ 2 +
        centerEnergy w U tail 1 (1 * weight l.last)) -
        1 / 2 * (c * ‖state.atLevel 0 - w‖ ^ 2 +
          centerEnergy w state.atLevel tail 1 (1 * weight l.last)) at hE
      simp only [one_mul] at hE
      have hmul : c * ‖state.atLevel 0 - w‖ ^ 2 ≤ c * (2 * r ^ 2) := by
        linarith only [hE, htail', hbalance]
      have hsq := le_of_mul_le_mul_left hmul hc
      apply le_of_sq_le_sq _ (by positivity)
      rwa [mul_pow, hsqrt2]
  have haverage (t : ℕ) (ht : t ≤ l.last + 1) {state : Centers E}
      (hstate : (A t).outcome = .ok state) : ‖state.average - w‖ ≤ 3 * Real.sqrt 2 * r := by
    induction t generalizing state with
    | zero =>
      have he : state = ⟨s, U⟩ := by simpa only [A, passCycle, Except.ok.injEq] using hstate.symm
      rw [he]
      change r ≤ 3 * Real.sqrt 2 * r
      linarith only [hsmall, mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) hr]
    | succ j ih =>
      obtain ⟨prev, hprev, hstep⟩ := cycle_ok_succ P l F 0 child U j hstate
      have hj := Nat.le_of_succ_le_succ ht
      have hj' : j ≤ l.last + 1 := hj.trans (Nat.le_succ _)
      have hprevC := hcenter j hj' hprev
      have hstateC := hcenter (j + 1) ht hstate
      have hprevA := ih hj' hprev
      obtain ⟨v, hv, _, he⟩ := passStep_ok P l F 0 j child hstep
      let u := prev.atLevel 0
      let H := (F.changeArgument l j prev.average).scale * regularization l F.terminal
      let z := P.apply (v.average + H⁻¹ • (l.operator u - l.operator v.average))
      let G := F.descend l j prev.average u
        (l.gradient ((F.changeArgument l j prev.average).arg u) + l.operator u)
      have hG : G.Valid D := PassFrame.descend_valid hF hp hj hprevC.1.1 u
        (l.gradient ((F.changeArgument l j prev.average).arg u) + l.operator u)
      have hvD := (hchild G hG prev.atLevel hprevC.1.2 v hv).1.1
      have hH : 0 < H := mul_pos hG.scale_pos hc
      have hm := accepted_curvature hG.terminal_pos hG.terminal_le_scale
        (le_refl l.smoothness) hp.lipschitz_nonneg
      have hM : 2 * l.lipschitz ≤ H := by
        have hn : 0 ≤ G.scale * l.smoothness :=
          mul_nonneg hG.scale_pos.le hp.smoothness_pos.le
        change _ + 2 * l.lipschitz ≤ H at hm
        linarith only [hm, hn]
      have hz : state.atLevel 0 = z := by
        rw [he]
        simp only [corrected, Function.update_self, z, u, H]
      have hmove : ‖v.average - z‖ ≤ ‖v.average - u‖ / 2 :=
        correction_move hH hM (hp.lipschitz u (hprevC.1.2 0) v.average hvD)
          (P.normal _ hvD)
      have hvR := trial_radius hprevC.2 (hz ▸ hstateC.2) hmove
      have hR : (0 : ℝ) ≤ 3 * Real.sqrt 2 * r := by positivity
      have hb := mix_mem (convex_closedBall w (3 * Real.sqrt 2 * r))
        (weight_pos j).le (weight_le_one j)
        (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hprevA)
        (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hvR)
      rw [he]
      simpa only [corrected, Metric.mem_closedBall, dist_eq_norm] using hb
  have havg := haverage _ le_rfl hout
  have he : out.average - s = (out.average - w) + (w - s) := by abel
  rw [he]
  have htri := norm_add_le (out.average - w) (w - s)
  rw [norm_sub_rev w s] at htri
  change _ ≤ ‖out.average - w‖ + r at htri
  exact htri.trans (by nlinarith only [havg])

/-- A uniform Lipschitz bound controls the secant on the working set. -/
theorem secant_le_of_lipschitz {l : Level E} {x y : E} {L : ℝ} (hL : 0 ≤ L)
    (h : ‖l.gradient y - l.gradient x‖ ≤ L * ‖y - x‖) :
    secant l x y (l.gradient x) ≤ 2 * L := by
  by_cases he : x = y
  · subst y
    simpa [secant] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL
  simp only [secant, ite_eq_right he]
  have hpos : 0 < ‖y - x‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm he)))
  apply (div_le_iff₀ hpos).mpr
  have hinner := (real_inner_le_norm (l.gradient y - l.gradient x) (y - x)).trans
    (mul_le_mul_of_nonneg_right h (norm_nonneg _))
  nlinarith only [hinner]

/-- A returned request names a present component and reports a failed check
whose arguments were inside the working set. -/
theorem runPass_error {D : Set E} (P : Projection D) (pairs : List (Pair E))
    (hp : ∀ pair ∈ pairs, Pair.Valid D pair.1 pair.2)
    (k : ℕ) (f : PassFrame E) (hf : f.Valid D) (U : ℕ → E) (hU : ∀ i, U i ∈ D)
    {req : Request} (hr : (runPass P pairs k f U).outcome = .error req) :
    ∃ (j : ℕ) (pair : Pair E) (x y : E), pairs[j]? = some pair ∧ req.level = k + j ∧
      x ∈ D ∧ y ∈ D ∧ pair.2.smoothness < req.threshold ∧
      req.threshold = secant pair.2 x y (pair.2.gradient x) := by
  induction pairs generalizing k f U with
  | nil => simp [runPass] at hr
  | cons pair tail ih =>
    rcases pair with ⟨p, l⟩
    have hpair := hp (p, l) List.mem_cons_self
    have htail (pair : Pair E) (h : pair ∈ tail) := hp pair (List.mem_cons_of_mem _ h)
    let child := runPass P tail (k + 1)
    have hc : PassCertificate D tail (k + 1) child := runPass_correct P tail htail (k + 1)
    have hcycle (n : ℕ) (hn : n ≤ l.last + 1)
        (her : (passCycle P l f k child U n).outcome = .error req) :
        ∃ (j : ℕ) (pair : Pair E) (x y : E), ((p, l) :: tail)[j]? = some pair ∧
          req.level = k + j ∧ x ∈ D ∧ y ∈ D ∧ pair.2.smoothness < req.threshold ∧
          req.threshold = secant pair.2 x y (pair.2.gradient x) := by
      induction n with
      | zero => simp [passCycle] at her
      | succ n hn' =>
        cases prev : (passCycle P l f k child U n).outcome with
        | error e =>
          have he : e = req := by simpa only [passCycle, prev, Except.error.injEq] using her
          subst e
          exact hn' (Nat.le_of_succ_le hn) prev
        | ok s =>
          have hstep : (passStep P l f k n child s).outcome = .error req := by
            simpa only [passCycle, prev] using her
          have hs : s.Feasible D := by
            cases n with
            | zero =>
              have he : s = ⟨U k, U⟩ := by
                simpa only [passCycle, Except.ok.injEq] using prev.symm
              rw [he]
              exact ⟨hU k, hU⟩
            | succ t =>
              have ht : t ≤ l.last := by omega
              exact (passCycle_correct P hpair htail hf k hc U hU ht prev).1
          let u := s.atLevel k
          let F := f.changeArgument l n s.average
          let x := F.arg u
          let G := f.descend l n s.average u (l.gradient x + l.operator u)
          have hG := PassFrame.descend_valid hf hpair (Nat.le_of_succ_le_succ hn) hs.1 u
            (l.gradient x + l.operator u)
          have hx : x ∈ D := hG.maps (hs.2 k)
          dsimp only [passStep] at hstep
          cases hh : (child G s.atLevel).outcome with
          | error e =>
            have hh' := hh
            dsimp only [G, x, F, u] at hh'
            simp only [hh', Except.error.injEq] at hstep
            subst e
            obtain ⟨j, pair, a, b, hj, hk, ha, hb, hlt, he⟩ :=
              ih htail (k + 1) G hG s.atLevel hs.2 hh
            exact ⟨j + 1, pair, a, b, hj, by omega, ha, hb, hlt, he⟩
          | ok v =>
            have hv := (hc G hG s.atLevel hs.2 v hh).1.1
            have hh' := hh
            dsimp only [G, x, F, u] at hh'
            simp only [hh'] at hstep
            split at hstep
            · rename_i hbad
              have he := Except.error.inj hstep
              subst req
              exact ⟨0, (p, l), x, F.arg v.average, rfl, by simp, hx, hG.maps hv, hbad, rfl⟩
            · simp at hstep
    exact hcycle _ le_rfl hr

/-- The trace includes the requests made by every child, including failed children. -/
def Attempt.calls (a : Attempt E) (i : ℕ) (o : Oracle) : ℕ :=
  a.queries.countP fun q => decide (q.level = i ∧ q.oracle = o)

private theorem passStep_calls_le {D : Set E} (P : Projection D) (l : Level E)
    (f : PassFrame E) (k t : ℕ) (child : PassFrame E → (ℕ → E) → Attempt E)
    (s : Centers E) (i : ℕ) (o : Oracle) {B : ℕ}
    (hc : ∀ f U, (child f U).calls i o ≤ B) :
    (passStep P l f k t child s).calls i o ≤ 2 * (if k = i then 1 else 0) + B := by
  dsimp only [passStep]
  split
  · simp only [Attempt.calls, List.countP_append, List.countP_cons, List.countP_nil]
    specialize hc (f.descend l t s.average (s.atLevel k)
      (l.gradient ((f.changeArgument l t s.average).arg (s.atLevel k)) + l.operator (s.atLevel k)))
      s.atLevel
    unfold Attempt.calls at hc
    by_cases hk : k = i <;> cases o <;> simp [hk] at hc ⊢ <;> omega
  · split <;> split_ifs <;>
    simp only [Attempt.calls, List.countP_append, List.countP_cons, List.countP_nil] <;>
    specialize hc (f.descend l t s.average (s.atLevel k)
      (l.gradient ((f.changeArgument l t s.average).arg (s.atLevel k)) + l.operator (s.atLevel k)))
      s.atLevel <;>
    unfold Attempt.calls at hc <;>
    (by_cases hk : k = i <;> cases o <;> simp [hk] at hc ⊢ <;> omega)

/-- Each oracle at a given level is called at most twice per scheduled visit.
The bound applies also to an aborted pass. -/
theorem runPass_calls_le {D : Set E} (P : Projection D) (pairs : List (Pair E))
    (k : ℕ) (f : PassFrame E) (U : ℕ → E) (i : ℕ) (o : Oracle) :
    (runPass P pairs k f U).calls i o ≤ 2 * Localized.visits (pairs.map Prod.snd) k i := by
  induction pairs generalizing k f U with
  | nil => simp [runPass, Attempt.calls, Localized.visits]
  | cons pair tail ih =>
    rcases pair with ⟨p, l⟩
    let child := runPass P tail (k + 1)
    let b := (if k = i then 1 else 0) + Localized.visits (tail.map Prod.snd) (k + 1) i
    have cyc (t : ℕ) : (passCycle P l f k child U t).calls i o ≤ 2 * (t * b) := by
      induction t with
      | zero => simp [passCycle, Attempt.calls]
      | succ t ht =>
        cases h : (passCycle P l f k child U t).outcome with
        | error req =>
          simp only [passCycle, h]
          exact ht.trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right b (Nat.le_succ _)))
        | ok s =>
          simp only [passCycle, h, Attempt.calls, List.countP_append]
          have hstep := passStep_calls_le P l f k t child s i o (ih (k + 1))
          change (passCycle P l f k child U t).calls i o +
            (passStep P l f k t child s).calls i o ≤ 2 * ((t + 1) * b)
          calc
            _ ≤ 2 * (t * b) + 2 * b :=
              Nat.add_le_add ht (by simpa only [b, Nat.mul_add] using hstep)
            _ = _ := by ring
    exact cyc (l.last + 1)

theorem adaptivePass_calls_le {D : Set E} (P : Projection D) (pairs : List (Pair E))
    (s : E) (i : ℕ) (o : Oracle) :
    (adaptivePass P pairs s).calls i o ≤ 2 * Localized.visits (pairs.map Prod.snd) 0 i :=
  runPass_calls_le P pairs 0 _ _ i o

/-- The full tree of scheduled visits budgets one projection at each leaf
and at most one correction projection at each internal step. -/
def projectionBudget : List (Pair E) → ℕ
  | [] => 1
  | (_, l) :: tail => (l.last + 1) * (projectionBudget tail + 1)

theorem runPass_projections_le {D : Set E} (P : Projection D) (pairs : List (Pair E))
    (k : ℕ) (f : PassFrame E) (U : ℕ → E) :
    (runPass P pairs k f U).projections ≤ projectionBudget pairs := by
  induction pairs generalizing k f U with
  | nil => exact le_rfl
  | cons pair tail ih =>
    rcases pair with ⟨p, l⟩
    let child := runPass P tail (k + 1)
    have oneStep (s : Centers E) (t : ℕ) :
        (passStep P l f k t child s).projections ≤ projectionBudget tail + 1 := by
      let x := (f.changeArgument l t s.average).arg (s.atLevel k)
      have hc := ih (k + 1) (f.descend l t s.average (s.atLevel k)
        (l.gradient x + l.operator (s.atLevel k))) s.atLevel
      dsimp only [passStep]
      split
      · exact hc.trans (Nat.le_succ _)
      · split
        · exact hc.trans (Nat.le_succ _)
        · exact Nat.succ_le_succ hc
    have hcycle (t : ℕ) : (passCycle P l f k child U t).projections ≤
        t * (projectionBudget tail + 1) := by
      induction t with
      | zero => simp [passCycle]
      | succ t ht =>
        cases hp : (passCycle P l f k child U t).outcome with
        | error req =>
          simp only [passCycle, hp]
          exact ht.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))
        | ok out =>
          simp only [passCycle, hp, Nat.succ_mul]
          exact Nat.add_le_add ht (oneStep out t)
    exact hcycle (l.last + 1)

end

end LeanLab.Sliding.PathA
