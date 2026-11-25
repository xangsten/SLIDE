module

public import LeanLab.Common.Projection

set_option linter.style.header false

/-!
# Common data and bounds for recursive sliding

The recursive variants share oracle labels, the visit count, the working set,
and the projected minimum of an accumulated quadratic.
-/

@[expose] public section

namespace LeanLab.Sliding.Localized

open Set
open TwoLevel (Projection)
open scoped RealInnerProductSpace

noncomputable section

/-- One pair of oracles with curvature bounds and a positive cycle length. -/
structure Level (E : Type*) where
  gradient : E → E
  operator : E → E
  smoothness : ℝ
  lipschitz : ℝ
  last : ℕ

/-- The sum of frozen quadratic models, up to an additive constant. -/
structure Model (E : Type*) where
  curvature : ℝ
  linear : E

inductive Oracle
  | gradient
  | operator
  deriving DecidableEq

structure Query (E : Type*) where
  level : ℕ
  oracle : Oracle
  point : E

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The set used for the projected leaf and corrections in variant A. -/
def region (C : Set E) (s : E) (R : ℝ) : Set E := C ∩ Metric.closedBall s R

/-- Number of visits to an indexed level for a starting depth. -/
def visits : List (Level E) → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | l :: ls, k, i =>
    (l.last + 1) * ((if k = i then 1 else 0) + visits ls (k + 1) i)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Exact prefix-product formula for visits to a component in the list. -/
theorem visits_eq_prod (levels : List (Level E)) (k j : ℕ) (hj : j < levels.length) :
    visits levels k (k + j) =
      ∏ i ∈ Finset.range (j + 1), (levels[i]?).elim 1 (fun l => l.last + 1) := by
  induction levels generalizing k j with
  | nil => simp at hj
  | cons l ls ih =>
    cases j with
    | zero =>
      have hbelow : ∀ (tail : List (Level E)) (base target : ℕ), target < base →
          visits tail base target = 0 := by
        intro tail
        induction tail with
        | nil => simp [visits]
        | cons a tail ht =>
          intro base target hlt
          simp [visits, (ne_of_lt hlt).symm, ht _ _ (by omega : target < base + 1)]
      simp [visits, hbelow ls (k + 1) k (by omega)]
    | succ j =>
      have hj' : j < ls.length := by simpa using hj
      have hk : k ≠ k + (j + 1) := by omega
      rw [visits, ite_eq_right hk, zero_add, show k + (j + 1) = k + 1 + j by omega, ih _ _ hj']
      conv_rhs => rw [Finset.prod_range_succ']
      simp [Nat.mul_comm]

/-- The minimum obtained by projecting the center of a positive quadratic. -/
theorem projected_model_bound {D : Set E} (P : Projection D) {H : ℝ} (hH : 0 < H)
    (u slope : E) {w : E} (hw : w ∈ D) :
    let v := P.apply (H⁻¹ • (H • u - slope))
    model H u slope v - model H u slope w + H / 2 * ‖v - w‖ ^ 2 ≤ 0 := by
  let a := H⁻¹ • (H • u - slope)
  let v := P.apply a
  have hnormal := P.normal a hw
  have heq : H • (v - u) + slope = -(H • (a - v)) := by
    dsimp only [a]
    conv_rhs => rw [smul_sub, smul_smul, mul_inv_cancel₀ hH.ne', one_smul]
    module
  apply leaf_bound
  rw [heq, inner_neg_left, real_inner_smul_left]
  exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hH.le hnormal)

end

end LeanLab.Sliding.Localized

namespace LeanLab.Sliding.PathA

noncomputable section

/-- The shared scale for choosing cycle lengths from curvature and Lipschitz bounds. -/
def scale (δ Λ M : ℝ) : ℝ := max (Real.sqrt (Λ / δ)) (M / δ)

end

end LeanLab.Sliding.PathA
