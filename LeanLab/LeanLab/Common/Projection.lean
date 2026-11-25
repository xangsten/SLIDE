module

public import LeanLab.Common.Sliding

set_option linter.style.header false

/-!
# Projections and averaging

The shared projection interface, averaging weights, and operator assumptions.
-/

@[expose] public section

namespace LeanLab.Sliding.TwoLevel

open Set
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact projection onto the working set, specified by its normal inequality. -/
structure Projection (D : Set E) where
  apply : E → E
  feasible (x : E) : apply x ∈ D
  normal (x : E) {w : E} : w ∈ D → ⟪x - apply x, w - apply x⟫ ≤ 0

def mix (α : ℝ) (y v : E) : E := (1 - α) • y + α • v

theorem weight_le_one (j : ℕ) : weight j ≤ 1 := by
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  exact (weight_upper j).trans ((div_le_iff₀ (by positivity)).mpr (by linarith))

theorem weight_antitone : Antitone weight := by
  apply antitone_nat_of_succ_le
  intro j
  have h₀ := weight_pos j
  have h₁ := weight_pos (j + 1)
  have hrec := weight_recurrence j
  apply (le_of_pow_le_pow_left₀ (n := 2) (by decide) h₀.le)
  have hmul := (div_eq_div_iff (pow_ne_zero _ h₁.ne') (pow_ne_zero _ h₀.ne')).mp hrec
  nlinarith [mul_nonneg h₁.le (sq_nonneg (weight j))]

theorem mix_mem {D : Set E} (hD : Convex ℝ D) {α : ℝ}
    (hα : 0 ≤ α) (hα₁ : α ≤ 1) {y v : E} (hy : y ∈ D) (hv : v ∈ D) :
    mix α y v ∈ D :=
  hD hy hv (sub_nonneg.mpr hα₁) hα (sub_add_cancel 1 α)

/-- The only analytic premises for the operator level. -/
structure MonotoneLipschitz (D : Set E) (Q : E → E) (M : ℝ) : Prop where
  nonneg : 0 ≤ M
  monotone {v w : E} : v ∈ D → w ∈ D → 0 ≤ ⟪Q v - Q w, v - w⟫
  lipschitz {u v : E} : u ∈ D → v ∈ D → ‖Q u - Q v‖ ≤ M * ‖v - u‖

end

end LeanLab.Sliding.TwoLevel
