module

public import LeanLab.Common.Recursive

set_option linter.style.header false

/-!
# Target accuracy and balance for recursive sliding

The levels are indexed from zero, after sorting by increasing target scale.
The larger length multiplier at the inner levels makes the contributions to
the radius estimate decay geometrically.
-/

@[expose] public section

namespace LeanLab.Sliding.PathA

open scoped BigOperators RealInnerProductSpace

noncomputable section

theorem weight_lower (t : ℕ) : 1 / ((t : ℝ) + 1) ≤ weight t := by
  have hrecip : reciprocalWeight t ≤ (t : ℝ) + 1 := by
    induction t with
    | zero => norm_num [reciprocalWeight]
    | succ t ih =>
      have hp : 0 ≤ reciprocalWeight t := (inv_pos.mp (weight_pos t)).le
      have hs : Real.sqrt (1 + 4 * reciprocalWeight t ^ 2) ≤ 1 + 2 * reciprocalWeight t := by
        apply le_of_sq_le_sq _ (by positivity)
        rw [Real.sq_sqrt (by positivity)]
        nlinarith
      rw [reciprocalWeight, Nat.cast_succ]
      linarith
  simpa [weight, one_div] using inv_anti₀ (inv_pos.mp (weight_pos t)) hrecip

def steps (h : ℕ → ℝ) : ℕ → ℕ
  | 0 => ⌈2 * h 0⌉₊
  | j + 1 => ⌈16 * (h (j + 1) / h j)⌉₊

def prefixCalls (h : ℕ → ℝ) : ℕ → ℕ
  | 0 => steps h 0
  | j + 1 => prefixCalls h j * steps h (j + 1)

def prefixWeight (h : ℕ → ℝ) : ℕ → ℝ
  | 0 => weight (steps h 0 - 1)
  | j + 1 => prefixWeight h j * weight (steps h (j + 1) - 1)

def contribution (s Λ M : ℝ) : ℝ := s ^ 2 * Λ + 2 * s * M

private theorem ceiling_bounds {r k : ℝ} (hr : 1 ≤ r) (hk : 1 ≤ k) :
    k * r ≤ (⌈k * r⌉₊ : ℝ) ∧ (⌈k * r⌉₊ : ℝ) ≤ (k + 1) * r ∧
      0 < ⌈k * r⌉₊ := by
  have hkr : 1 ≤ k * r := by nlinarith
  have hceil := Nat.le_ceil (k * r)
  have hu := Nat.ceil_lt_add_one (show 0 ≤ k * r by linarith)
  have hp : 0 < (⌈k * r⌉₊ : ℝ) := by linarith
  exact ⟨hceil, by linarith, Nat.cast_pos.mp hp⟩

private theorem cycle_weight {T : ℕ} (hT : 0 < T) :
    1 / (T : ℝ) ≤ weight (T - 1) ∧ weight (T - 1) ≤ 2 / (T : ℝ) := by
  have hc : ((T - 1 : ℕ) : ℝ) + 1 = T := by
    rw [Nat.cast_sub (by omega : 1 ≤ T)]
    norm_num
  refine ⟨by simpa only [hc] using weight_lower (T - 1), (weight_upper _).trans ?_⟩
  apply div_le_div_of_nonneg_left (by norm_num) (Nat.cast_pos.mpr hT)
  linarith

theorem prefix_calls_le {h : ℕ → ℝ} (h₀ : 1 ≤ h 0) (hs : Monotone h) (j : ℕ) :
    (prefixCalls h j : ℝ) ≤ 3 * 17 ^ j * h j := by
  induction j with
  | zero =>
    simpa [prefixCalls, steps, show (2 : ℝ) + 1 = 3 by norm_num] using
      (ceiling_bounds h₀ (show (1 : ℝ) ≤ 2 by norm_num)).2.1
  | succ j ih =>
    have hp : 0 < h j := (zero_lt_one.trans_le h₀).trans_le (hs (Nat.zero_le j))
    have hr : 1 ≤ h (j + 1) / h j := (le_div_iff₀ hp).mpr (by simpa using hs (Nat.le_succ j))
    have hu : (steps h (j + 1) : ℝ) ≤ 17 * (h (j + 1) / h j) := by
      simpa [steps, show (16 : ℝ) + 1 = 17 by norm_num] using
        (ceiling_bounds hr (show (1 : ℝ) ≤ 16 by norm_num)).2.1
    rw [prefixCalls, Nat.cast_mul]
    calc
      _ ≤ (3 * 17 ^ j * h j) * (17 * (h (j + 1) / h j)) :=
        mul_le_mul ih hu (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [pow_succ]; field_simp

private theorem prefix_weight_bounds {h : ℕ → ℝ} (h₀ : 1 ≤ h 0) (hs : Monotone h) :
    (1 / 3 : ℝ) ≤ prefixWeight h 0 * h 0 ∧ prefixWeight h 0 * h 0 ≤ 1 ∧
    ∀ j, 0 ≤ prefixWeight h j ∧
      prefixWeight h j * h j ≤ (prefixWeight h 0 * h 0) * (1 / 8 : ℝ) ^ j := by
  have hp (j : ℕ) : 0 < h j := (zero_lt_one.trans_le h₀).trans_le (hs (Nat.zero_le j))
  obtain ⟨hl, hu, ht⟩ := ceiling_bounds h₀ (show (1 : ℝ) ≤ 2 by norm_num)
  obtain ⟨wl, wu⟩ := cycle_weight ht
  have ht' : 0 < (steps h 0 : ℝ) := Nat.cast_pos.mpr ht
  change 2 * h 0 ≤ (steps h 0 : ℝ) at hl
  change (steps h 0 : ℝ) ≤ (2 + 1) * h 0 at hu
  have hw' : 0 < prefixWeight h 0 := weight_pos _
  change 1 / (steps h 0 : ℝ) ≤ prefixWeight h 0 at wl
  change prefixWeight h 0 ≤ 2 / (steps h 0 : ℝ) at wu
  refine ⟨?_, ?_, ?_⟩
  · have hmul := mul_le_mul_of_nonneg_left hu hw'.le
    have hwl := (div_le_iff₀ ht').mp wl
    linarith
  · have hmul := mul_le_mul_of_nonneg_left hl hw'.le
    have hwu := (le_div_iff₀ ht').mp wu
    linarith
  intro j
  induction j with
  | zero => simpa using hw'.le
  | succ j ih =>
    have hr : 1 ≤ h (j + 1) / h j := (le_div_iff₀ (hp j)).mpr
      (by simpa using hs (Nat.le_succ j))
    obtain ⟨hl, _, ht⟩ := ceiling_bounds hr (show (1 : ℝ) ≤ 16 by norm_num)
    let a := weight (steps h (j + 1) - 1)
    have ha : 0 ≤ a := (weight_pos _).le
    have hlength : 16 * (h (j + 1) / h j) ≤ (steps h (j + 1) : ℝ) := hl
    have hmul := mul_le_mul_of_nonneg_left hlength ha
    have hupper := (le_div_iff₀ (Nat.cast_pos.mpr ht)).mp (cycle_weight ht).2
    have hratio : a * h (j + 1) ≤ h j / 8 := by
      have hbound : a * (16 * (h (j + 1) / h j)) ≤ 2 := hmul.trans hupper
      rw [← mul_div_assoc, ← mul_div_assoc, div_le_iff₀ (hp j)] at hbound
      linarith
    constructor
    · exact mul_nonneg ih.1 ha
    · change (prefixWeight h j * a) * h (j + 1) ≤
        (prefixWeight h 0 * h 0) * (1 / 8 : ℝ) ^ (j + 1)
      calc
        _ ≤ (prefixWeight h j * h j) / 8 := by
          rw [mul_assoc, mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hratio ih.1
        _ ≤ ((prefixWeight h 0 * h 0) * (1 / 8 : ℝ) ^ j) / 8 :=
          div_le_div_of_nonneg_right ih.2 (by norm_num)
        _ = _ := by rw [pow_succ, ← mul_assoc, mul_one_div]

/-- The first contribution controls all deeper levels, and half the total
coefficient is at most the target accuracy when the curvature floor is ε/3. -/
theorem balance_and_accuracy {δ : ℝ} (hδ : 0 < δ) {Λ M : ℕ → ℝ}
    (hΛ : ∀ j, δ ≤ Λ j) (hM : ∀ j, 0 ≤ M j)
    (hs : Monotone (fun j => scale δ (Λ j) (M j))) (n : ℕ) :
    let h := fun j => scale δ (Λ j) (M j)
    let q := fun j => contribution (prefixWeight h j) (Λ j) (M j)
    (∑ j ∈ Finset.range n, q (j + 1)) ≤ q 0 ∧
      (∑ j ∈ Finset.range (n + 1), q j) / 2 ≤ 3 * δ := by
  let h := fun j => scale δ (Λ j) (M j)
  let s := prefixWeight h
  let x := s 0 * h 0
  let q := fun j => contribution (s j) (Λ j) (M j)
  have hroot (j : ℕ) : 1 ≤ Real.sqrt (Λ j / δ) := by
    calc
      1 = Real.sqrt 1 := by norm_num
      _ ≤ _ := Real.sqrt_le_sqrt ((le_div_iff₀ hδ).mpr (by simpa using hΛ j))
  have h₀ : 1 ≤ h 0 := (hroot 0).trans (le_max_left ..)
  obtain ⟨hx₁, hx₂, hw⟩ := prefix_weight_bounds h₀ hs
  have hx : 0 ≤ x := by change 1 / 3 ≤ x at hx₁; linarith
  have hgrad (j : ℕ) : Λ j ≤ δ * h j ^ 2 := by
    have hh : Real.sqrt (Λ j / δ) ≤ h j := le_max_left ..
    have hp := pow_le_pow_left₀ (Real.sqrt_nonneg _) hh 2
    rw [Real.sq_sqrt (div_nonneg (hδ.le.trans (hΛ j)) hδ.le)] at hp
    linarith only [(div_le_iff₀ hδ).mp hp]
  have hop (j : ℕ) : M j ≤ δ * h j := by
    have hh : M j / δ ≤ h j := le_max_right ..
    linarith only [(div_le_iff₀ hδ).mp hh]
  have hmajor (j : ℕ) : q j ≤ δ * (s j * h j) ^ 2 + 2 * δ * (s j * h j) := by
    unfold q contribution
    have hg := mul_le_mul_of_nonneg_left (hgrad j) (sq_nonneg (s j))
    have hm := mul_le_mul_of_nonneg_left (hop j) (show 0 ≤ 2 * s j by positivity [(hw j).1])
    linarith only [hg, hm]
  have hminor : δ * x ^ 2 ≤ q 0 := by
    change δ * (s 0 * h 0) ^ 2 ≤ contribution (s 0) (Λ 0) (M 0)
    have hs0 := (hw 0).1
    rcases le_total (M 0 / δ) (Real.sqrt (Λ 0 / δ)) with hh | hh
    · have heq : h 0 = Real.sqrt (Λ 0 / δ) := max_eq_left hh
      have hΛ0 : 0 ≤ Λ 0 := hδ.le.trans (hΛ 0)
      rw [mul_pow, heq, Real.sq_sqrt (by positivity), mul_comm (s 0 ^ 2), ← mul_assoc,
        mul_div_cancel₀ _ hδ.ne']
      unfold contribution
      linarith only [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs0) (hM 0)]
    · have heq : h 0 = M 0 / δ := max_eq_right hh
      have he : δ * x = s 0 * M 0 := by
        change δ * (s 0 * h 0) = _
        rw [heq]
        field_simp
      change δ * x ^ 2 ≤ _
      unfold contribution
      have hb := mul_le_mul_of_nonneg_left (show x ≤ 1 from hx₂)
        (mul_nonneg hδ.le hx)
      nlinarith only [he, hb, mul_nonneg hs0 (hM 0), mul_nonneg (sq_nonneg (s 0))
        (hδ.le.trans (hΛ 0))]
  have hfirst : q 0 ≤ 3 * δ := by
    have hb := mul_le_mul_of_nonneg_left (show x ≤ 1 from hx₂) hx
    have hc := mul_le_mul_of_nonneg_left (show x ≤ 1 from hx₂) hδ.le
    have hd := mul_le_mul_of_nonneg_left (show x ^ 2 ≤ 1 by nlinarith only [hb, hx₂]) hδ.le
    change q 0 ≤ _
    linarith only [hmajor 0, hc, hd]
  have htail (j : ℕ) : q j ≤ 7 * (1 / 8 : ℝ) ^ j * q 0 := by
    let r : ℝ := (1 / 8 : ℝ) ^ j
    have hr : 0 ≤ r := by positivity
    have hr₁ : r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hh : 1 ≤ h j := (hroot j).trans (le_max_left ..)
    have hprod : 0 ≤ s j * h j := mul_nonneg (hw j).1 (zero_le_one.trans hh)
    have hsq := pow_le_pow_left₀ hprod (hw j).2 2
    have hg := mul_le_mul_of_nonneg_left hsq hδ.le
    have hm := mul_le_mul_of_nonneg_left (hw j).2 (show 0 ≤ 2 * δ by positivity)
    have hr₂ := mul_le_mul_of_nonneg_left hr₁ hr
    have hg' := mul_le_mul_of_nonneg_left (show r ^ 2 ≤ r by nlinarith only [hr₂])
      (mul_nonneg hδ.le (sq_nonneg x))
    have hm' := mul_le_mul_of_nonneg_left (show 1 ≤ 3 * x by linarith only [hx₁])
      (show 0 ≤ 2 * δ * x * r by positivity)
    have hfinal := mul_le_mul_of_nonneg_left hminor (show 0 ≤ 7 * r by positivity)
    change q j ≤ 7 * r * q 0
    change (s j * h j) ^ 2 ≤ (x * r) ^ 2 at hsq
    change δ * (s j * h j) ^ 2 ≤ δ * (x * r) ^ 2 at hg
    change 2 * δ * (s j * h j) ≤ 2 * δ * (x * r) at hm
    linarith only [hmajor j, hg, hm, hg', hm', hfinal]
  have hq₀ : 0 ≤ q 0 := (mul_nonneg hδ.le (sq_nonneg x)).trans hminor
  have hsum : (∑ j ∈ Finset.range n, q (j + 1)) ≤ (1 - (1 / 8 : ℝ) ^ n) * q 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hj := htail (n + 1)
      rw [pow_succ] at hj
      linarith only [ih, hj]
  have hbalance : (∑ j ∈ Finset.range n, q (j + 1)) ≤ q 0 := by
    rw [sub_mul, one_mul] at hsum
    exact hsum.trans (sub_le_self _ (mul_nonneg (by positivity) hq₀))
  refine ⟨hbalance, ?_⟩
  rw [Finset.sum_range_succ']
  linarith only [hbalance, hfirst]

/-- The schedule turns the local pass bound into the global target bound. -/
theorem accepted_gap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : Set E} {f : E → ℝ} {Q : E → E} {z zin : E} {R δ : ℝ} {n : ℕ}
    {Λ M : ℕ → ℝ} (hδ : 0 < δ) (hΛ : ∀ j, δ ≤ Λ j) (hM : ∀ j, 0 ≤ M j)
    (hs : Monotone (fun j => scale δ (Λ j) (M j)))
    (hf : ConvexOn ℝ C f) (hQ : ∀ x ∈ C, ∀ y ∈ C, 0 ≤ ⟪Q x - Q y, x - y⟫)
    (hz : z ∈ C) (hR : 0 < R) (haccept : ‖z - zin‖ ≤ R / 2)
    (hlocal : let h := fun j => scale δ (Λ j) (M j)
      let q := fun j => contribution (prefixWeight h j) (Λ j) (M j)
      ∀ w ∈ C, ‖w - zin‖ ≤ R →
        gap f Q z w ≤ ((∑ j ∈ Finset.range (n + 1), q j) / 2) * ‖w - zin‖ ^ 2)
    (w : E) (hw : w ∈ C) : gap f Q z w ≤ (3 * δ) * ‖w - zin‖ ^ 2 := by
  refine global_gap_bound hf hQ hz hR (by positivity) haccept ?_ w hw
  intro v hv hdist
  exact (hlocal v hv hdist).trans
    (mul_le_mul_of_nonneg_right (balance_and_accuracy hδ hΛ hM hs n).2 (sq_nonneg _))

end

end LeanLab.Sliding.PathA
