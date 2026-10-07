import Mathlib
import Saxl.Statement
import Saxl.Dominance

/-! # The staircase partition `ρ_m = (m, m-1, …, 1)` -/

namespace OAI.Saxl

open YoungDiagram

/-- Cells of `staircase m` are the `(i, j)` with `i + j < m`. -/
theorem mem_staircase {m i j : ℕ} : (i, j) ∈ staircase m ↔ i < m ∧ j < m ∧ i + j < m := by
  rw [← mem_cells]
  simp [staircase, and_assoc]

/-- Row `i` of `staircase m` has length `m - i`. -/
theorem rowLen_staircase (m i : ℕ) : (staircase m).rowLen i = m - i :=
  nat_eq_of_lt_iff fun j => by rw [← mem_iff_lt_rowLen, mem_staircase]; omega

/-- Column `j` of `staircase m` has length `m - j`. -/
theorem colLen_staircase (m j : ℕ) : (staircase m).colLen j = m - j :=
  nat_eq_of_lt_iff fun i => by rw [← mem_iff_lt_colLen, mem_staircase]; omega

/-- `rowSum (staircase m) k = ∑_{i<k} (m - i)`. -/
theorem rowSum_staircase (m k : ℕ) : rowSum (staircase m) k = ∑ i ∈ Finset.range k, (m - i) := by
  unfold rowSum; simp only [rowLen_staircase]

/-- `2 ∑_{i<k} (m - i) = k (2m - k + 1)` for `k ≤ m`. -/
theorem two_mul_rowSum_staircase (m : ℕ) {k : ℕ} (hk : k ≤ m) :
    2 * rowSum (staircase m) k = k * (2 * m + 1 - k) := by
  rw [rowSum_staircase]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih (by omega)]
    have h1 : k ≤ 2 * m + 1 := by omega
    have : k * (2 * m + 1 - k) + 2 * (m - k) = (k + 1) * (2 * m + 1 - (k + 1)) := by
      zify [h1, (show k ≤ m by omega), (show k + 1 ≤ 2 * m + 1 by omega)]
      ring
    exact this

/-- `N_m = |staircase m|` is the sum of its `m` rows. -/
theorem card_staircase (m : ℕ) : (staircase m).card = rowSum (staircase m) m := by
  rw [rowSum, sum_rowLen_eq_card]
  rw [colLen_staircase]; omega

/-- `rowSum μ k ≤ card μ`. -/
theorem rowSum_le_card (μ : YoungDiagram) (k : ℕ) : rowSum μ k ≤ μ.card := by
  rw [← sum_rowLen_eq_card μ (le_max_right k (μ.colLen 0)), rowSum]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (le_max_left _ _))

/-- Past row `m`, staircase row sums are the whole card. -/
theorem rowSum_staircase_of_le (m : ℕ) {k : ℕ} (hk : m ≤ k) :
    rowSum (staircase m) k = (staircase m).card := by
  rw [rowSum, sum_rowLen_eq_card]
  rw [colLen_staircase]; omega

/-- The staircase is self-conjugate. -/
theorem transpose_staircase (m : ℕ) : (staircase m).transpose = staircase m := by
  ext ⟨i, j⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, mem_transpose, Prod.swap_prod_mk,
    mem_staircase, mem_staircase]
  omega

end OAI.Saxl
