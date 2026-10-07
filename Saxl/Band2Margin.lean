import Mathlib
import Saxl.Staircase

/-!
# The margin lemma (paper eqs. (4.6)–(4.7), any band width)

A subset `A` of the cells of the staircase `ρ_m` whose row counts and column counts are those of
the smaller staircase `ρ_{m-s}` — `|A ∩ row i| = m - s - i` and `|A ∩ col j| = m - s - j` — must
be `ρ_{m-s}` itself.  This is the equality case of the row/column margin inequalities: column `j`
contributes at most `min k (m - s - j)` cells to the first `k` rows, and the prefix sums force
equality in every column.
-/

namespace OAI.Saxl

open Finset

section cells

/-- Row `i` of the staircase, as an image of `range (m - i)`. -/
theorem staircase_filter_fst (m i : ℕ) :
    ((staircase m).cells.filter fun c => c.1 = i) = (range (m - i)).image fun j => (i, j) := by
  ext c
  rw [mem_filter, mem_image, YoungDiagram.mem_cells]
  constructor
  · rintro ⟨hc, hi⟩
    have hc' : (c.1, c.2) ∈ staircase m := hc
    rw [mem_staircase] at hc'
    exact ⟨c.2, mem_range.2 (by omega), Prod.ext hi.symm rfl⟩
  · rintro ⟨j, hj, rfl⟩
    rw [mem_range] at hj
    refine ⟨?_, rfl⟩
    show (i, j) ∈ staircase m
    rw [mem_staircase]; omega

/-- Column `j` of the staircase cut at row `k`, as an image of `range (min k (m - j))`. -/
theorem staircase_filter_snd_lt (m j k : ℕ) :
    ((staircase m).cells.filter fun c => c.2 = j ∧ c.1 < k) =
      (range (min k (m - j))).image fun i => (i, j) := by
  ext c
  rw [mem_filter, mem_image, YoungDiagram.mem_cells]
  constructor
  · rintro ⟨hc, hj, hk⟩
    have hc' : (c.1, c.2) ∈ staircase m := hc
    rw [mem_staircase] at hc'
    exact ⟨c.1, mem_range.2 (lt_min hk (by omega)), Prod.ext rfl hj.symm⟩
  · rintro ⟨i, hi, rfl⟩
    rw [mem_range, lt_min_iff] at hi
    refine ⟨?_, rfl, hi.1⟩
    show (i, j) ∈ staircase m
    rw [mem_staircase]; omega

theorem card_staircase_filter_fst (m i : ℕ) :
    ((staircase m).cells.filter fun c => c.1 = i).card = m - i := by
  rw [staircase_filter_fst, card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2), card_range]

theorem card_staircase_filter_snd_lt (m j k : ℕ) :
    ((staircase m).cells.filter fun c => c.2 = j ∧ c.1 < k).card = min k (m - j) := by
  rw [staircase_filter_snd_lt, card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1),
    card_range]

theorem staircase_fst_lt {m : ℕ} {c : ℕ × ℕ} (hc : c ∈ (staircase m).cells) : c.1 < m := by
  rw [YoungDiagram.mem_cells] at hc
  have : (c.1, c.2) ∈ staircase m := hc
  rw [mem_staircase] at this; omega

theorem staircase_snd_lt {m : ℕ} {c : ℕ × ℕ} (hc : c ∈ (staircase m).cells) : c.2 < m := by
  rw [YoungDiagram.mem_cells] at hc
  have : (c.1, c.2) ∈ staircase m := hc
  rw [mem_staircase] at this; omega

/-- Cells of `ρ_m` in the first `k` rows, counted by rows. -/
theorem card_staircase_rows (m k : ℕ) :
    ((staircase m).cells.filter fun c => c.1 < k).card = ∑ i ∈ range k, (m - i) := by
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := range k)]
  · refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [← card_staircase_filter_fst m i]
    congr 1
    ext c
    simp only [mem_filter, and_assoc]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, by omega, h3⟩
  · intro c hc
    rw [mem_coe, mem_filter] at hc
    rw [mem_coe, mem_range]; exact hc.2

/-- Cells of `ρ_m` in the first `k` rows, counted by columns. -/
theorem card_staircase_rows_cols (m k : ℕ) :
    ((staircase m).cells.filter fun c => c.1 < k).card = ∑ j ∈ range m, min k (m - j) := by
  rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := range m)]
  · refine sum_congr rfl fun j _ => ?_
    rw [← card_staircase_filter_snd_lt m j k]
    congr 1
    ext c
    simp only [mem_filter, and_assoc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩
    · rintro ⟨h1, h3, h2⟩; exact ⟨h1, h2, h3⟩
  · intro c hc
    rw [mem_coe, mem_filter] at hc
    rw [mem_coe, mem_range]; exact staircase_snd_lt hc.1

/-- Margin equality for the staircase `ρ_h`: `∑_{i<k} (h - i) = ∑_{j<m} min k (h - j)` whenever
`h ≤ m`. -/
theorem staircase_margin (h m k : ℕ) (hm : h ≤ m) :
    ∑ i ∈ range k, (h - i) = ∑ j ∈ range m, min k (h - j) := by
  rw [← card_staircase_rows, card_staircase_rows_cols]
  apply sum_subset (range_mono hm)
  intro j _ hj
  rw [mem_range] at hj
  simp [Nat.sub_eq_zero_of_le (by omega : h ≤ j)]

end cells

/-- **Margin lemma.**  A set of cells of `ρ_m` with the row and column counts of `ρ_{m-s}` is
`ρ_{m-s}`. -/
theorem eq_staircase_of_margins {m s : ℕ} {A : Finset (ℕ × ℕ)}
    (hA : A ⊆ (staircase m).cells)
    (hrow : ∀ i, (A.filter fun c => c.1 = i).card = m - s - i)
    (hcol : ∀ j, (A.filter fun c => c.2 = j).card = m - s - j) :
    A = (staircase (m - s)).cells := by
  classical
  -- prefix counts: `|A ∩ rows<k|` two ways
  have hpre_row : ∀ k, (A.filter fun c => c.1 < k).card = ∑ i ∈ range k, (m - s - i) := by
    intro k
    rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := range k)]
    · refine sum_congr rfl fun i hi => ?_
      rw [mem_range] at hi
      rw [← hrow i]
      congr 1
      ext c
      simp only [mem_filter, and_assoc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by omega, h3⟩
    · intro c hc
      rw [mem_coe, mem_filter] at hc
      rw [mem_coe, mem_range]; exact hc.2
  have hpre_col : ∀ k, (A.filter fun c => c.1 < k).card =
      ∑ j ∈ range m, ((A.filter fun c => c.2 = j).filter fun c => c.1 < k).card := by
    intro k
    rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := range m)]
    · refine sum_congr rfl fun j _ => ?_
      congr 1
      ext c
      simp only [mem_filter, and_assoc]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩
      · rintro ⟨h1, h3, h2⟩; exact ⟨h1, h2, h3⟩
    · intro c hc
      rw [mem_coe, mem_filter] at hc
      rw [mem_coe, mem_range]; exact staircase_snd_lt (hA hc.1)
  -- each column contributes at most `min k (m - s - j)`
  have hbound : ∀ k j, ((A.filter fun c => c.2 = j).filter fun c => c.1 < k).card ≤
      min k (m - s - j) := by
    intro k j
    refine le_min ?_ ?_
    · refine (card_le_card_of_injOn Prod.fst (t := range k) ?_ ?_).trans (card_range k).le
      · intro c hc
        rw [mem_coe, mem_filter] at hc
        rw [mem_coe, mem_range]; exact hc.2
      · intro c hc c' hc' hcc
        rw [mem_coe, mem_filter, mem_filter] at hc hc'
        exact Prod.ext hcc (hc.1.2.trans hc'.1.2.symm)
    · rw [← hcol j]
      exact card_le_card (filter_subset _ _)
  -- equality in every column, for every `k`
  have heq : ∀ k j, j < m → ((A.filter fun c => c.2 = j).filter fun c => c.1 < k).card =
      min k (m - s - j) := by
    intro k j hj
    have hsum : ∑ j ∈ range m, ((A.filter fun c => c.2 = j).filter fun c => c.1 < k).card =
        ∑ j ∈ range m, min k (m - s - j) := by
      rw [← hpre_col, hpre_row]
      exact staircase_margin (m - s) m k (Nat.sub_le _ _)
    exact (sum_eq_sum_iff_of_le (fun j _ => hbound k j)).1 hsum j (mem_range.2 hj)
  -- every cell of `A` in column `j` has row `< m - s - j`
  have hrows : ∀ c ∈ A, c.1 < m - s - c.2 := by
    intro c hc
    have h1 := heq (m - s - c.2) c.2 (staircase_snd_lt (hA hc))
    rw [min_self] at h1
    have h1' : ((A.filter fun c' => c'.2 = c.2).filter fun c' => c'.1 < m - s - c.2).card =
        (A.filter fun c' => c'.2 = c.2).card := h1.trans (hcol c.2).symm
    have h2 : (A.filter fun c' => c'.2 = c.2).filter (fun c' => c'.1 < m - s - c.2) =
        A.filter fun c' => c'.2 = c.2 :=
      eq_of_subset_of_card_le (filter_subset _ _) h1'.symm.le
    have hc' : c ∈ (A.filter fun c' => c'.2 = c.2).filter (fun c' => c'.1 < m - s - c.2) := by
      rw [h2, mem_filter]; exact ⟨hc, rfl⟩
    exact (mem_filter.1 hc').2
  have hsub : A ⊆ (staircase (m - s)).cells := by
    intro c hc
    rw [YoungDiagram.mem_cells]
    show (c.1, c.2) ∈ staircase (m - s)
    rw [mem_staircase]
    have := hrows c hc; omega
  -- and the cardinalities agree
  apply eq_of_subset_of_card_le hsub
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (s := (staircase (m - s)).cells) (t := range m),
    card_eq_sum_card_fiberwise (f := Prod.fst) (s := A) (t := range m)]
  · refine sum_le_sum fun i _ => ?_
    rw [hrow i, card_staircase_filter_fst]
  · intro c hc
    rw [mem_coe, mem_range]; exact staircase_fst_lt (hA hc)
  · intro c hc
    rw [mem_coe, mem_range]
    have := staircase_fst_lt hc; omega

end OAI.Saxl
