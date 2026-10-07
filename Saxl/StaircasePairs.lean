import Mathlib
import Saxl.Staircase
import Saxl.Polytabloid
import Saxl.Content
import Saxl.RowSquares
import Saxl.Orbit

/-!
# Row structure of a staircase tableau and the retained pair words (Prop 3.2)

For `t : Tableau N (staircase m)`: `rowOf p`, `colOf p` are the coordinates of the cell at
position `p`; `swapTableau t` has row word `colOf` and column group the row-preserving
permutations.  For row-preserving `g g'`, the pair word `p ↦ colOf (g⁻¹ p) + colOf (g'⁻¹ p)` has
the content of `c₀ : p ↦ (row length) - 1` only if it *equals* `c₀` (`pair_eq_of_content_eq`).
-/

namespace OAI.Saxl

open Equiv YoungDiagram Finset

variable {m N : ℕ} (t : Tableau N (staircase m))

/-- Row coordinate of the cell at position `p`. -/
def rowOf (p : Fin N) : ℕ := (t p).val.1

/-- Column coordinate of the cell at position `p`. -/
def colOf (p : Fin N) : ℕ := (t p).val.2

theorem rowOf_add_colOf_lt (p : Fin N) : rowOf t p + colOf t p < m := by
  have h : ((t p).val.1, (t p).val.2) ∈ staircase m := (t p).2
  rw [mem_staircase] at h
  exact h.2.2

theorem rowOf_lt (p : Fin N) : rowOf t p < m := by
  have := rowOf_add_colOf_lt t p; omega

/-- Swapping coordinates is a bijection of the staircase cells. -/
def swapCells (m : ℕ) : (staircase m).cells ≃ (staircase m).cells where
  toFun c := ⟨c.val.swap, by
    have h := c.2
    rw [YoungDiagram.mem_cells] at h ⊢
    obtain ⟨⟨i, j⟩, _⟩ := c
    simp only [Prod.swap_prod_mk]
    rw [mem_staircase] at h ⊢
    omega⟩
  invFun c := ⟨c.val.swap, by
    have h := c.2
    rw [YoungDiagram.mem_cells] at h ⊢
    obtain ⟨⟨i, j⟩, _⟩ := c
    simp only [Prod.swap_prod_mk]
    rw [mem_staircase] at h ⊢
    omega⟩
  left_inv c := by ext1; simp
  right_inv c := by ext1; simp

/-- The tableau alternating along rows: coordinates swapped. -/
def swapTableau : Tableau N (staircase m) := t.trans (swapCells m)

theorem rowWord_swapTableau (p : Fin N) : (rowWord (swapTableau t) p : ℕ) = colOf t p := rfl

theorem mem_columnGroup_swapTableau (g : Perm (Fin N)) :
    g ∈ columnGroup (swapTableau t) ↔ ∀ p, rowOf t (g p) = rowOf t p := by
  simp only [mem_columnGroup, swapTableau, Equiv.trans_apply]
  rfl

/-- The row fiber. -/
def rowFiber (i : ℕ) : Finset (Fin N) := univ.filter fun p => rowOf t p = i

theorem mem_rowFiber {i : ℕ} {p : Fin N} : p ∈ rowFiber t i ↔ rowOf t p = i := by
  simp [rowFiber]

/-- `colOf` maps the row fiber bijectively onto `range (m - i)`. -/
theorem image_colOf_rowFiber (i : ℕ) (hi : i < m) :
    (rowFiber t i).image (colOf t) = range (m - i) := by
  ext j
  rw [mem_image, mem_range]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [mem_rowFiber] at hp
    have := rowOf_add_colOf_lt t p
    omega
  · intro hj
    have hcell : (i, j) ∈ staircase m := by rw [mem_staircase]; omega
    refine ⟨t.symm ⟨(i, j), hcell⟩, ?_, ?_⟩
    · rw [mem_rowFiber]; show (t (t.symm _)).val.1 = i; simp
    · show (t (t.symm _)).val.2 = j; simp

theorem colOf_injOn_rowFiber (i : ℕ) : Set.InjOn (colOf t) (rowFiber t i) := by
  intro p hp q hq hpq
  rw [mem_coe, mem_rowFiber] at hp hq
  apply t.injective
  apply Subtype.ext
  exact Prod.ext (hp.trans hq.symm) hpq

theorem card_rowFiber (i : ℕ) (hi : i < m) : (rowFiber t i).card = m - i := by
  rw [← card_range (m - i), ← image_colOf_rowFiber t i hi, card_image_of_injOn (colOf_injOn_rowFiber t i)]

theorem sum_colOf_rowFiber (i : ℕ) (hi : i < m) :
    ∑ p ∈ rowFiber t i, (colOf t p : ℤ) = ∑ j ∈ range (m - i), (j : ℤ) := by
  rw [← image_colOf_rowFiber t i hi, sum_image (colOf_injOn_rowFiber t i)]

/-- Row-preserving permutations preserve the row fibers. -/
theorem sum_colOf_comp_rowFiber {g : Perm (Fin N)} (hg : ∀ p, rowOf t (g p) = rowOf t p)
    (i : ℕ) (hi : i < m) :
    ∑ p ∈ rowFiber t i, (colOf t (g⁻¹ p) : ℤ) = ∑ j ∈ range (m - i), (j : ℤ) := by
  rw [← sum_colOf_rowFiber t i hi]
  refine sum_nbij' (fun p => g⁻¹ p) (fun p => g p) ?_ ?_ (fun p _ => by simp) (fun p _ => by simp)
    (fun p _ => rfl)
  · intro p hp
    rw [mem_rowFiber] at hp ⊢
    have := hg (g⁻¹ p)
    have h1 : g (g⁻¹ p) = p := by rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
    rw [h1] at this
    rw [← this]; exact hp
  · intro p hp
    rw [mem_rowFiber] at hp ⊢
    rw [hg, hp]

theorem rowOf_mem_image (p : Fin N) : rowOf t p ∈ univ.image (rowOf t) := mem_image_of_mem _ (mem_univ p)

theorem lt_of_mem_image_rowOf {i : ℕ} (hi : i ∈ univ.image (rowOf t)) : i < m := by
  obtain ⟨p, _, rfl⟩ := mem_image.1 hi
  exact rowOf_lt t p

/-- The target word `c₀ : p ↦ (row length) - 1`, with letters in `Fin (2 * m)`. -/
def targetWord (p : Fin N) : Fin (2 * m) :=
  ⟨m - rowOf t p - 1, by have := rowOf_lt t p; omega⟩

/-- The pair word of two row-preserving permutations. -/
def pairWord (g g' : Perm (Fin N)) (p : Fin N) : Fin (2 * m) :=
  ⟨colOf t (g⁻¹ p) + colOf t (g'⁻¹ p), by
    have h1 := rowOf_add_colOf_lt t (g⁻¹ p)
    have h2 := rowOf_add_colOf_lt t (g'⁻¹ p)
    omega⟩

/-- **Uniqueness of the retained word** (paper eq. (3.9)). -/
theorem pair_eq_of_content_eq {g g' : Perm (Fin N)} (hg : ∀ p, rowOf t (g p) = rowOf t p)
    (hg' : ∀ p, rowOf t (g' p) = rowOf t p)
    (hc : content (pairWord t g g') = content (targetWord t)) :
    pairWord t g g' = targetWord t := by
  -- equal content ⇒ equal sums of squares
  obtain ⟨σ, hσ⟩ := exists_perm_of_content_eq hc
  have hsq : ∑ p, ((colOf t (g⁻¹ p) : ℤ) + colOf t (g'⁻¹ p)) ^ 2 =
      ∑ p, (((m - rowOf t p : ℕ) : ℤ) - 1) ^ 2 := by
    have h1 : ∀ p, ((colOf t (g⁻¹ p) : ℤ) + colOf t (g'⁻¹ p)) = ((pairWord t g g' p : ℕ) : ℤ) := by
      intro p; simp [pairWord]
    have h2 : ∀ p, (((m - rowOf t p : ℕ) : ℤ) - 1) = ((targetWord t p : ℕ) : ℤ) := by
      intro p
      have := rowOf_lt t p
      simp only [targetWord]
      push_cast [show 1 ≤ m - rowOf t p by omega]
      ring
    simp_rw [h1, h2, hσ]
    exact (Equiv.sum_comp σ (fun p => ((pairWord t g g' p : ℕ) : ℤ) ^ 2)).symm
  have key := eq_of_sum_sq_eq (rowOf t) (fun i => m - i) (fun p => colOf t (g⁻¹ p))
    (fun p => colOf t (g'⁻¹ p))
    (fun i hi => card_rowFiber t i (lt_of_mem_image_rowOf t hi))
    (fun i hi => sum_colOf_comp_rowFiber t hg i (lt_of_mem_image_rowOf t hi))
    (fun i hi => sum_colOf_comp_rowFiber t hg' i (lt_of_mem_image_rowOf t hi)) hsq
  funext p
  apply Fin.ext
  have := key p
  have hr := rowOf_lt t p
  simp only [pairWord, targetWord]
  omega

end OAI.Saxl
