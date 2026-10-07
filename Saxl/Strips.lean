import Mathlib
import Saxl.Dominance

/-!
# Horizontal strips (paper §6, Lemma 6.1)

`HorizontalStrip ν λ` : `ν ⊆ λ` and `λ/ν` has at most one box per column.
-/

namespace OAI.Saxl

open YoungDiagram

/-- `λ/ν` is a horizontal strip. -/
def HorizontalStrip (nu lam : YoungDiagram) : Prop :=
  nu ≤ lam ∧ ∀ j, lam.colLen j ≤ nu.colLen j + 1

theorem nat_eq_of_lt_iff {a b : ℕ} (h : ∀ j, j < a ↔ j < b) : a = b := by
  apply le_antisymm <;> apply Nat.le_of_not_lt <;> intro hh
  · exact lt_irrefl _ ((h _).1 hh)
  · exact lt_irrefl _ ((h _).2 hh)

/-! ### Full sweep: delete the first row -/

/-- The diagram with rows `(λ₂, λ₃, …)`. -/
def dropRow (lam : YoungDiagram) : YoungDiagram where
  cells := (lam.cells.filter (fun c => 1 ≤ c.1)).image (fun c => (c.1 - 1, c.2))
  isLowerSet := by
    intro x y hxy hx
    simp only [Finset.coe_image, Finset.coe_filter, Set.mem_image] at hx ⊢
    obtain ⟨c, ⟨hc, hc1⟩, rfl⟩ := hx
    refine ⟨(y.1 + 1, y.2), ⟨?_, by simp⟩, by simp⟩
    refine lam.isLowerSet (show (y.1 + 1, y.2) ≤ c from Prod.mk_le_mk.2 ⟨?_, ?_⟩) hc
    · have := hxy.1; simp at this ⊢; omega
    · exact hxy.2

theorem mem_dropRow {lam : YoungDiagram} {i j : ℕ} : (i, j) ∈ dropRow lam ↔ (i + 1, j) ∈ lam := by
  rw [← mem_cells, ← mem_cells (μ := lam)]
  simp only [dropRow, Finset.mem_image, Finset.mem_filter, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, ⟨h, ha⟩, rfl, rfl⟩
    have : a - 1 + 1 = a := by omega
    simpa [this] using h
  · intro h
    exact ⟨i + 1, j, ⟨h, by simp⟩, by simp, rfl⟩

theorem rowLen_dropRow (lam : YoungDiagram) (i : ℕ) : (dropRow lam).rowLen i = lam.rowLen (i + 1) :=
  nat_eq_of_lt_iff fun j => by
    rw [← mem_iff_lt_rowLen, ← mem_iff_lt_rowLen, mem_dropRow]

end OAI.Saxl
