import Mathlib

/-!
# Dominance order on partitions

Milestone 4 groundwork (paper §2, eq. (2.1)).  Partitions are `YoungDiagram`s; `λ ⊵ μ` means
every initial sum of row lengths of `λ` is at least that of `μ`.
-/

namespace OAI.Saxl

open YoungDiagram

/-- Sum of the first `k` row lengths. -/
def rowSum (μ : YoungDiagram) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, μ.rowLen i

/-- `Dominates λ μ` : `λ ⊵ μ`. -/
def Dominates (lam mu : YoungDiagram) : Prop := ∀ k, rowSum mu k ≤ rowSum lam k

namespace Dominates

theorem refl (lam : YoungDiagram) : Dominates lam lam := fun _ => le_rfl

theorem trans {a b c : YoungDiagram} (h₁ : Dominates a b) (h₂ : Dominates b c) :
    Dominates a c := fun k => (h₂ k).trans (h₁ k)

end Dominates

/-- `rowLen i = 0` past the last row. -/
theorem rowLen_eq_zero_of_le {μ : YoungDiagram} {i : ℕ} (h : μ.colLen 0 ≤ i) : μ.rowLen i = 0 := by
  by_contra hne
  have : (i, 0) ∈ μ := by
    rw [mem_iff_lt_rowLen]; omega
  rw [mem_iff_lt_colLen] at this
  omega

theorem list_sum_range_map (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-- Row sums over any `N` past the last row give the card. -/
theorem sum_rowLen_eq_card (μ : YoungDiagram) {N : ℕ} (hN : μ.colLen 0 ≤ N) :
    ∑ i ∈ Finset.range N, μ.rowLen i = μ.card := by
  rw [← sum_rowLens_eq_card, rowLens, list_sum_range_map]
  symm
  apply Finset.sum_subset (Finset.range_mono hN)
  intro i hi hi'
  simp only [Finset.mem_range, not_lt] at hi hi'
  exact rowLen_eq_zero_of_le hi'

/-- Counting cells column by column: `∑_{j<q} colLen j = ∑_i min (rowLen i) q`. -/
theorem sum_colLen_eq_sum_min (μ : YoungDiagram) {N : ℕ} (hN : μ.colLen 0 ≤ N) (q : ℕ) :
    ∑ j ∈ Finset.range q, μ.colLen j = ∑ i ∈ Finset.range N, min (μ.rowLen i) q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, ih]
    have hc : μ.colLen q = ∑ i ∈ Finset.range N, if q < μ.rowLen i then 1 else 0 := by
      rw [← Finset.card_filter]
      have : (Finset.range N).filter (fun i => q < μ.rowLen i) = Finset.range (μ.colLen q) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        rw [← mem_iff_lt_rowLen, mem_iff_lt_colLen]
        have := μ.colLen_anti 0 q (Nat.zero_le _)
        omega
      rw [this, Finset.card_range]
    rw [hc, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> omega

/-- Upper bound: for every `k ≤ N`, `S + rowSum k ≤ k q + n`. -/
theorem sum_min_add_rowSum_le (μ : YoungDiagram) {N : ℕ} (hN : μ.colLen 0 ≤ N) (q : ℕ)
    {k : ℕ} (hk : k ≤ N) :
    ∑ i ∈ Finset.range N, min (μ.rowLen i) q + rowSum μ k ≤ k * q + μ.card := by
  rw [← sum_rowLen_eq_card μ hN,
    ← Finset.sum_range_add_sum_Ico (fun i => min (μ.rowLen i) q) hk,
    ← Finset.sum_range_add_sum_Ico (fun i => μ.rowLen i) hk, rowSum]
  have h1 : ∑ i ∈ Finset.range k, min (μ.rowLen i) q ≤ k * q := by
    calc _ ≤ ∑ _i ∈ Finset.range k, q := Finset.sum_le_sum fun i _ => min_le_right _ _
      _ = k * q := by simp
  have h2 : ∑ i ∈ Finset.Ico k N, min (μ.rowLen i) q ≤ ∑ i ∈ Finset.Ico k N, μ.rowLen i :=
    Finset.sum_le_sum fun i _ => min_le_left _ _
  omega

/-- Equality is attained at `k = colLen q`. -/
theorem sum_min_add_rowSum_eq (μ : YoungDiagram) {N : ℕ} (hN : μ.colLen 0 ≤ N) (q : ℕ) :
    ∑ i ∈ Finset.range N, min (μ.rowLen i) q + rowSum μ (μ.colLen q) =
      μ.colLen q * q + μ.card := by
  have hk : μ.colLen q ≤ N := (μ.colLen_anti 0 q (Nat.zero_le _)).trans hN
  rw [← sum_rowLen_eq_card μ hN,
    ← Finset.sum_range_add_sum_Ico (fun i => min (μ.rowLen i) q) hk,
    ← Finset.sum_range_add_sum_Ico (fun i => μ.rowLen i) hk, rowSum]
  have key : ∀ i, q < μ.rowLen i ↔ i < μ.colLen q := fun i => by
    rw [← mem_iff_lt_rowLen, mem_iff_lt_colLen]
  have h1 : ∑ i ∈ Finset.range (μ.colLen q), min (μ.rowLen i) q = μ.colLen q * q := by
    calc _ = ∑ _i ∈ Finset.range (μ.colLen q), q := by
          apply Finset.sum_congr rfl
          intro i hi
          have := (key i).2 (Finset.mem_range.1 hi)
          omega
      _ = _ := by simp
  have h2 : ∑ i ∈ Finset.Ico (μ.colLen q) N, min (μ.rowLen i) q =
      ∑ i ∈ Finset.Ico (μ.colLen q) N, μ.rowLen i := by
    apply Finset.sum_congr rfl
    intro i hi
    have := Finset.mem_Ico.1 hi
    have : ¬ q < μ.rowLen i := fun h => by have := (key i).1 h; omega
    omega
  omega

/-- Conjugation reverses dominance (paper eq. (2.1)). -/
theorem Dominates.transpose {lam mu : YoungDiagram} (h : Dominates lam mu)
    (hc : lam.card = mu.card) : Dominates mu.transpose lam.transpose := by
  intro q
  set N := max (lam.colLen 0) (mu.colLen 0) with hNdef
  have hl : lam.colLen 0 ≤ N := le_max_left _ _
  have hm : mu.colLen 0 ≤ N := le_max_right _ _
  have e : ∀ ν : YoungDiagram, ν.colLen 0 ≤ N →
      rowSum ν.transpose q = ∑ i ∈ Finset.range N, min (ν.rowLen i) q := fun ν hν => by
    rw [rowSum]
    simp only [rowLen_transpose]
    exact sum_colLen_eq_sum_min ν hν q
  rw [e lam hl, e mu hm]
  have hkN : mu.colLen q ≤ N := (mu.colLen_anti 0 q (Nat.zero_le _)).trans hm
  have a := sum_min_add_rowSum_le lam hl q hkN
  have b := sum_min_add_rowSum_eq mu hm q
  have c := h (mu.colLen q)
  omega

theorem nat_eq_of_lt_iff {a b : ℕ} (h : ∀ j, j < a ↔ j < b) : a = b := by
  apply le_antisymm <;> apply Nat.le_of_not_lt <;> intro hh
  · exact lt_irrefl _ ((h _).1 hh)
  · exact lt_irrefl _ ((h _).2 hh)

end OAI.Saxl
