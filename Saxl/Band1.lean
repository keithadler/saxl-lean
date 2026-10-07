import Mathlib
import Saxl.Prop32
import Saxl.WordSectors
import Saxl.Branching

/-!
# The width-one band cut (Prop 4.2 with `s = 1`), part 1

Letters of the pair space are `(a, b) ∈ Fin (dR m) × Fin (dR m)`; `(0, 0)` is *low*, a pair with
both entries nonzero is *high*, anything else is *mixed*.  `unmixedProj` kills every word with a
mixed position (the paper's `P_1`).  The *transversal lemma*: every unmixed summand of `w_m` has its
low positions exactly on the anti-diagonal `{i + j = m - 1}` (paper eqs. (4.6)–(4.7) for `s = 1`).
-/

namespace OAI.Saxl

open Equiv YoungDiagram Finset

section proj

variable {m N : ℕ}

/-- A pair letter is unmixed if both entries are zero or both are nonzero. -/
def Unmixed (ab : Fin (dR m) × Fin (dR m)) : Prop := ((ab.1 : ℕ) = 0 ↔ (ab.2 : ℕ) = 0)

instance (ab : Fin (dR m) × Fin (dR m)) : Decidable (Unmixed ab) := by unfold Unmixed; infer_instance

/-- The letterwise projection killing mixed positions. -/
def unmixedProj : WordSpaceL N (Fin (dR m) × Fin (dR m)) →ₗ[ℂ] WordSpaceL N (Fin (dR m) × Fin (dR m)) where
  toFun f u := if ∀ p, Unmixed (u p) then f u else 0
  map_add' f g := by funext u; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c f := by
    funext u; simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; split_ifs <;> simp

theorem unmixedProj_apply (f : WordSpaceL N (Fin (dR m) × Fin (dR m))) (u : Fin N → Fin (dR m) × Fin (dR m)) :
    unmixedProj f u = if ∀ p, Unmixed (u p) then f u else 0 := rfl

theorem unmixedProj_wordRep (g : Perm (Fin N)) (f : WordSpaceL N (Fin (dR m) × Fin (dR m))) :
    unmixedProj (wordRepL N _ g f) = wordRepL N _ g (unmixedProj f) := by
  funext u
  rw [unmixedProj_apply, wordRepL_apply, wordRepL_apply, unmixedProj_apply]
  have : (∀ p, Unmixed ((u ∘ g) p)) ↔ ∀ p, Unmixed (u p) :=
    ⟨fun h p => by simpa using h (g.symm p), fun h p => h _⟩
  by_cases h : ∀ p, Unmixed (u p)
  · rw [if_pos h, if_pos (this.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]

end proj

section transversal

variable {m N : ℕ} (t : Tableau N (staircase m))

/-- The anti-diagonal band `{p : rowOf p + colOf p = m - 1}`. -/
def bandSet : Finset (Fin N) := univ.filter fun p => rowOf t p + colOf t p = m - 1

/-- The unmixed pair word of two permutations (first layer along rows with letters `colOf`,
second along columns with letters `rowOf`). -/
def pairWordRC (g g' : Perm (Fin N)) (p : Fin N) : Fin (dR m) × Fin (dR m) :=
  (rowWord (swapTableau t) ((g : Perm (Fin N))⁻¹ p), rowWord t ((g' : Perm (Fin N))⁻¹ p))

theorem pairWordRC_fst (g g' : Perm (Fin N)) (p : Fin N) :
    ((pairWordRC t g g' p).1 : ℕ) = colOf t (g⁻¹ p) := rfl

theorem pairWordRC_snd (g g' : Perm (Fin N)) (p : Fin N) :
    ((pairWordRC t g g' p).2 : ℕ) = rowOf t (g'⁻¹ p) := rfl

/-- Row-preserving `g`: in every row exactly one position has first letter `0`. -/
theorem card_lowFirst_row {g : Perm (Fin N)} (hg : ∀ p, rowOf t (g p) = rowOf t p) (i : ℕ)
    (hi : i < m) :
    ((rowFiber t i).filter fun p => colOf t (g⁻¹ p) = 0).card = 1 := by
  have hgi : ∀ p, rowOf t (g⁻¹ p) = rowOf t p := fun p => by
    have := hg (g⁻¹ p)
    rw [show g (g⁻¹ p) = p by rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]] at this
    exact this.symm
  have hcell : (i, 0) ∈ (staircase m).cells := by rw [YoungDiagram.mem_cells, mem_staircase]; omega
  rw [card_eq_one]
  refine ⟨g (t.symm ⟨(i, 0), hcell⟩), ?_⟩
  ext p
  simp only [mem_filter, mem_rowFiber, mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    -- `g⁻¹ p` is the cell `(i, 0)`
    have hc : g⁻¹ p = t.symm ⟨(i, 0), hcell⟩ := by
      apply t.injective
      apply Subtype.ext
      rw [Equiv.apply_symm_apply]
      rw [← hgi p] at h1
      exact Prod.ext h1 h2
    rw [← hc]
    rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
  · rintro rfl
    have hq : g⁻¹ (g (t.symm ⟨(i, 0), hcell⟩)) = t.symm ⟨(i, 0), hcell⟩ := by
      rw [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]
    refine ⟨?_, ?_⟩
    · rw [← hgi, hq]; show (t (t.symm _)).val.1 = i; simp
    · rw [hq]; show (t (t.symm _)).val.2 = 0; simp

/-- The column fiber. -/
def colFiber (j : ℕ) : Finset (Fin N) := univ.filter fun p => colOf t p = j

theorem mem_colFiber {j : ℕ} {p : Fin N} : p ∈ colFiber t j ↔ colOf t p = j := by
  simp [colFiber]

/-- Column-preserving `g'`: in every column exactly one position has second letter `0`. -/
theorem card_lowSecond_col {g' : Perm (Fin N)} (hg' : ∀ p, colOf t (g' p) = colOf t p) (j : ℕ)
    (hj : j < m) :
    ((colFiber t j).filter fun p => rowOf t (g'⁻¹ p) = 0).card = 1 := by
  have hgi : ∀ p, colOf t (g'⁻¹ p) = colOf t p := fun p => by
    have := hg' (g'⁻¹ p)
    rw [show g' (g'⁻¹ p) = p by rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]] at this
    exact this.symm
  have hcell : (0, j) ∈ (staircase m).cells := by rw [YoungDiagram.mem_cells, mem_staircase]; omega
  rw [card_eq_one]
  refine ⟨g' (t.symm ⟨(0, j), hcell⟩), ?_⟩
  ext p
  simp only [mem_filter, mem_colFiber, mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    have hc : g'⁻¹ p = t.symm ⟨(0, j), hcell⟩ := by
      apply t.injective
      apply Subtype.ext
      rw [Equiv.apply_symm_apply]
      rw [← hgi p] at h1
      exact Prod.ext h2 h1
    rw [← hc, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
  · rintro rfl
    have hq : g'⁻¹ (g' (t.symm ⟨(0, j), hcell⟩)) = t.symm ⟨(0, j), hcell⟩ := by
      rw [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]
    refine ⟨?_, ?_⟩
    · rw [← hgi, hq]; show (t (t.symm _)).val.2 = j; simp
    · rw [hq]; show (t (t.symm _)).val.1 = 0; simp

/-- **Transversal lemma.**  If the pair word of a row-preserving `g` and a column-preserving `g'`
is unmixed, then its low positions are exactly the anti-diagonal band. -/
theorem low_iff_band {g g' : Perm (Fin N)} (hg : ∀ p, rowOf t (g p) = rowOf t p)
    (hg' : ∀ p, colOf t (g' p) = colOf t p)
    (hu : ∀ p, Unmixed (pairWordRC t g g' p)) (p : Fin N) :
    colOf t (g⁻¹ p) = 0 ↔ rowOf t p + colOf t p = m - 1 := by
  classical
  -- `L` = low positions; unmixedness: first letter `0 ↔` second letter `0`
  set L : Finset (Fin N) := univ.filter fun q => colOf t (g⁻¹ q) = 0 with hL
  have hL2 : ∀ q, q ∈ L ↔ rowOf t (g'⁻¹ q) = 0 := fun q => by
    rw [hL, mem_filter]; simp only [mem_univ, true_and]
    have := hu q; unfold Unmixed at this
    rw [pairWordRC_fst, pairWordRC_snd] at this; exact this
  have hrow : ∀ i, i < m → ((rowFiber t i).filter fun q => q ∈ L).card = 1 := fun i hi => by
    rw [← card_lowFirst_row t hg i hi]; congr 1; ext q; simp [hL]
  have hcol : ∀ j, j < m → ((colFiber t j).filter fun q => q ∈ L).card = 1 := fun j hj => by
    rw [← card_lowSecond_col t hg' j hj]; congr 1; ext q; simp [hL2]
  -- (1) `L ⊆ band`
  have hsub : ∀ q ∈ L, rowOf t q + colOf t q = m - 1 := by
    intro q hq
    by_contra hne
    have hlt : rowOf t q + colOf t q < m - 1 := by
      have := rowOf_add_colOf_lt t q; omega
    set i := rowOf t q with hi
    -- count `L`-cells in columns `≤ m - 2 - i`
    set S : Finset (Fin N) := L.filter fun r => colOf t r ≤ m - 2 - i with hS
    have hScard : S.card = m - 1 - i := by
      have hfib : ∀ c ∈ range (m - 1 - i), (S.filter fun r => colOf t r = c).card = 1 := by
        intro c hc
        rw [mem_range] at hc
        rw [← hcol c (by omega)]
        congr 1; ext r
        simp only [hS, mem_filter, mem_colFiber]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h3, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h2, by omega⟩, h1⟩
      rw [card_eq_sum_card_fiberwise (f := colOf t) (t := range (m - 1 - i)), sum_congr rfl hfib]
      · simp
      · intro r hr
        rw [mem_coe, hS, mem_filter] at hr
        rw [mem_coe, mem_range]; omega
    -- but rows `> i` each contribute an `L`-cell in those columns, and so does `q`
    set S' : Finset (Fin N) := L.filter fun r => i < rowOf t r with hS'
    have hS'card : S'.card = m - 1 - i := by
      have hfib : ∀ r ∈ Finset.Ico (i + 1) m, (S'.filter fun x => rowOf t x = r).card = 1 := by
        intro r hr
        rw [mem_Ico] at hr
        rw [← hrow r hr.2]
        congr 1; ext x
        simp only [hS', mem_filter, mem_rowFiber]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h3, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h2, by omega⟩, h1⟩
      rw [card_eq_sum_card_fiberwise (f := rowOf t) (t := Finset.Ico (i + 1) m), sum_congr rfl hfib]
      · simp only [sum_const, Nat.card_Ico, smul_eq_mul, mul_one]; omega
      · intro r hr
        rw [mem_coe, hS', mem_filter] at hr
        rw [mem_coe, mem_Ico]
        have := rowOf_lt t r; omega
    have hS'S : S' ⊆ S := by
      intro r hr
      rw [hS', mem_filter] at hr
      rw [hS, mem_filter]
      refine ⟨hr.1, ?_⟩
      have := rowOf_add_colOf_lt t r
      omega
    have hqS : q ∈ S := by
      rw [hS, mem_filter]; exact ⟨hq, by omega⟩
    have hqS' : q ∉ S' := by
      rw [hS', mem_filter]; intro h; exact lt_irrefl _ h.2
    have := card_le_card (insert_subset hqS hS'S)
    rw [card_insert_of_notMem hqS', hS'card, hScard] at this
    omega
  constructor
  · intro h
    exact hsub p (by rw [hL, mem_filter]; exact ⟨mem_univ _, h⟩)
  · intro hband
    -- the unique `L`-cell of row `rowOf p` lies on the band, hence equals `p`
    have hi := rowOf_lt t p
    obtain ⟨q, hq⟩ := card_eq_one.1 (hrow (rowOf t p) hi)
    have hqmem : q ∈ (rowFiber t (rowOf t p)).filter fun r => r ∈ L := by rw [hq]; exact mem_singleton_self q
    rw [mem_filter, mem_rowFiber] at hqmem
    have hqband := hsub q hqmem.2
    have hpq : q = p := by
      apply t.injective; apply Subtype.ext
      show (rowOf t q, colOf t q) = (rowOf t p, colOf t p)
      rw [hqmem.1]
      congr 1
      omega
    rw [hL, mem_filter] at hqmem
    rw [← hpq]; exact hqmem.2.2

end transversal

end OAI.Saxl
