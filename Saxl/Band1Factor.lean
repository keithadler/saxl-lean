import Mathlib
import Saxl.Band1
import Saxl.Branching
import Saxl.YoungOccurs

/-!
# The width-one band cut, part 2: the factorisation lemma (paper eq. (4.8), `s = 1`)

For a strip tableau `T` of `staircase (m-1) ⊆ staircase m` (the band = last `b` positions), the
polytabloid of `T.t` evaluated at `extendCol v` (letters shifted by one on the first `a` positions,
`0` on the band) equals `sign σ • polytabloid (T.nuTableau) v`, where `σ` is the cyclic shift of
every column (band cell ↦ top cell, other cells one row down).
-/

namespace OAI.Saxl

open Equiv YoungDiagram Finset

attribute [local instance] Fintype.ofFinite

section shift

variable (m : ℕ)

/-- Cyclic shift of a column of the staircase: `(r, c) ↦ (r + 1, c)`, the bottom cell to `(0, c)`. -/
def shiftCell (c : (staircase m).cells) : (staircase m).cells :=
  ⟨if c.val.1 + 1 + c.val.2 < m then (c.val.1 + 1, c.val.2) else (0, c.val.2), by
    have h : (c.val.1, c.val.2) ∈ staircase m := c.2
    rw [mem_staircase] at h
    split_ifs <;> rw [YoungDiagram.mem_cells, mem_staircase] <;> omega⟩

/-- Inverse shift: `(r, c) ↦ (r - 1, c)`, the top cell to the bottom `(m - 1 - c, c)`. -/
def unshiftCell (c : (staircase m).cells) : (staircase m).cells :=
  ⟨if 0 < c.val.1 then (c.val.1 - 1, c.val.2) else (m - 1 - c.val.2, c.val.2), by
    have h : (c.val.1, c.val.2) ∈ staircase m := c.2
    rw [mem_staircase] at h
    split_ifs <;> rw [YoungDiagram.mem_cells, mem_staircase] <;> omega⟩

theorem unshiftCell_shiftCell (c : (staircase m).cells) : unshiftCell m (shiftCell m c) = c := by
  have h : (c.val.1, c.val.2) ∈ staircase m := c.2
  rw [mem_staircase] at h
  apply Subtype.ext
  obtain ⟨⟨r, cc⟩, _⟩ := c
  simp only [shiftCell, unshiftCell]
  split_ifs <;> simp_all <;> omega

theorem shiftCell_unshiftCell (c : (staircase m).cells) : shiftCell m (unshiftCell m c) = c := by
  have h : (c.val.1, c.val.2) ∈ staircase m := c.2
  rw [mem_staircase] at h
  apply Subtype.ext
  obtain ⟨⟨r, cc⟩, _⟩ := c
  simp only [shiftCell, unshiftCell]
  split_ifs <;> simp_all <;> omega

/-- The column shift as a bijection of cells. -/
def shiftEquiv : (staircase m).cells ≃ (staircase m).cells where
  toFun := shiftCell m
  invFun := unshiftCell m
  left_inv := unshiftCell_shiftCell m
  right_inv := shiftCell_unshiftCell m

theorem shiftEquiv_val_snd (c : (staircase m).cells) : ((shiftEquiv m c).val).2 = c.val.2 := by
  simp only [shiftEquiv, shiftCell, Equiv.coe_fn_mk]; split_ifs <;> rfl

theorem shiftEquiv_val_fst_of_lt (c : (staircase m).cells) (h : c.val.1 + 1 + c.val.2 < m) :
    ((shiftEquiv m c).val).1 = c.val.1 + 1 := by
  simp only [shiftEquiv, shiftCell, Equiv.coe_fn_mk, if_pos h]

theorem shiftEquiv_val_fst_of_band (c : (staircase m).cells) (h : c.val.1 + 1 + c.val.2 = m) :
    ((shiftEquiv m c).val).1 = 0 := by
  simp only [shiftEquiv, shiftCell, Equiv.coe_fn_mk, if_neg (by omega : ¬ c.val.1 + 1 + c.val.2 < m)]

end shift

section factor

variable {m a b : ℕ} (T : StripTableau a b (staircase (m - 1)) (staircase m))

local notation "t" => T.t

/-- The column shift as a permutation of positions. -/
def colShift : Perm (Fin (a + b)) := (t).trans ((shiftEquiv m).trans (t).symm)

theorem colShift_apply (p : Fin (a + b)) : colShift T p = (t).symm (shiftEquiv m (t p)) := rfl

theorem t_colShift (p : Fin (a + b)) : t (colShift T p) = shiftEquiv m (t p) := by
  rw [colShift_apply, Equiv.apply_symm_apply]

theorem colShift_mem : colShift T ∈ columnGroup t := by
  rw [mem_columnGroup]
  intro p
  rw [t_colShift, shiftEquiv_val_snd]

/-- Cells on the first `a` positions are not on the band. -/
theorem castAdd_not_band (i : Fin a) : (t (Fin.castAdd b i)).val.1 + 1 + (t (Fin.castAdd b i)).val.2 < m := by
  have h : ((t (Fin.castAdd b i)).val.1, (t (Fin.castAdd b i)).val.2) ∈ staircase (m - 1) :=
    T.mem_nu i
  rw [mem_staircase] at h
  omega

/-- Cells on the last `b` positions are on the band. -/
theorem natAdd_band (j : Fin b) : (t (Fin.natAdd a j)).val.1 + 1 + (t (Fin.natAdd a j)).val.2 = m := by
  have h1 : ((t (Fin.natAdd a j)).val.1, (t (Fin.natAdd a j)).val.2) ∉ staircase (m - 1) :=
    T.not_mem_nu j
  have h2 : ((t (Fin.natAdd a j)).val.1, (t (Fin.natAdd a j)).val.2) ∈ staircase m :=
    (t (Fin.natAdd a j)).2
  rw [mem_staircase] at h1 h2
  omega

theorem rowWord_colShift_castAdd (i : Fin a) :
    (rowWord t (colShift T (Fin.castAdd b i)) : ℕ) = rowWord t (Fin.castAdd b i) + 1 := by
  show (t (colShift T (Fin.castAdd b i))).val.1 = (t (Fin.castAdd b i)).val.1 + 1
  rw [t_colShift, shiftEquiv_val_fst_of_lt _ _ (castAdd_not_band T i)]

theorem rowWord_colShift_natAdd (j : Fin b) :
    (rowWord t (colShift T (Fin.natAdd a j)) : ℕ) = 0 := by
  show (t (colShift T (Fin.natAdd a j))).val.1 = 0
  rw [t_colShift, shiftEquiv_val_fst_of_band _ _ (natAdd_band T j)]

theorem staircase_mono (m : ℕ) : staircase (m - 1) ≤ staircase m := by
  intro c hc
  obtain ⟨i, j⟩ := c
  rw [mem_staircase] at hc ⊢
  omega

/-- The shifted word: `v + 1` on the first `a` positions, `0` on the band. -/
def extendCol (v : Fin a → Fin (dR (m - 1))) : Fin (a + b) → Fin (dR m) :=
  Fin.addCases (fun i => ⟨(v i : ℕ) + 1, by
      have := (v i).2; have := dR_eq (m - 1); have := dR_eq m; have := castAdd_not_band T i; omega⟩)
    (fun j => ⟨0, by have := natAdd_band T j; have := dR_eq m; omega⟩)

theorem extendCol_castAdd (v : Fin a → Fin (dR (m - 1))) (i : Fin a) :
    (extendCol T v (Fin.castAdd b i) : ℕ) = (v i : ℕ) + 1 := by
  simp [extendCol]

theorem extendCol_natAdd (v : Fin a → Fin (dR (m - 1))) (j : Fin b) :
    (extendCol T v (Fin.natAdd a j) : ℕ) = 0 := by
  simp [extendCol]

/-- The unique row-`0` cell of a column: two cells with row `0` and the same column coincide. -/
theorem eq_of_row_zero {p q : Fin (a + b)} (hp : (t p).val.1 = 0) (hq : (t q).val.1 = 0)
    (hc : (t p).val.2 = (t q).val.2) : p = q := by
  apply (t).injective; apply Subtype.ext; exact Prod.ext (hp.trans hq.symm) hc

/-- The key equivalence for the factorisation. -/
theorem extendCol_eq_iff (v : Fin a → Fin (dR (m - 1))) (h : Perm (Fin a)) :
    extendCol T v = rowWord t ∘ ⇑((embA (b := b) h * (colShift T)⁻¹)⁻¹ : Perm (Fin (a + b))) ↔
      v = rowWord (T.nuTableau (staircase_mono m)) ∘ ⇑(h⁻¹ : Perm (Fin a)) := by
  have hinv : (embA (b := b) h * (colShift T)⁻¹)⁻¹ = colShift T * embA h⁻¹ := by
    rw [mul_inv_rev, inv_inv, StripTableau.embA_inv]
  rw [hinv]
  constructor
  · intro H
    funext i
    apply Fin.ext
    have := congrFun H (Fin.castAdd b i)
    rw [Function.comp_apply, Perm.mul_apply, embA_castAdd] at this
    have h2 := congrArg Fin.val this
    rw [extendCol_castAdd, rowWord_colShift_castAdd] at h2
    simp only [Function.comp_apply]
    rw [T.rowWord_nuTableau]
    omega
  · intro H
    funext p
    apply Fin.ext
    refine Fin.addCases (fun i => ?_) (fun j => ?_) p
    · rw [extendCol_castAdd, Function.comp_apply, Perm.mul_apply, embA_castAdd,
        rowWord_colShift_castAdd, ← T.rowWord_nuTableau]
      have := congrFun H i
      simp only [Function.comp_apply] at this
      rw [this]
    · rw [extendCol_natAdd, Function.comp_apply, Perm.mul_apply, embA_natAdd,
        rowWord_colShift_natAdd]

/-- **Factorisation lemma** (paper eq. (4.8), `s = 1`): the staircase polytabloid on the shifted
word is `sign σ` times the smaller staircase polytabloid. -/
theorem polytabloid_extendCol (v : Fin a → Fin (dR (m - 1))) :
    polytabloid t (extendCol T v) =
      ((Perm.sign (colShift T) : ℤ) : ℂ) • polytabloid (T.nuTableau (staircase_mono m)) v := by
  rw [StripTableau.polytabloid_coeff, StripTableau.polytabloid_coeff, smul_eq_mul, Finset.mul_sum]
  symm
  refine Finset.sum_bij_ne_zero
    (fun h _ _ => (⟨embA (h : Perm (Fin a)) * (colShift T)⁻¹,
      (columnGroup t).mul_mem ((T.embA_mem_columnGroup_iff (staircase_mono m) _).2 h.2)
        ((columnGroup t).inv_mem (colShift_mem T))⟩ : columnGroup t))
    (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro h₁ _ _ h₂ _ _ heq
    have heq' : embA (b := b) (h₁ : Perm (Fin a)) * (colShift T)⁻¹ =
        embA (h₂ : Perm (Fin a)) * (colShift T)⁻¹ := congrArg Subtype.val heq
    have h3 : embA (b := b) (h₁ : Perm (Fin a)) = embA h₂ := mul_right_cancel heq'
    ext1
    ext i
    have := congrArg (fun σ : Perm (Fin (a + b)) => (σ (Fin.castAdd b i)).val) h3
    simpa using this
  · intro g _ hne
    have hcond : extendCol T v = rowWord t ∘ ⇑((g : Perm (Fin (a + b)))⁻¹ : Perm (Fin (a + b))) := by
      by_contra hcon
      apply hne
      rw [if_neg hcon, mul_zero]
    -- `g * σ` fixes the band positions
    have hfix : ∀ j, ((g : Perm (Fin (a + b))) * colShift T) (Fin.natAdd a j) = Fin.natAdd a j := by
      intro j
      rw [Perm.mul_apply]
      -- `g⁻¹ (natAdd j)` and `σ (natAdd j)` are both the row-`0` cell of the column of `natAdd j`
      have h1 : (t ((g : Perm (Fin (a + b)))⁻¹ (Fin.natAdd a j))).val.1 = 0 := by
        have := congrFun hcond (Fin.natAdd a j)
        have h2 := congrArg Fin.val this
        rw [extendCol_natAdd] at h2
        exact h2.symm
      have h2 : (t (colShift T (Fin.natAdd a j))).val.1 = 0 := rowWord_colShift_natAdd T j
      have hc1 : (t ((g : Perm (Fin (a + b)))⁻¹ (Fin.natAdd a j))).val.2 = (t (Fin.natAdd a j)).val.2 :=
        (mem_columnGroup t).1 ((columnGroup t).inv_mem g.2) _
      have hc2 : (t (colShift T (Fin.natAdd a j))).val.2 = (t (Fin.natAdd a j)).val.2 :=
        (mem_columnGroup t).1 (colShift_mem T) _
      have heq := eq_of_row_zero T h2 h1 (hc2.trans hc1.symm)
      rw [heq, ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
    obtain ⟨h, hh⟩ := StripTableau.exists_embA_of_fixes hfix
    have hmem : h ∈ columnGroup (T.nuTableau (staircase_mono m)) :=
      (T.embA_mem_columnGroup_iff (staircase_mono m) h).1
        (by rw [← hh]; exact (columnGroup t).mul_mem g.2 (colShift_mem T))
    have hg : (g : Perm (Fin (a + b))) = embA h * (colShift T)⁻¹ := by
      rw [← hh]; group
    refine ⟨⟨h, hmem⟩, Finset.mem_univ _, ?_, ?_⟩
    · have hv : v = rowWord (T.nuTableau (staircase_mono m)) ∘ ⇑(h⁻¹ : Perm (Fin a)) :=
        (extendCol_eq_iff T v h).1 (by rw [← hg]; exact hcond)
      rw [if_pos hv, mul_one]
      rcases Int.units_eq_one_or (Perm.sign h) with hs | hs <;> simp [hs]
    · ext1; exact hg.symm
  · intro h _ _
    show (((Perm.sign (colShift T)) : ℤ) : ℂ) * ((((Perm.sign (h : Perm (Fin a))) : ℤ) : ℂ) * _) =
      (((Perm.sign (embA (b := b) (h : Perm (Fin a)) * (colShift T)⁻¹)) : ℤ) : ℂ) * _
    rw [Perm.sign_mul, Perm.sign_inv, StripTableau.sign_embA, Units.val_mul, Int.cast_mul, ← mul_assoc,
      mul_comm (((Perm.sign (colShift T)) : ℤ) : ℂ)]
    congr 1
    by_cases hv : v = rowWord (T.nuTableau (staircase_mono m)) ∘ ⇑((h : Perm (Fin a))⁻¹ : Perm (Fin a))
    · rw [if_pos hv, if_pos ((extendCol_eq_iff T v h).2 hv)]
    · rw [if_neg hv, if_neg (fun H => hv ((extendCol_eq_iff T v h).1 H))]

end factor

end OAI.Saxl
