import Mathlib
import Saxl.Band1Factor
import Saxl.Band2Transversal

/-!
# The width-`s` band: column shift, band shape and band tableau

For `T : StripTableau a b (staircase (m - s)) (staircase m)` the band `F = ρ_m \ ρ_{m-s}` meets
column `c` in its bottom `min (m - c) s` cells.  `shiftCellS` cyclically rotates every column so
that the band cells move to rows `0, …, min (m - c) s - 1` and the cells of `ρ_{m-s}` move down by
`s`.  The band with its column structure is the Young diagram `bandShape m s = {(r, c) : r < s,
r + c < m}` (for `s = 2`: the shape `(m, m - 1)`), and `T.bandTableau : Tableau b (bandShape m s)`
records, for each band position, its index inside its column block and its column.
-/

namespace OAI.Saxl

open Equiv YoungDiagram Finset

section shift

variable (m s : ℕ)

/-- Length of the band part of column `c`: `min (m - c) s`, written as `(m - c) - (m - s - c)`. -/
def bandLen (c : ℕ) : ℕ := (m - c) - (m - s - c)

theorem bandLen_eq (c : ℕ) : bandLen m s c = min (m - c) s := by
  unfold bandLen; omega

/-- Column rotation: cells of `ρ_{m-s}` move down by `bandLen`, band cells move to the top. -/
def shiftCellS (c : (staircase m).cells) : (staircase m).cells :=
  ⟨if c.val.1 < m - s - c.val.2 then (c.val.1 + bandLen m s c.val.2, c.val.2)
    else (c.val.1 - (m - s - c.val.2), c.val.2), by
    have h : (c.val.1, c.val.2) ∈ staircase m := c.2
    rw [mem_staircase] at h
    unfold bandLen
    split_ifs <;> rw [YoungDiagram.mem_cells, mem_staircase] <;> omega⟩

/-- Inverse rotation. -/
def unshiftCellS (c : (staircase m).cells) : (staircase m).cells :=
  ⟨if c.val.1 < bandLen m s c.val.2 then (c.val.1 + (m - s - c.val.2), c.val.2)
    else (c.val.1 - bandLen m s c.val.2, c.val.2), by
    have h : (c.val.1, c.val.2) ∈ staircase m := c.2
    rw [mem_staircase] at h
    unfold bandLen
    split_ifs <;> rw [YoungDiagram.mem_cells, mem_staircase] <;> omega⟩

theorem shiftCellS_val (c : (staircase m).cells) : (shiftCellS m s c).val =
    if c.val.1 < m - s - c.val.2 then (c.val.1 + bandLen m s c.val.2, c.val.2)
    else (c.val.1 - (m - s - c.val.2), c.val.2) := rfl

theorem unshiftCellS_val (c : (staircase m).cells) : (unshiftCellS m s c).val =
    if c.val.1 < bandLen m s c.val.2 then (c.val.1 + (m - s - c.val.2), c.val.2)
    else (c.val.1 - bandLen m s c.val.2, c.val.2) := rfl

theorem unshiftCellS_shiftCellS (c : (staircase m).cells) :
    unshiftCellS m s (shiftCellS m s c) = c := by
  have h : (c.val.1, c.val.2) ∈ staircase m := c.2
  rw [mem_staircase] at h
  apply Subtype.ext
  rw [unshiftCellS_val, shiftCellS_val]
  split_ifs with h1 h2 h2 <;> simp only at h2 ⊢ <;>
    first
    | (exfalso; unfold bandLen at *; omega)
    | (refine Prod.ext ?_ rfl; unfold bandLen at *; omega)

theorem shiftCellS_unshiftCellS (c : (staircase m).cells) :
    shiftCellS m s (unshiftCellS m s c) = c := by
  have h : (c.val.1, c.val.2) ∈ staircase m := c.2
  rw [mem_staircase] at h
  apply Subtype.ext
  rw [shiftCellS_val, unshiftCellS_val]
  split_ifs with h1 h2 h2 <;> simp only at h2 ⊢ <;>
    first
    | (exfalso; unfold bandLen at *; omega)
    | (refine Prod.ext ?_ rfl; unfold bandLen at *; omega)

/-- The column rotation as a bijection of cells. -/
def shiftEquivS : (staircase m).cells ≃ (staircase m).cells where
  toFun := shiftCellS m s
  invFun := unshiftCellS m s
  left_inv := unshiftCellS_shiftCellS m s
  right_inv := shiftCellS_unshiftCellS m s

theorem shiftEquivS_val_snd (c : (staircase m).cells) : ((shiftEquivS m s c).val).2 = c.val.2 := by
  simp only [shiftEquivS, shiftCellS, Equiv.coe_fn_mk]; split_ifs <;> rfl

theorem shiftEquivS_val_fst_of_lt (c : (staircase m).cells) (h : c.val.1 < m - s - c.val.2) :
    ((shiftEquivS m s c).val).1 = c.val.1 + s := by
  have h2 : (c.val.1, c.val.2) ∈ staircase m := c.2
  rw [mem_staircase] at h2
  simp only [shiftEquivS, shiftCellS, Equiv.coe_fn_mk, if_pos h, bandLen]
  omega

theorem shiftEquivS_val_fst_of_band (c : (staircase m).cells) (h : m - s - c.val.2 ≤ c.val.1) :
    ((shiftEquivS m s c).val).1 = c.val.1 - (m - s - c.val.2) := by
  simp only [shiftEquivS, shiftCellS, Equiv.coe_fn_mk, if_neg (not_lt.2 h)]

/-- The band shape `{(r, c) : r < s, r + c < m}` (for `s = 2`: `(m, m - 1)`). -/
def bandShape : YoungDiagram where
  cells := (staircase m).cells.filter fun c => c.1 < s
  isLowerSet := by
    rintro ⟨i2, j2⟩ ⟨i1, j1⟩ ⟨hi : i1 ≤ i2, hj : j1 ≤ j2⟩ h
    rw [Finset.mem_coe, mem_filter, YoungDiagram.mem_cells, mem_staircase] at h ⊢
    omega

theorem mem_bandShape {r c : ℕ} : (r, c) ∈ bandShape m s ↔ r < s ∧ r + c < m := by
  rw [← YoungDiagram.mem_cells]
  show (r, c) ∈ (staircase m).cells.filter _ ↔ _
  rw [mem_filter, YoungDiagram.mem_cells, mem_staircase]
  constructor
  · rintro ⟨⟨_, _, h⟩, hs⟩; exact ⟨hs, h⟩
  · rintro ⟨hs, h⟩; exact ⟨⟨by omega, by omega, h⟩, hs⟩

theorem colLen_bandShape (hs : s ≤ m) : (bandShape m s).colLen 0 = s :=
  nat_eq_of_lt_iff fun i => by rw [← mem_iff_lt_colLen, mem_bandShape]; omega


end shift

section tableau

variable {m s a b : ℕ} (T : StripTableau a b (staircase (m - s)) (staircase m))

local notation "t" => T.t

theorem staircase_sub_le (m s : ℕ) : staircase (m - s) ≤ staircase m := by
  intro c hc
  obtain ⟨i, j⟩ := c
  rw [mem_staircase] at hc ⊢
  omega

/-- The column rotation as a permutation of positions. -/
def colShiftS : Perm (Fin (a + b)) := (t).trans ((shiftEquivS m s).trans (t).symm)

theorem t_colShiftS (p : Fin (a + b)) : t (colShiftS T p) = shiftEquivS m s (t p) := by
  show t ((t).symm (shiftEquivS m s (t p))) = _
  rw [Equiv.apply_symm_apply]

theorem colShiftS_mem : colShiftS T ∈ columnGroup t := by
  rw [mem_columnGroup]
  intro p
  rw [t_colShiftS, shiftEquivS_val_snd]

/-- Cells on the first `a` positions lie in `ρ_{m-s}`: row `< m - s - col`. -/
theorem castAdd_small (i : Fin a) :
    (t (Fin.castAdd b i)).val.1 < m - s - (t (Fin.castAdd b i)).val.2 := by
  have h : ((t (Fin.castAdd b i)).val.1, (t (Fin.castAdd b i)).val.2) ∈ staircase (m - s) :=
    T.mem_nu i
  rw [mem_staircase] at h
  omega

/-- Cells on the last `b` positions lie in the band: row `≥ m - s - col`. -/
theorem natAdd_bandS (j : Fin b) :
    m - s - (t (Fin.natAdd a j)).val.2 ≤ (t (Fin.natAdd a j)).val.1 := by
  have h1 : ((t (Fin.natAdd a j)).val.1, (t (Fin.natAdd a j)).val.2) ∉ staircase (m - s) :=
    T.not_mem_nu j
  have h2 : ((t (Fin.natAdd a j)).val.1, (t (Fin.natAdd a j)).val.2) ∈ staircase m :=
    (t (Fin.natAdd a j)).2
  rw [mem_staircase] at h1 h2
  omega

theorem rowWord_colShiftS_castAdd (i : Fin a) :
    (rowWord t (colShiftS T (Fin.castAdd b i)) : ℕ) = rowWord t (Fin.castAdd b i) + s := by
  show (t (colShiftS T (Fin.castAdd b i))).val.1 = (t (Fin.castAdd b i)).val.1 + s
  rw [t_colShiftS, shiftEquivS_val_fst_of_lt _ _ _ (castAdd_small T i)]

theorem rowWord_colShiftS_natAdd (j : Fin b) :
    (rowWord t (colShiftS T (Fin.natAdd a j)) : ℕ) =
      rowWord t (Fin.natAdd a j) - (m - s - (t (Fin.natAdd a j)).val.2) := by
  show (t (colShiftS T (Fin.natAdd a j))).val.1 = _
  rw [t_colShiftS, shiftEquivS_val_fst_of_band _ _ _ (natAdd_bandS T j)]
  rfl

/-- Every band cell sits at a `natAdd` position. -/
theorem exists_natAdd_of_not_mem_small {p : Fin (a + b)}
    (hp : ((t p).val.1, (t p).val.2) ∉ staircase (m - s)) : ∃ j, p = Fin.natAdd a j := by
  rcases StripTableau.exists_castAdd_or_natAdd p with ⟨i, rfl⟩ | h
  · exact absurd (T.mem_nu i) hp
  · exact h

/-- The band tableau: position `natAdd j` goes to `(row - (m - s - col), col)`. -/
noncomputable def bandTableau : Tableau b (bandShape m s) :=
  Equiv.ofBijective
    (fun j => ⟨((t (Fin.natAdd a j)).val.1 - (m - s - (t (Fin.natAdd a j)).val.2),
      (t (Fin.natAdd a j)).val.2), by
        have h1 := natAdd_bandS T j
        have h2 : ((t (Fin.natAdd a j)).val.1, (t (Fin.natAdd a j)).val.2) ∈ staircase m :=
          (t (Fin.natAdd a j)).2
        rw [mem_staircase] at h2
        rw [YoungDiagram.mem_cells, mem_bandShape]
        omega⟩) <| by
    refine ⟨fun j j' h => ?_, fun c => ?_⟩
    · have h' := congrArg Subtype.val h
      simp only [Prod.mk.injEq] at h'
      have h1 := natAdd_bandS T j
      have h2 := natAdd_bandS T j'
      have hcell : t (Fin.natAdd a j) = t (Fin.natAdd a j') := by
        apply Subtype.ext
        refine Prod.ext ?_ h'.2
        omega
      have h3 := congrArg Fin.val ((t).injective hcell)
      simp only [Fin.coe_natAdd] at h3
      exact Fin.ext (by omega)
    · obtain ⟨⟨r, c⟩, hc⟩ := c
      rw [YoungDiagram.mem_cells, mem_bandShape] at hc
      have hmem : (r + (m - s - c), c) ∈ (staircase m).cells := by
        rw [YoungDiagram.mem_cells, mem_staircase]; omega
      have hnot : (r + (m - s - c), c) ∉ staircase (m - s) := by
        rw [mem_staircase]; omega
      obtain ⟨j, hj⟩ := exists_natAdd_of_not_mem_small T (p := (t).symm ⟨_, hmem⟩)
        (by rw [Equiv.apply_symm_apply]; exact hnot)
      refine ⟨j, Subtype.ext ?_⟩
      have ht : t (Fin.natAdd a j) = ⟨(r + (m - s - c), c), hmem⟩ := by
        rw [← hj, Equiv.apply_symm_apply]
      simp only [ht]
      refine Prod.ext ?_ rfl
      show r + (m - s - c) - (m - s - c) = r
      omega

theorem bandTableau_val (j : Fin b) : (bandTableau T j).val =
    ((t (Fin.natAdd a j)).val.1 - (m - s - (t (Fin.natAdd a j)).val.2),
      (t (Fin.natAdd a j)).val.2) := rfl

theorem bandTableau_val_snd (j : Fin b) : (bandTableau T j).val.2 = (t (Fin.natAdd a j)).val.2 :=
  rfl

theorem rowWord_bandTableau (j : Fin b) :
    (rowWord (bandTableau T) j : ℕ) = rowWord t (colShiftS T (Fin.natAdd a j)) := by
  rw [rowWord_colShiftS_natAdd]; rfl

/-- `embB τ` is a column permutation of `t` iff `τ` is one of the band tableau. -/
theorem embB_mem_columnGroup_iff (τ : Perm (Fin b)) :
    embB (a := a) τ ∈ columnGroup t ↔ τ ∈ columnGroup (bandTableau T) := by
  simp only [mem_columnGroup]
  constructor
  · intro H j
    have := H (Fin.natAdd a j)
    rw [embB_natAdd] at this
    rw [bandTableau_val_snd, bandTableau_val_snd]
    exact this
  · intro H p
    rcases StripTableau.exists_castAdd_or_natAdd p with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · simp only [embB_castAdd]
    · have := H j
      rw [bandTableau_val_snd, bandTableau_val_snd] at this
      rw [embB_natAdd (a := a) τ j]
      exact this

/-- `embPair (h, τ)` is a column permutation of `t` iff both components are. -/
theorem embPair_mem_columnGroup_iff (h : Perm (Fin a)) (τ : Perm (Fin b)) :
    embPair (h, τ) ∈ columnGroup t ↔
      h ∈ columnGroup (T.nuTableau (staircase_sub_le m s)) ∧ τ ∈ columnGroup (bandTableau T) := by
  rw [embPair_eq_mul]
  constructor
  · intro H
    simp only [mem_columnGroup] at H
    constructor
    · rw [← T.embA_mem_columnGroup_iff (staircase_sub_le m s) h, mem_columnGroup]
      intro p
      rcases StripTableau.exists_castAdd_or_natAdd p with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · have := H (Fin.castAdd b i)
        simp only [Perm.mul_apply, embB_castAdd] at this
        exact this
      · simp only [embA_natAdd]
    · rw [← embB_mem_columnGroup_iff T τ, mem_columnGroup]
      intro p
      rcases StripTableau.exists_castAdd_or_natAdd p with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · simp only [embB_castAdd]
      · have := H (Fin.natAdd a j)
        simp only [Perm.mul_apply, embB_natAdd, embA_natAdd] at this
        rw [embB_natAdd (a := a) τ j]
        exact this
  · rintro ⟨h1, h2⟩
    exact (columnGroup t).mul_mem ((T.embA_mem_columnGroup_iff _ h).2 h1)
      ((embB_mem_columnGroup_iff T τ).2 h2)

theorem sign_embPair (h : Perm (Fin a)) (τ : Perm (Fin b)) :
    Perm.sign (embPair (h, τ)) = Perm.sign h * Perm.sign τ := by
  simp [embPair, Perm.sign_permCongr, Perm.sign_sumCongr]

/-- The extended word: `v + s` on the first `a` positions, `y` on the band. -/
def extendS (hs : s ≤ m) (v : Fin a → Fin (dR (m - s))) (y : Fin b → Fin ((bandShape m s).colLen 0)) :
    Fin (a + b) → Fin (dR m) :=
  Fin.addCases (fun i => ⟨(v i : ℕ) + s, by
      have := (v i).2; have := dR_eq (m - s); have := dR_eq m; omega⟩)
    (fun j => ⟨(y j : ℕ), by
      have := (y j).2; have := colLen_bandShape m s hs; have := dR_eq m; omega⟩)

theorem extendS_castAdd (hs : s ≤ m) (v : Fin a → Fin (dR (m - s)))
    (y : Fin b → Fin ((bandShape m s).colLen 0)) (i : Fin a) :
    (extendS hs v y (Fin.castAdd b i) : ℕ) = (v i : ℕ) + s := by
  simp [extendS]

theorem extendS_natAdd (hs : s ≤ m) (v : Fin a → Fin (dR (m - s)))
    (y : Fin b → Fin ((bandShape m s).colLen 0)) (j : Fin b) :
    (extendS hs v y (Fin.natAdd a j) : ℕ) = (y j : ℕ) := by
  simp [extendS]

end tableau


end OAI.Saxl
