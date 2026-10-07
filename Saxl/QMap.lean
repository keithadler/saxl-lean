import Mathlib
import Saxl.StaircasePairs
import Saxl.SignTwist
import Saxl.WordRep
import Saxl.Antisymmetrizer

/-!
# The map `Q` of Prop 3.2 and its value on `v_R ⊗ v_R` (paper eq. (3.10))

`Q = contentProj α ∘ letterPush q` with `q (a, b) = a + b`.  On the pair tensor of the two
row-alternating polytabloids (`swapTableau t` and `transposeTableau t`), only the summands with
`g' = g · ω` survive (`ω` the row reversal), each contributing `sign ω`; hence
`Q (e_{t'} ⊗ e_{tᵀ}) = (|C| · sign ω) • e_{c₀}` with a nonzero scalar.
-/

namespace OAI.Saxl

open Equiv YoungDiagram Finset

attribute [local instance] Fintype.ofFinite

section contentProj

variable {N d : ℕ}

/-- Projection onto the words of content `α`. -/
def contentProj (α : Fin d → ℕ) : WordSpace N d →ₗ[ℂ] WordSpace N d where
  toFun f u := if content u = α then f u else 0
  map_add' f g := by funext u; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c f := by
    funext u; simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; split_ifs <;> simp

theorem contentProj_apply (α : Fin d → ℕ) (f : WordSpace N d) (u : Fin N → Fin d) :
    contentProj α f u = if content u = α then f u else 0 := rfl

theorem contentProj_single (α : Fin d → ℕ) (w : Fin N → Fin d) :
    contentProj α (Pi.single w 1) = if content w = α then Pi.single w 1 else 0 := by
  funext u
  rw [contentProj_apply]
  by_cases hu : u = w
  · subst hu; split_ifs <;> simp
  · rw [Pi.single_eq_of_ne hu]; split_ifs <;> simp [Pi.single_eq_of_ne hu]

theorem contentProj_wordRep (α : Fin d → ℕ) (g : Perm (Fin N)) (f : WordSpace N d) :
    contentProj α (wordRep N d g f) = wordRep N d g (contentProj α f) := by
  funext u
  rw [contentProj_apply, wordRep_apply, wordRep_apply, contentProj_apply, content_comp_perm]

end contentProj

section rev

variable {m N : ℕ} (t : Tableau N (staircase m))

/-- Row reversal of positions. -/
def rev (p : Fin N) : Fin N :=
  t.symm ⟨(rowOf t p, m - rowOf t p - 1 - colOf t p), by
    rw [YoungDiagram.mem_cells, mem_staircase]; have := rowOf_add_colOf_lt t p; omega⟩

theorem t_rev (p : Fin N) :
    (t (rev t p)).val = (rowOf t p, m - rowOf t p - 1 - colOf t p) := by
  simp [rev]

theorem rowOf_rev (p : Fin N) : rowOf t (rev t p) = rowOf t p := by
  simp [rev, rowOf]

theorem colOf_rev (p : Fin N) : colOf t (rev t p) = m - rowOf t p - 1 - colOf t p := by
  simp [rev, colOf]

theorem rev_rev (p : Fin N) : rev t (rev t p) = p := by
  apply t.injective
  apply Subtype.ext
  rw [t_rev, rowOf_rev, colOf_rev]
  have := rowOf_add_colOf_lt t p
  show (rowOf t p, _) = ((t p).val.1, (t p).val.2)
  show (rowOf t p, _) = (rowOf t p, colOf t p)
  congr 1
  omega

/-- The row reversal as a permutation. -/
def revPerm : Perm (Fin N) := ⟨rev t, rev t, rev_rev t, rev_rev t⟩

theorem revPerm_apply (p : Fin N) : revPerm t p = rev t p := rfl

theorem revPerm_inv : (revPerm t)⁻¹ = revPerm t := by
  ext p; rfl

theorem revPerm_mem_columnGroup : revPerm t ∈ columnGroup (swapTableau t) := by
  rw [mem_columnGroup_swapTableau]
  intro p; exact rowOf_rev t p

end rev

section Q

variable {m N : ℕ} (t : Tableau N (staircase m))

/-- Number of letters of the staircase word spaces. -/
abbrev dR (m : ℕ) : ℕ := (staircase m).colLen 0
/-- Number of letters of the transposed staircase word spaces. -/
abbrev dT (m : ℕ) : ℕ := (staircase m).transpose.colLen 0

theorem dR_eq (m : ℕ) : dR m = m := by rw [dR, colLen_staircase]; omega

theorem dT_eq (m : ℕ) : dT m = m := by rw [dT, colLen_transpose, rowLen_staircase]; omega

/-- The letter map `(a, b) ↦ a + b`. -/
def qmap (ab : Fin (dR m) × Fin (dT m)) : Fin (2 * m) :=
  ⟨ab.1 + ab.2, by
    have h1 : (ab.1 : ℕ) < dR m := ab.1.2
    have h2 : (ab.2 : ℕ) < dT m := ab.2.2
    have := dR_eq m; have := dT_eq m; omega⟩

theorem qmap_val (ab : Fin (dR m) × Fin (dT m)) : (qmap ab : ℕ) = ab.1 + ab.2 := rfl

/-- The column groups of the two row-alternating tableaux agree (row-preserving permutations). -/
theorem mem_columnGroup_transposeTableau_iff (g : Perm (Fin N)) :
    g ∈ columnGroup (transposeTableau t) ↔ ∀ p, rowOf t (g p) = rowOf t p := by
  rw [mem_columnGroup_transposeTableau]; rfl

theorem rowWord_transposeTableau_eq (p : Fin N) :
    (rowWord (transposeTableau t) p : ℕ) = colOf t p := rfl

/-- The letter-sum word of a summand is `pairWord`. -/
theorem qmap_comp (g g' : Perm (Fin N)) :
    (qmap ∘ fun p => (rowWord (swapTableau t) (g⁻¹ p), rowWord (transposeTableau t) (g'⁻¹ p))) =
      pairWord t g g' := by
  funext p
  apply Fin.ext
  simp only [Function.comp_apply, qmap_val, pairWord, rowWord_swapTableau,
    rowWord_transposeTableau_eq]

/-- `pairWord t g g' = targetWord t ↔ g' = g * ω` (for row-preserving `g`, `g' ∈ C_{tᵀ}`). -/
theorem pairWord_eq_target_iff {g g' : Perm (Fin N)} (hg : ∀ p, rowOf t (g p) = rowOf t p)
    (hg' : g' ∈ columnGroup (transposeTableau t)) :
    pairWord t g g' = targetWord t ↔ g' = g * revPerm t := by
  have hgi : ∀ p, rowOf t (g⁻¹ p) = rowOf t p := fun p => by
    have := hg (g⁻¹ p)
    rw [show g (g⁻¹ p) = p by rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]] at this
    exact this.symm
  have hrev : ∀ p, colOf t ((g * revPerm t)⁻¹ p) = m - rowOf t p - 1 - colOf t (g⁻¹ p) := by
    intro p
    rw [mul_inv_rev, Perm.mul_apply, revPerm_inv, revPerm_apply, colOf_rev, hgi]
  have hbound : ∀ p, colOf t (g⁻¹ p) ≤ m - rowOf t p - 1 := fun p => by
    have := rowOf_add_colOf_lt t (g⁻¹ p); rw [hgi] at this; omega
  constructor
  · intro h
    have hω : g * revPerm t ∈ columnGroup (transposeTableau t) := by
      rw [mem_columnGroup_transposeTableau_iff]
      intro p; rw [Perm.mul_apply, revPerm_apply, hg, rowOf_rev]
    have hmem : (g * revPerm t)⁻¹ * g' ∈ columnGroup (transposeTableau t) :=
      (columnGroup _).mul_mem ((columnGroup _).inv_mem hω) hg'
    have hrw : rowWord (transposeTableau t) ∘ ⇑((g * revPerm t)⁻¹ * g') =
        rowWord (transposeTableau t) := by
      funext p
      apply Fin.ext
      simp only [Function.comp_apply, rowWord_transposeTableau_eq, Perm.mul_apply]
      have hp := congrArg (fun w => (w (g' p) : ℕ)) h
      simp only [pairWord, targetWord] at hp
      have h1 : colOf t (g'⁻¹ (g' p)) = colOf t p := by
        rw [show g'⁻¹ (g' p) = p by rw [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]]
      rw [h1] at hp
      rw [hrev]
      have := hbound (g' p)
      omega
    have h1 := eq_one_of_mem_columnGroup_of_rowWord _ hmem hrw
    rw [inv_mul_eq_one] at h1
    exact h1.symm
  · rintro rfl
    funext p
    apply Fin.ext
    simp only [pairWord, targetWord]
    rw [hrev]
    have := hbound p
    omega

open scoped TensorProduct in
/-- Expansion of the pair tensor of the two row-alternating polytabloids. -/
theorem pairLift_polytabloid_expand :
    pairLift (polytabloid (swapTableau t) ⊗ₜ[ℂ] polytabloid (transposeTableau t)) =
      ∑ g : columnGroup (swapTableau t), ∑ g' : columnGroup (transposeTableau t),
        ((((Perm.sign (g : Perm (Fin N))) : ℤ) : ℂ) * (((Perm.sign (g' : Perm (Fin N))) : ℤ) : ℂ)) •
          (Pi.single (fun i => (rowWord (swapTableau t) ((g : Perm (Fin N))⁻¹ i),
            rowWord (transposeTableau t) ((g' : Perm (Fin N))⁻¹ i))) 1 :
            WordSpaceL N (Fin (dR m) × Fin (dT m))) := by
  rw [polytabloid_eq_sum, polytabloid_eq_sum, TensorProduct.sum_tmul, map_sum]
  refine sum_congr rfl fun g _ => ?_
  rw [TensorProduct.tmul_sum, map_sum]
  refine sum_congr rfl fun g' _ => ?_
  rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_smul, map_smul, smul_smul,
    pairLift_tmul, pairMul_single]
  rfl

theorem revPerm_mem_transpose : revPerm t ∈ columnGroup (transposeTableau t) := by
  rw [mem_columnGroup_transposeTableau_iff]; intro p; exact rowOf_rev t p

theorem card_ne_zero_ℂ : (Fintype.card (columnGroup (swapTableau t)) : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

open scoped TensorProduct in
/-- **Paper eq. (3.10)**: `Q (v_R ⊗ v_R) = (|C| · sign ω) • e_{c₀}`. -/
theorem Q_pair :
    contentProj (content (targetWord t)) (letterPush qmap
      (pairLift (polytabloid (swapTableau t) ⊗ₜ[ℂ] polytabloid (transposeTableau t)))) =
      ((Fintype.card (columnGroup (swapTableau t)) : ℂ) * ((Perm.sign (revPerm t) : ℤ) : ℂ)) •
        (Pi.single (targetWord t) 1 : WordSpace N (2 * m)) := by
  classical
  rw [pairLift_polytabloid_expand]
  simp_rw [map_sum, map_smul, letterPush_single, contentProj_single, qmap_comp]
  have hif : ∀ (g : columnGroup (swapTableau t)) (g' : columnGroup (transposeTableau t)),
      (if content (pairWord t (g : Perm (Fin N)) (g' : Perm (Fin N))) = content (targetWord t)
        then (Pi.single (pairWord t (g : Perm (Fin N)) (g' : Perm (Fin N))) 1 : WordSpace N (2 * m))
        else 0) =
      if g' = ⟨(g : Perm (Fin N)) * revPerm t,
          (columnGroup _).mul_mem ((mem_columnGroup_transposeTableau_iff t _).2
            ((mem_columnGroup_swapTableau t _).1 g.2)) (revPerm_mem_transpose t)⟩
        then Pi.single (targetWord t) 1 else 0 := by
    intro g g'
    have hg := (mem_columnGroup_swapTableau t _).1 g.2
    by_cases hc : content (pairWord t (g : Perm (Fin N)) (g' : Perm (Fin N))) = content (targetWord t)
    · have heq := pair_eq_of_content_eq t hg ((mem_columnGroup_transposeTableau_iff t _).1 g'.2) hc
      rw [if_pos hc, heq, if_pos (Subtype.ext ((pairWord_eq_target_iff t hg g'.2).1 heq))]
    · rw [if_neg hc, if_neg]
      intro h
      apply hc
      rw [(pairWord_eq_target_iff t hg g'.2).2 (congrArg Subtype.val h)]
  simp_rw [hif, smul_ite, smul_zero, sum_ite_eq', if_pos (mem_univ _)]
  simp only [Perm.sign_mul, Units.val_mul, Int.cast_mul, ← mul_assoc, sign_sq, one_mul,
    sum_const, card_univ, nsmul_eq_mul, mul_smul]
  rfl

end Q

end OAI.Saxl
