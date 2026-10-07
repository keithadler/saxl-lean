import Mathlib
import Saxl.Band2Shift
import Saxl.WordSectors

/-!
# The factorisation lemma for a band of width `s` (paper eq. (4.8))

On a word that is `v + s` on the positions of `ρ_{m-s}` and `y` on the band, the staircase
polytabloid factorises: `e_t (extendS v y) = sign σ · e_ν v · e_β y`, where `σ` is the column
rotation, `ν` the `ρ_{m-s}`-tableau on the first `a` positions and `β` the band tableau.
-/

namespace OAI.Saxl

open Equiv YoungDiagram Finset

attribute [local instance] Fintype.ofFinite

section factor

variable {m s a b : ℕ} (T : StripTableau a b (staircase (m - s)) (staircase m)) (hs : s ≤ m)

local notation "t" => T.t
local notation "ν" => T.nuTableau (staircase_sub_le m s)
local notation "β" => bandTableau T

/-- A permutation sending band positions to band positions is an `embPair`. -/
theorem exists_embPair_of_natAdd {g : Perm (Fin (a + b))}
    (hg : ∀ j, ∃ j', g (Fin.natAdd a j) = Fin.natAdd a j') :
    ∃ p : Perm (Fin a) × Perm (Fin b), g = embPair p := by
  apply exists_embPair_of_smul_eq
  apply Subtype.ext
  rw [smul_subsets_val]
  apply eq_of_subset_of_card_le
  · intro q hq
    rw [Finset.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    obtain ⟨j, rfl⟩ := (mem_lastPositions p).1 hp
    obtain ⟨j', hj'⟩ := hg j
    rw [Equiv.coe_toEmbedding, hj']
    exact (mem_lastPositions _).2 ⟨j', rfl⟩
  · rw [card_map]

/-- The key equivalence: the extended word is a term of the big polytabloid iff its two parts are
terms of the two small ones. -/
theorem extendS_eq_iff (v : Fin a → Fin (dR (m - s))) (y : Fin b → Fin ((bandShape m s).colLen 0))
    (h : Perm (Fin a)) (τ : Perm (Fin b)) :
    extendS hs v y = rowWord t ∘ ⇑((embPair (h, τ) * (colShiftS T)⁻¹)⁻¹ : Perm (Fin (a + b))) ↔
      v = rowWord ν ∘ ⇑(h⁻¹ : Perm (Fin a)) ∧ y = rowWord β ∘ ⇑(τ⁻¹ : Perm (Fin b)) := by
  have hinv : (embPair (h, τ) * (colShiftS T)⁻¹)⁻¹ = colShiftS T * embPair (h⁻¹, τ⁻¹) := by
    rw [mul_inv_rev, inv_inv, ← map_inv, Prod.inv_mk]
  rw [hinv]
  constructor
  · intro H
    refine ⟨?_, ?_⟩
    · funext i
      apply Fin.ext
      have := congrArg Fin.val (congrFun H (Fin.castAdd b i))
      rw [extendS_castAdd, Function.comp_apply, Perm.mul_apply, embPair_castAdd,
        rowWord_colShiftS_castAdd] at this
      dsimp only at this
      simp only [Function.comp_apply]
      rw [T.rowWord_nuTableau]
      omega
    · funext j
      apply Fin.ext
      have := congrArg Fin.val (congrFun H (Fin.natAdd a j))
      rw [extendS_natAdd, Function.comp_apply, Perm.mul_apply, embPair_natAdd] at this
      dsimp only at this
      simp only [Function.comp_apply]
      rw [rowWord_bandTableau]
      exact this
  · rintro ⟨Hv, Hy⟩
    funext p
    apply Fin.ext
    refine Fin.addCases (fun i => ?_) (fun j => ?_) p
    · rw [extendS_castAdd, Function.comp_apply, Perm.mul_apply, embPair_castAdd,
        rowWord_colShiftS_castAdd]
      dsimp only
      rw [← T.rowWord_nuTableau]
      have := congrFun Hv i
      simp only [Function.comp_apply] at this
      rw [this]
    · rw [extendS_natAdd, Function.comp_apply, Perm.mul_apply, embPair_natAdd]
      dsimp only
      rw [← rowWord_bandTableau]
      have := congrFun Hy j
      simp only [Function.comp_apply] at this
      rw [this]

/-- Band positions carry letters `< s` after the rotation. -/
theorem rowWord_colShiftS_natAdd_lt (j : Fin b) :
    (rowWord t (colShiftS T (Fin.natAdd a j)) : ℕ) < s := by
  rw [rowWord_colShiftS_natAdd]
  have h2 : ((t (Fin.natAdd a j)).val.1, (t (Fin.natAdd a j)).val.2) ∈ staircase m :=
    (t (Fin.natAdd a j)).2
  rw [mem_staircase] at h2
  have h1 := natAdd_bandS T j
  show (t (Fin.natAdd a j)).val.1 - (m - s - (t (Fin.natAdd a j)).val.2) < s
  omega

/-- **Factorisation lemma** (paper eq. (4.8)). -/
theorem polytabloid_extendS (v : Fin a → Fin (dR (m - s))) (y : Fin b → Fin ((bandShape m s).colLen 0)) :
    polytabloid t (extendS hs v y) =
      ((Perm.sign (colShiftS T) : ℤ) : ℂ) • (polytabloid ν v * polytabloid β y) := by
  have hR : (∑ x : columnGroup ν × columnGroup β,
      ((((Perm.sign (x.1 : Perm (Fin a))) : ℤ) : ℂ) *
        (if v = rowWord ν ∘ ⇑((x.1 : Perm (Fin a))⁻¹ : Perm (Fin a)) then 1 else 0)) *
      ((((Perm.sign (x.2 : Perm (Fin b))) : ℤ) : ℂ) *
        (if y = rowWord β ∘ ⇑((x.2 : Perm (Fin b))⁻¹ : Perm (Fin b)) then 1 else 0))) =
      polytabloid ν v * polytabloid β y := by
    rw [Fintype.sum_prod_type, StripTableau.polytabloid_coeff, StripTableau.polytabloid_coeff,
      sum_mul_sum]
  rw [StripTableau.polytabloid_coeff, ← hR, smul_eq_mul, mul_sum]
  symm
  refine Finset.sum_bij_ne_zero
    (fun x _ _ => (⟨embPair ((x.1 : Perm (Fin a)), (x.2 : Perm (Fin b))) * (colShiftS T)⁻¹,
      (columnGroup t).mul_mem ((embPair_mem_columnGroup_iff T _ _).2 ⟨x.1.2, x.2.2⟩)
        ((columnGroup t).inv_mem (colShiftS_mem T))⟩ : columnGroup t))
    (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro x₁ _ _ x₂ _ _ heq
    have heq' : embPair ((x₁.1 : Perm (Fin a)), (x₁.2 : Perm (Fin b))) * (colShiftS T)⁻¹ =
        embPair ((x₂.1 : Perm (Fin a)), (x₂.2 : Perm (Fin b))) * (colShiftS T)⁻¹ :=
      congrArg Subtype.val heq
    have h3 := mul_right_cancel heq'
    refine Prod.ext (Subtype.ext (Equiv.ext fun i => ?_)) (Subtype.ext (Equiv.ext fun j => ?_))
    · have := congrArg (fun σ : Perm (Fin (a + b)) => (σ (Fin.castAdd b i)).val) h3
      exact Fin.ext (by simpa using this)
    · have := congrArg (fun σ : Perm (Fin (a + b)) => (σ (Fin.natAdd a j)).val) h3
      exact Fin.ext (by simpa using this)
  · intro g _ hne
    have hcond : extendS hs v y = rowWord t ∘ ⇑((g : Perm (Fin (a + b)))⁻¹ : Perm (Fin (a + b))) := by
      by_contra hcon
      apply hne
      rw [if_neg hcon, mul_zero]
    -- `g * σ` sends band positions to band positions
    have hnat : ∀ j, ∃ j', ((g : Perm (Fin (a + b))) * colShiftS T) (Fin.natAdd a j) =
        Fin.natAdd a j' := by
      intro j
      rw [Perm.mul_apply]
      rcases StripTableau.exists_castAdd_or_natAdd
          ((g : Perm (Fin (a + b))) (colShiftS T (Fin.natAdd a j))) with ⟨i, hi⟩ | ⟨j', hj'⟩
      · exfalso
        have h1 := congrArg Fin.val (congrFun hcond (Fin.castAdd b i))
        rw [extendS_castAdd, Function.comp_apply, ← hi, ← Perm.mul_apply, inv_mul_cancel,
          Perm.one_apply] at h1
        have h2 := rowWord_colShiftS_natAdd_lt T j
        omega
      · exact ⟨j', hj'⟩
    obtain ⟨⟨h, τ⟩, hhτ⟩ := exists_embPair_of_natAdd hnat
    have hmem : h ∈ columnGroup ν ∧ τ ∈ columnGroup β :=
      (embPair_mem_columnGroup_iff T h τ).1
        (by rw [← hhτ]; exact (columnGroup t).mul_mem g.2 (colShiftS_mem T))
    have hg : (g : Perm (Fin (a + b))) = embPair (h, τ) * (colShiftS T)⁻¹ := by
      rw [← hhτ]; group
    refine ⟨(⟨h, hmem.1⟩, ⟨τ, hmem.2⟩), Finset.mem_univ _, ?_, ?_⟩
    · obtain ⟨hv, hy⟩ := (extendS_eq_iff T hs v y h τ).1 (by rw [← hg]; exact hcond)
      dsimp only
      rw [if_pos hv, if_pos hy, mul_one, mul_one]
      rcases Int.units_eq_one_or (Perm.sign h) with hs1 | hs1 <;>
      rcases Int.units_eq_one_or (Perm.sign τ) with hs2 | hs2 <;>
      rcases Int.units_eq_one_or (Perm.sign (colShiftS T)) with hs3 | hs3 <;> simp [hs1, hs2, hs3]
    · ext1; exact hg.symm
  · intro x _ _
    dsimp only
    rw [Perm.sign_mul, Perm.sign_inv, sign_embPair, Units.val_mul, Units.val_mul, Int.cast_mul,
      Int.cast_mul]
    by_cases hv : v = rowWord ν ∘ ⇑((x.1 : Perm (Fin a))⁻¹ : Perm (Fin a)) <;>
    by_cases hy : y = rowWord β ∘ ⇑((x.2 : Perm (Fin b))⁻¹ : Perm (Fin b))
    · rw [if_pos hv, if_pos hy, if_pos ((extendS_eq_iff T hs v y _ _).2 ⟨hv, hy⟩)]
      ring
    · rw [if_pos hv, if_neg hy, if_neg (fun H => hy ((extendS_eq_iff T hs v y _ _).1 H).2)]
      ring
    · rw [if_neg hv, if_neg (fun H => hv ((extendS_eq_iff T hs v y _ _).1 H).1)]
      ring
    · rw [if_neg hv, if_neg (fun H => hv ((extendS_eq_iff T hs v y _ _).1 H).1)]
      ring

end factor

end OAI.Saxl
