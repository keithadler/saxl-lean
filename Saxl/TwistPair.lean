import Mathlib
import Saxl.QMap
import Saxl.SignTwist
import Saxl.SignTwistOccurs
import Saxl.Antisymmetrizer
import Saxl.SubmoduleTheorem

/-!
# `id ⊗ Θ` on the pair-letter space (Prop 3.2, eqs. (3.4)–(3.7))

`idΘ` sends `e_{(a,b)} ↦ pairLift (e_a ⊗ Θ e_b)`; it is sign-twisted equivariant.  With
`u = Σ_{h ∈ H_R} h v_C` we have `Σ_{h∈H_R} ε(h) h (v_R ⊗ v_C) = v_R ⊗ u`, and `Θ u = c₁ • v_R'`
with `c₁ ≠ 0` (`v_R' = e_{tᵀ}`), by the antisymmetriser lemma — no multiplicity-one needed.
-/

namespace OAI.Saxl

open Equiv YoungDiagram Finset

attribute [local instance] Fintype.ofFinite

open scoped TensorProduct

section generic

variable {n : ℕ} {L : Type} [Fintype L] [DecidableEq L]

/-- Basis expansion in a general word space. -/
theorem eq_sum_single_L (f : WordSpaceL n L) :
    f = ∑ u, f u • (Pi.single u 1 : WordSpaceL n L) := by
  ext a
  rw [Finset.sum_apply, Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

end generic

section twist

variable {m N : ℕ} (t : Tableau N (staircase m))

/-- `id ⊗ Θ` on the pair space. -/
noncomputable def idΘ : WordSpaceL N (Fin (dR m) × Fin (dR m)) →ₗ[ℂ]
    WordSpaceL N (Fin (dR m) × Fin (dT m)) where
  toFun f := ∑ u, f u • pairLift (Pi.single (Prod.fst ∘ u) 1 ⊗ₜ[ℂ] Θ t (Pi.single (Prod.snd ∘ u) 1))
  map_add' f g := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.smul_sum, smul_smul]

theorem idΘ_single (u : Fin N → Fin (dR m) × Fin (dR m)) :
    idΘ t (Pi.single u 1) =
      pairLift (Pi.single (Prod.fst ∘ u) 1 ⊗ₜ[ℂ] Θ t (Pi.single (Prod.snd ∘ u) 1)) := by
  show ∑ u', (Pi.single u (1 : ℂ) : WordSpaceL N _) u' • _ = _
  rw [Finset.sum_eq_single u]
  · simp
  · intro u' _ hu'; simp [Pi.single_eq_of_ne hu']
  · intro h; exact absurd (Finset.mem_univ _) h

theorem idΘ_pairLift_single (a b : Fin N → Fin (dR m)) :
    idΘ t (pairLift (Pi.single a 1 ⊗ₜ[ℂ] Pi.single b 1)) =
      pairLift (Pi.single a 1 ⊗ₜ[ℂ] Θ t (Pi.single b 1)) := by
  rw [pairLift_tmul, pairMul_single, idΘ_single]
  rfl

/-- `idΘ (f ⊗ g) = f ⊗ Θ g`. -/
theorem idΘ_pairLift (f g : WordSpace N (dR m)) :
    idΘ t (pairLift (f ⊗ₜ[ℂ] g)) = pairLift (f ⊗ₜ[ℂ] Θ t g) := by
  conv_lhs => rw [eq_sum_single f, eq_sum_single g]
  conv_rhs => rw [eq_sum_single f, eq_sum_single g]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, map_smul, idΘ_pairLift_single]

/-- Twisted equivariance of `idΘ`. -/
theorem idΘ_wordRep (g : Perm (Fin N)) (f : WordSpaceL N (Fin (dR m) × Fin (dR m))) :
    idΘ t (wordRepL N _ g f) =
      ((Perm.sign g : ℤ) : ℂ) • wordRepL N _ g (idΘ t f) := by
  conv_lhs => rw [eq_sum_single_L f]
  conv_rhs => rw [eq_sum_single_L f]
  simp only [map_sum, map_smul, Finset.smul_sum, wordRepL_single, idΘ_single]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_comm]
  congr 1
  have h1 : Prod.fst ∘ (u ∘ ⇑g⁻¹) = (Prod.fst ∘ u) ∘ ⇑g⁻¹ := rfl
  have h2 : Prod.snd ∘ (u ∘ ⇑g⁻¹) = (Prod.snd ∘ u) ∘ ⇑g⁻¹ := rfl
  rw [h1, h2, ← wordRepL_single, ← wordRepL_single, ← pairLift_tprod, Representation.tprod_apply,
    TensorProduct.map_tmul]
  show pairLift (_ ⊗ₜ Θ t (wordRep N _ g _)) = _
  rw [Θ_wordRep, TensorProduct.tmul_smul, map_smul]
  rfl

end twist

section u

variable {m N : ℕ} (t : Tableau N (staircase m))

/-- `u = Σ_{h ∈ H_R} h v_C` (paper eq. (3.4)). -/
noncomputable def uvec : WordSpace N (dR m) :=
  ∑ h : columnGroup (swapTableau t), wordRep N (dR m) (h : Perm (Fin N)) (polytabloid t)

theorem uvec_mem_specht : uvec t ∈ Specht t :=
  Submodule.sum_mem _ fun h _ => Submodule.subset_span ⟨_, rfl⟩

theorem rowWord_comp_eq_of_mem (h : columnGroup (swapTableau t)) :
    rowWord t ∘ ⇑(h : Perm (Fin N)) = rowWord t := by
  funext i; apply Fin.ext; exact (mem_columnGroup_swapTableau t _).1 h.2 i

/-- The coefficient of `u` at the row word is `|H_R|`. -/
theorem uvec_apply_rowWord :
    uvec t (rowWord t) = (Fintype.card (columnGroup (swapTableau t)) : ℂ) := by
  rw [uvec, Finset.sum_apply]
  simp only [wordRep_apply]
  rw [Finset.card_univ.symm, Finset.cast_card]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [StripTableau.polytabloid_coeff, Finset.sum_eq_single (1 : columnGroup t)]
  · simp [rowWord_comp_eq_of_mem t h]
  · intro k _ hk
    have hne : rowWord t ∘ ⇑(h : Perm (Fin N)) ≠ rowWord t ∘ ⇑((k : Perm (Fin N))⁻¹ : Perm (Fin N)) := by
      intro heq
      apply hk
      have h1 : rowWord t ∘ ⇑((h : Perm (Fin N)) * k) = rowWord t := by
        funext i
        have := congrFun heq ((k : Perm (Fin N)) i)
        simp only [Function.comp_apply, perm_inv_apply] at this
        simpa [Perm.mul_apply] using this
      have hk' : rowWord t ∘ ⇑(k : Perm (Fin N)) = rowWord t := by
        funext i
        have := congrFun h1 i
        simp only [Function.comp_apply, Perm.mul_apply] at this
        have hh := congrFun (rowWord_comp_eq_of_mem t h) ((k : Perm (Fin N)) i)
        simp only [Function.comp_apply] at hh
        simp only [Function.comp_apply]
        rw [← hh]; exact this
      ext1
      exact eq_one_of_mem_columnGroup_of_rowWord t k.2 hk'
    rw [if_neg hne, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem uvec_ne_zero : uvec t ≠ 0 := fun h0 => by
  have := uvec_apply_rowWord t
  rw [h0] at this
  simp at this
  exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 this.symm)

theorem columnGroup_swap_eq_transpose :
    columnGroup (swapTableau t) = columnGroup (transposeTableau t) := by
  ext g; rw [mem_columnGroup_swapTableau, mem_columnGroup_transposeTableau_iff]

/-- `Θ u = κ_{tᵀ} (Θ v_C)`. -/
theorem Θ_uvec_eq_kappa :
    Θ t (uvec t) = kappa (transposeTableau t) (dT m) (Θ t (polytabloid t)) := by
  rw [uvec, map_sum, kappa_apply]
  refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun g => by
    rw [mem_columnGroup_swapTableau, mem_columnGroup_transposeTableau_iff]) _ _ fun h => ?_
  simp only [Equiv.subtypeEquivRight_apply]
  exact Θ_wordRep t _ _

theorem Θ_uvec_mem_span :
    Θ t (uvec t) ∈ Submodule.span ℂ {polytabloid (transposeTableau t)} := by
  rw [Θ_uvec_eq_kappa]
  exact kappa_mem_span_of_mem_contentSub _
    (spechtSub_le_contentSub _ (Θ_mem_specht t (polytabloid_mem_specht t)))

theorem Θ_uvec_ne_zero : Θ t (uvec t) ≠ 0 := by
  intro h0
  have hinj := (ΘS_bijective t).1
  have h1 : ΘS t ⟨uvec t, uvec_mem_specht t⟩ = 0 := Subtype.ext (by rw [ΘS_apply]; exact h0)
  have := hinj (h1.trans (map_zero _).symm)
  exact uvec_ne_zero t (congrArg Subtype.val this)

/-- `Θ u = c₁ • v_R'` with `c₁ ≠ 0` (replaces paper eq. (3.5)). -/
theorem exists_Θ_uvec :
    ∃ c : ℂ, c ≠ 0 ∧ Θ t (uvec t) = c • polytabloid (transposeTableau t) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (Θ_uvec_mem_span t)
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  rw [zero_smul] at hc
  exact Θ_uvec_ne_zero t hc.symm

/-- Paper eq. (3.4): `Σ_{h ∈ H_R} ε(h) h (v_R ⊗ v_C) = v_R ⊗ u`. -/
theorem symmetrize_pair :
    ∑ h : columnGroup (swapTableau t), ((Perm.sign (h : Perm (Fin N)) : ℤ) : ℂ) •
      wordRepL N (Fin (dR m) × Fin (dR m)) (h : Perm (Fin N))
        (pairLift (polytabloid (swapTableau t) ⊗ₜ[ℂ] polytabloid t)) =
      pairLift (polytabloid (swapTableau t) ⊗ₜ[ℂ] uvec t) := by
  rw [uvec, TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← pairLift_tprod, Representation.tprod_apply, TensorProduct.map_tmul]
  show _ • pairLift (wordRep N (dR m) (h : Perm (Fin N)) (polytabloid (swapTableau t)) ⊗ₜ[ℂ]
    wordRep N (dR m) (h : Perm (Fin N)) (polytabloid t)) = _
  rw [wordRep_polytabloid _ h.2, ← TensorProduct.smul_tmul', map_smul, smul_smul, sign_sq, one_smul]

end u

end OAI.Saxl
