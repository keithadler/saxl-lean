import Mathlib
import Saxl.TwistPair
import Saxl.LetterInj
import Saxl.YoungOccurs
import Saxl.SignTwistOccurs

/-!
# Prop 3.2: the dominance base case

For `λ ⊴ ρ_m` with `|λ| = N_m`, `S^λ` occurs in `W_m = ℂ[G] (v_R ⊗ v_C)`.
Chain: Young's rule (occurrence form) gives `S^{λᵗ}` in `M^α = ℂ[G] e_{c₀}`; `Q : Z_m ↠ M^α`
(eq. 3.10); `Z_m ⊆ (id ⊗ Θ)(W_m ⊗ ε)` (eqs. 3.4–3.7, without multiplicity one); hence `S^{λᵗ}`
occurs in `W_m ⊗ ε`, i.e. `S^λ` occurs in `W_m`.
-/

namespace OAI.Saxl

open Equiv YoungDiagram Finset Representation

attribute [local instance] Fintype.ofFinite

open scoped TensorProduct

/-- Occurrence passes to a larger subrepresentation of the same ambient representation. -/
theorem occurs_of_le {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) {V : Type*} [AddCommMonoid V]
    [Module ℂ V] {ρ : Representation ℂ (Perm (Fin n)) V} {W₁ W₂ : Subrepresentation ρ}
    (h : W₁ ≤ W₂) (hW : Occurs t W₁.toRepresentation) : Occurs t W₂.toRepresentation := by
  obtain ⟨f, hf⟩ := hW
  let I : IntertwiningMap W₁.toRepresentation W₂.toRepresentation :=
    { toLinearMap := Submodule.inclusion (h : W₁.toSubmodule ≤ W₂.toSubmodule)
      isIntertwining' := fun g => LinearMap.ext fun x => Subtype.ext rfl }
  refine ⟨I.comp f, fun h0 => hf ?_⟩
  refine DFunLike.ext f 0 fun x => ?_
  have h1 : (I.comp f) x = 0 := by rw [h0]; rfl
  exact Subtype.ext (congrArg Subtype.val h1)

section prop32

variable {m N : ℕ} (t : Tableau N (staircase m))

/-- Ambient representation of `W_m`. -/
abbrev pairRepR (m N : ℕ) := wordRepL N (Fin (dR m) × Fin (dR m))
/-- Ambient representation of `Z_m`. -/
abbrev pairRepT (m N : ℕ) := wordRepL N (Fin (dR m) × Fin (dT m))

/-- `w_m = v_R ⊗ v_C`. -/
noncomputable def wm : WordSpaceL N (Fin (dR m) × Fin (dR m)) :=
  pairLift (polytabloid (swapTableau t) ⊗ₜ[ℂ] polytabloid t)

/-- `W_m = ℂ[G] w_m`. -/
noncomputable def Wm : Subrepresentation (pairRepR m N) := cycG (pairRepR m N) (wm t)

/-- `z_m = v_R ⊗ v_R'`. -/
noncomputable def zm : WordSpaceL N (Fin (dR m) × Fin (dT m)) :=
  pairLift (polytabloid (swapTableau t) ⊗ₜ[ℂ] polytabloid (transposeTableau t))

/-- `Z_m = ℂ[G] z_m`. -/
noncomputable def Zm : Subrepresentation (pairRepT m N) := cycG (pairRepT m N) (zm t)

/-- `M^α = ℂ[G] e_{c₀}`. -/
noncomputable def Mα : Subrepresentation (wordRepL N (Fin (2 * m))) :=
  cycG (wordRepL N (Fin (2 * m))) (Pi.single (targetWord t) 1)

/-- `Q` as an intertwiner out of `Z_m`. -/
noncomputable def QI : IntertwiningMap (Zm t).toRepresentation (wordRepL N (Fin (2 * m))) where
  toLinearMap := (contentProj (content (targetWord t)) ∘ₗ letterPush qmap) ∘ₗ (Zm t).toSubmodule.subtype
  isIntertwining' g := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    show contentProj _ (letterPush qmap (pairRepT m N g (x : WordSpaceL N _))) =
      wordRep N (2 * m) g (contentProj _ (letterPush qmap (x : WordSpaceL N _)))
    rw [letterPush_wordRepL, contentProj_wordRep]
    rfl

theorem QI_apply (x : (Zm t).toSubmodule) :
    QI t x = contentProj (content (targetWord t)) (letterPush qmap (x : WordSpaceL N _)) := rfl

/-- `M^α ⊆ Q(Z_m)`. -/
theorem Mα_le_range : (Mα t).toSubmodule ≤ (QI t).range.toSubmodule := by
  have hc : (Fintype.card (columnGroup (swapTableau t)) : ℂ) * ((Perm.sign (revPerm t) : ℤ) : ℂ) ≠ 0 :=
    mul_ne_zero (card_ne_zero_ℂ t) (sign_ne_zero _)
  have hz : zm t ∈ Zm t := Submodule.subset_span ⟨1, by simp⟩
  have h1 : QI t ⟨zm t, hz⟩ = _ • Pi.single (targetWord t) 1 := Q_pair t
  have hgen : (Pi.single (targetWord t) 1 : WordSpace N (2 * m)) ∈ (QI t).range := by
    have : (Pi.single (targetWord t) 1 : WordSpace N (2 * m)) =
        ((Fintype.card (columnGroup (swapTableau t)) : ℂ) * ((Perm.sign (revPerm t) : ℤ) : ℂ))⁻¹ •
          QI t ⟨zm t, hz⟩ := by
      rw [h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ ⟨_, rfl⟩
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, rfl⟩
  exact (QI t).range.apply_mem_toSubmodule g hgen

/-- Step A: `S^τ` in `M^α` ⇒ `S^τ` in `Z_m`. -/
theorem occurs_Zm_of_occurs_Mα {μ : YoungDiagram} (τ : Tableau N μ)
    (h : Occurs τ (Mα t).toRepresentation) : Occurs τ (Zm t).toRepresentation :=
  Occurs.of_surjective _ (corestrict (QI t)) (corestrict_surjective _)
    (occurs_of_le τ (Mα_le_range t) h)

/-- `id ⊗ Θ` restricted to `W_m ⊗ ε`, as an honest intertwiner. -/
noncomputable def idΘW : IntertwiningMap (signTwist (Wm t).toRepresentation) (pairRepT m N) where
  toLinearMap := idΘ t ∘ₗ (Wm t).toSubmodule.subtype
  isIntertwining' g := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    show idΘ t (((Perm.sign g : ℤ) : ℂ) • pairRepR m N g (x : WordSpaceL N _)) =
      pairRepT m N g (idΘ t (x : WordSpaceL N _))
    rw [map_smul, idΘ_wordRep, smul_smul, sign_sq, one_smul]

theorem idΘW_apply (x : (Wm t).toSubmodule) : idΘW t x = idΘ t (x : WordSpaceL N _) := rfl

/-- `Z_m ⊆ (id ⊗ Θ)(W_m)`. -/
theorem Zm_le_range : (Zm t).toSubmodule ≤ (idΘW t).range.toSubmodule := by
  obtain ⟨c, hc, hΘu⟩ := exists_Θ_uvec t
  -- the symmetrised generator lies in `W_m`
  have hsym : (∑ h : columnGroup (swapTableau t), ((Perm.sign (h : Perm (Fin N)) : ℤ) : ℂ) •
      pairRepR m N (h : Perm (Fin N)) (wm t)) ∈ Wm t :=
    Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hz : zm t ∈ (idΘW t).range := by
    have : zm t = c⁻¹ • idΘW t ⟨_, hsym⟩ := by
      rw [idΘW_apply]
      show zm t = c⁻¹ • idΘ t (∑ h : columnGroup (swapTableau t), _ • pairRepR m N (h : Perm (Fin N)) (wm t))
      rw [wm, symmetrize_pair, idΘ_pairLift, hΘu, TensorProduct.tmul_smul, map_smul, smul_smul,
        inv_mul_cancel₀ hc, one_smul]
      rfl
    rw [this]
    exact Submodule.smul_mem _ _ ⟨_, rfl⟩
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, rfl⟩
  exact (idΘW t).range.apply_mem_toSubmodule g hz

/-- Step B: `S^τ` in `Z_m` ⇒ `S^τ` in `W_m ⊗ ε`. -/
theorem occurs_twist_Wm_of_occurs_Zm {μ : YoungDiagram} (τ : Tableau N μ)
    (h : Occurs τ (Zm t).toRepresentation) : Occurs τ (signTwist (Wm t).toRepresentation) :=
  Occurs.of_surjective _ (corestrict (idΘW t)) (corestrict_surjective _)
    (occurs_of_le τ (Zm_le_range t) h)

end prop32

end OAI.Saxl
