import Mathlib
import Saxl.Prop32
import Saxl.ShapeInvariance
import Saxl.SubmoduleTheorem
import Saxl.MaschkeBridge

/-!
# From `W_m` to the tensor square

`W_m ⊆ pairLift (S^{t'} ⊗ S^t)` and `S^{t'} ≅ S^t` (same shape), so occurrence in `W_m` gives
occurrence in `S^ρ ⊗ S^ρ` for the canonical tableau — the form `TensorSquareCovers` needs.
-/

namespace OAI.Saxl

open Equiv Representation

open scoped TensorProduct

section equiv

variable {n : ℕ} {μ : YoungDiagram}

theorem id_ne_zero (t : Tableau n μ) : IntertwiningMap.id (spechtRep t) ≠ 0 := fun h => by
  have := congrArg (fun k : IntertwiningMap (spechtRep t) (spechtRep t) =>
    (k ⟨polytabloid t, polytabloid_mem_specht t⟩ : WordSpace n (μ.colLen 0))) h
  exact polytabloid_ne_zero t this

/-- Specht modules of the same shape are isomorphic. -/
noncomputable def spechtEquiv (t t' : Tableau n μ) : (spechtRep t).Equiv (spechtRep t') :=
  let h : Occurs t (spechtRep t') := occurs_of_occurs t' t ⟨IntertwiningMap.id _, id_ne_zero t'⟩
  (Classical.choose h).ofBijective
    ((IsIrreducible.bijective_or_eq_zero (Classical.choose h)).resolve_right
      (Classical.choose_spec h))

end equiv

section bridge

variable {m N : ℕ} (t : Tableau N (staircase m))

/-- `pairLift` on `S^{t'} ⊗ S^t`, as an intertwiner into the pair space. -/
noncomputable def tmulSub :
    IntertwiningMap ((spechtRep (swapTableau t)).tprod (spechtRep t)) (pairRepR m N) where
  toLinearMap := pairLift ∘ₗ TensorProduct.map (Specht (swapTableau t)).subtype (Specht t).subtype
  isIntertwining' g := by
    refine TensorProduct.ext' fun x y => ?_
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
      Submodule.subtype_apply]
    show pairLift ((wordRep N _ g (x : WordSpace N _)) ⊗ₜ (wordRep N _ g (y : WordSpace N _))) =
      pairRepR m N g (pairLift ((x : WordSpace N _) ⊗ₜ (y : WordSpace N _)))
    rw [← pairLift_tprod, Representation.tprod_apply, TensorProduct.map_tmul]
    rfl

theorem tmulSub_apply (x : Specht (swapTableau t)) (y : Specht t) :
    tmulSub t (x ⊗ₜ y) = pairLift ((x : WordSpace N _) ⊗ₜ (y : WordSpace N _)) := rfl

/-- `W_m ⊆ pairLift (S^{t'} ⊗ S^t)`. -/
theorem Wm_le_range : (Wm t).toSubmodule ≤ (tmulSub t).range.toSubmodule := by
  have hgen : wm t ∈ (tmulSub t).range :=
    ⟨⟨polytabloid (swapTableau t), polytabloid_mem_specht _⟩ ⊗ₜ ⟨polytabloid t, polytabloid_mem_specht _⟩, rfl⟩
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, rfl⟩
  exact (tmulSub t).range.apply_mem_toSubmodule g hgen

/-- Transport along the isomorphism of the first factor. -/
noncomputable def swapFactor :
    IntertwiningMap ((spechtRep (swapTableau t)).tprod (spechtRep t))
      ((spechtRep t).tprod (spechtRep t)) where
  toLinearMap := TensorProduct.map (spechtEquiv (swapTableau t) t).toLinearMap LinearMap.id
  isIntertwining' g := by
    refine TensorProduct.ext' fun x y => ?_
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul,
      LinearMap.id_apply]
    rw [IntertwiningMap.toLinearMap_apply, IntertwiningMap.isIntertwining _ _ _ g x]
    rfl

theorem swapFactor_injective : Function.Injective (swapFactor t) := by
  let e := (spechtEquiv (swapTableau t) t).toLinearEquiv
  have hL : (TensorProduct.map e.symm.toLinearMap LinearMap.id) ∘ₗ (swapFactor t).toLinearMap =
      LinearMap.id := by
    refine TensorProduct.ext' fun x y => ?_
    simp only [LinearMap.comp_apply, swapFactor, TensorProduct.map_tmul, LinearMap.id_apply]
    congr 1
    exact e.symm_apply_apply x
  intro a b hab
  have := congrArg (TensorProduct.map e.symm.toLinearMap LinearMap.id)
    (show (swapFactor t).toLinearMap a = (swapFactor t).toLinearMap b from hab)
  rwa [← LinearMap.comp_apply, hL, ← LinearMap.comp_apply, hL, LinearMap.id_apply,
    LinearMap.id_apply] at this

set_option maxHeartbeats 2000000 in
/-- **Bridge**: occurrence in `W_m` gives occurrence in `S^ρ ⊗ S^ρ`. -/
theorem occurs_tprod_of_occurs_Wm {lam : YoungDiagram} (tl : Tableau N lam)
    (h : Occurs tl (Wm t).toRepresentation) : Occurs tl ((spechtRep t).tprod (spechtRep t)) := by
  have h1 : Occurs tl (tmulSub t).range.toRepresentation := occurs_of_le tl (Wm_le_range t) h
  have h2 : Occurs tl ((spechtRep (swapTableau t)).tprod (spechtRep t)) :=
    Occurs.of_surjective (V := TensorProduct ℂ (Specht (swapTableau t)) (Specht t))
      (W := (tmulSub t).range.toSubmodule) tl
      (corestrict (V := TensorProduct ℂ (Specht (swapTableau t)) (Specht t)) (tmulSub t))
      (StripTableau.corestrict_surjective (V := TensorProduct ℂ (Specht (swapTableau t)) (Specht t)) _) h1
  obtain ⟨f, hf⟩ := h2
  refine ⟨(swapFactor t).comp f, fun h0 => hf ?_⟩
  refine DFunLike.ext f 0 fun x => ?_
  have h3 : ((swapFactor t).comp f) x = 0 := by rw [h0]; rfl
  rw [IntertwiningMap.comp_apply] at h3
  exact swapFactor_injective t (h3.trans (map_zero _).symm)

end bridge

/-- `TensorSquareCovers m` follows once every `S^λ` (`λ ⊢ N_m`) occurs in `W_m` for the canonical
tableau. -/
theorem tensorSquareCovers_of_Wm (m : ℕ)
    (h : ∀ (μ : YoungDiagram) (hμ : μ.card = (staircase m).card),
      Occurs (canonicalTableau μ hμ) (Wm (canonicalTableau (staircase m) rfl)).toRepresentation) :
    TensorSquareCovers m := fun μ hμ =>
  occurs_tprod_of_occurs_Wm (canonicalTableau (staircase m) rfl) (canonicalTableau μ hμ) (h μ hμ)

end OAI.Saxl
