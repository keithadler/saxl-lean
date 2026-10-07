import Mathlib
import Saxl.SignTwist
import Saxl.MaschkeBridge

/-!
# The sign twist, part B: transfer of occurrence

`V ⊗ ε` has the same subrepresentations as `V`, so irreducibility transfers and
`ΘS : S^λ ⊗ ε → S^{λᵗ}` is bijective (Schur both ways).  Hence
`Occurs tᵗ (V ⊗ ε) ↔ Occurs t V`.
-/

namespace OAI.Saxl

open Equiv Representation

variable {n : ℕ}

theorem sign_ne_zero (g : Perm (Fin n)) : ((Perm.sign g : ℤ) : ℂ) ≠ 0 := by
  rcases Int.units_eq_one_or (Perm.sign g) with h | h <;> simp [h]

section twist

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Perm (Fin n)) V)

/-- Subrepresentations of `V ⊗ ε` are those of `V`. -/
def signTwistSubrepIso : Subrepresentation (signTwist ρ) ≃o Subrepresentation ρ where
  toFun W := ⟨W.toSubmodule, fun g v hv => by
    have h := W.apply_mem_toSubmodule g hv
    rw [signTwist_apply] at h
    have := W.toSubmodule.smul_mem ((Perm.sign g : ℤ) : ℂ) h
    rwa [smul_smul, sign_sq, one_smul] at this⟩
  invFun W := ⟨W.toSubmodule, fun g v hv => by
    rw [signTwist_apply]; exact W.toSubmodule.smul_mem _ (W.apply_mem_toSubmodule g hv)⟩
  left_inv W := Subrepresentation.toSubmodule_injective rfl
  right_inv W := Subrepresentation.toSubmodule_injective rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_signTwist [h : IsIrreducible ρ] : IsIrreducible (signTwist ρ) :=
  (OrderIso.isSimpleOrder_iff (signTwistSubrepIso ρ)).2 h

variable {ρ} {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (Perm (Fin n)) W}

/-- An intertwiner between sign twists is an intertwiner. -/
def untwist (f : IntertwiningMap (signTwist ρ) (signTwist σ)) : IntertwiningMap ρ σ where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    refine LinearMap.ext fun v => ?_
    have h := IntertwiningMap.isIntertwining _ _ f g v
    simp only [signTwist_apply, map_smul] at h
    exact smul_right_injective W (sign_ne_zero g) h

theorem untwist_apply (f : IntertwiningMap (signTwist ρ) (signTwist σ)) (v : V) :
    untwist f v = f v := rfl

/-- An intertwiner induces one between the sign twists. -/
def twist (f : IntertwiningMap ρ σ) : IntertwiningMap (signTwist ρ) (signTwist σ) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, signTwist_apply, map_smul,
      IntertwiningMap.toLinearMap_apply, IntertwiningMap.isIntertwining _ _ f g v]

theorem twist_apply (f : IntertwiningMap ρ σ) (v : V) : twist f v = f v := rfl

end twist

variable {μ : YoungDiagram} (t : Tableau n μ)

theorem ΘS_bijective : Function.Bijective (ΘS t) := by
  haveI := isIrreducible_signTwist (spechtRep t)
  exact ⟨(IsIrreducible.injective_or_eq_zero (ΘS t)).resolve_right (ΘS_ne_zero t),
    (IsIrreducible.surjective_or_eq_zero (ΘS t)).resolve_right (ΘS_ne_zero t)⟩

/-- `S^{λᵗ}` occurs in `V ⊗ ε` ⇒ `S^λ` occurs in `V`. -/
theorem occurs_of_occurs_transpose {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Perm (Fin n)) V} (h : Occurs (transposeTableau t) (signTwist ρ)) :
    Occurs t ρ := by
  obtain ⟨f, hf⟩ := h
  refine ⟨untwist (f.comp (ΘS t)), fun h0 => hf ?_⟩
  refine DFunLike.ext f 0 fun y => ?_
  obtain ⟨x, rfl⟩ := (ΘS_bijective t).2 y
  have := congrArg (fun k : IntertwiningMap (spechtRep t) ρ => k x) h0
  exact this

/-- `S^λ` occurs in `V` ⇒ `S^{λᵗ}` occurs in `V ⊗ ε`. -/
theorem occurs_transpose_of_occurs {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Perm (Fin n)) V} (h : Occurs t ρ) :
    Occurs (transposeTableau t) (signTwist ρ) := by
  obtain ⟨f, hf⟩ := h
  let e := (ΘS t).ofBijective (ΘS_bijective t)
  refine ⟨(twist f).comp e.symm.toIntertwiningMap, fun h0 => hf ?_⟩
  refine DFunLike.ext f 0 fun x => ?_
  have := congrArg (fun k : IntertwiningMap (spechtRep (transposeTableau t)) (signTwist ρ) =>
    k (ΘS t x)) h0
  simp only [IntertwiningMap.comp_apply] at this
  have h2 : e.symm.toIntertwiningMap (ΘS t x) = x := by
    show e.toLinearEquiv.symm (e.toLinearEquiv x) = x
    exact e.toLinearEquiv.symm_apply_apply x
  rw [h2] at this
  exact this

end OAI.Saxl
