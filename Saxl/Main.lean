import Mathlib
import Saxl.Statement

/-!
# Top-level reduction

`Occurs t σ` says the Specht module `S^μ` (for the tableau `t`) admits a nonzero intertwiner into
`σ`; over `ℂ` this is "`S^μ` is a constituent of `σ`".  The challenge's `kronecker a b t` is the
dimension of the intertwiner space, so `Occurs` gives positivity.  `SaxlConjecture` is reduced to
`TensorSquareCovers m` for every `m ≥ 1`, which is the paper's Theorem 1.1 in intertwiner form.
-/

namespace OAI.Saxl

open Representation

universe uV

variable {n : ℕ}

/-- `S^μ` occurs in `σ` (a nonzero intertwiner exists). -/
def Occurs {μ : YoungDiagram} (t : Tableau n μ) {V : Type uV} [AddCommMonoid V] [Module ℂ V]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) V) : Prop :=
  ∃ f : IntertwiningMap (spechtRep t) σ, f ≠ 0

/-- The inclusion of a subrepresentation, as an intertwiner. -/
def inclusion {G : Type*} {V : Type uV} [Group G] [AddCommMonoid V] [Module ℂ V]
    {ρ : Representation ℂ G V} (W : Subrepresentation ρ) :
    IntertwiningMap W.toRepresentation ρ where
  toLinearMap := W.toSubmodule.subtype
  isIntertwining' g := by ext; rfl

theorem inclusion_injective {G : Type*} {V : Type uV} [Group G] [AddCommMonoid V]
    [Module ℂ V] {ρ : Representation ℂ G V} (W : Subrepresentation ρ) :
    Function.Injective (inclusion W) :=
  Subtype.val_injective

/-- Occurrence passes from a subrepresentation to the ambient one. -/
theorem Occurs.mono {μ : YoungDiagram} (t : Tableau n μ) {V : Type uV} [AddCommMonoid V]
    [Module ℂ V] {ρ : Representation ℂ (Equiv.Perm (Fin n)) V} (W : Subrepresentation ρ)
    (h : Occurs t W.toRepresentation) : Occurs t ρ := by
  obtain ⟨f, hf⟩ := h
  refine ⟨(inclusion W).comp f, fun h0 => hf ?_⟩
  refine DFunLike.ext f 0 fun v => ?_
  have h1 : ((inclusion W).comp f) v = 0 := by rw [h0]; rfl
  rw [IntertwiningMap.comp_apply] at h1
  exact inclusion_injective W (h1.trans (map_zero _).symm)

/-- Generic form, stated where every instance is canonical: a nonzero intertwiner between
finite-dimensional representations gives a positive-dimensional intertwiner space. -/
theorem finrank_intertwiner_pos {G : Type*} [Group G] {V W : Type*} [AddCommGroup V]
    [AddCommGroup W] [Module ℂ V] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (f : IntertwiningMap ρ σ)
    (hf : f ≠ 0) : 0 < Module.finrank ℂ (IntertwiningMap ρ σ) :=
  Module.finrank_pos_iff_exists_ne_zero.2 ⟨f, hf⟩

/-- Bridge to the challenge's `kronecker`: a nonzero intertwiner gives positive multiplicity.
The explicit `V`/`W` force the canonical instance paths; the instance paths baked into `tprod`
are definitionally equal, which `exact` checks. -/
theorem kronecker_pos_of_occurs {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ)
    (h : Occurs t ((spechtRep a).tprod (spechtRep b))) : 0 < kronecker a b t := by
  obtain ⟨f, hf⟩ := h
  unfold kronecker
  exact finrank_intertwiner_pos (V := Specht t) (W := TensorProduct ℂ (Specht a) (Specht b))
    (spechtRep t) ((spechtRep a).tprod (spechtRep b)) f hf

/-- Paper Theorem 1.1 in intertwiner form: every `S^μ`, `μ ⊢ N_m`, occurs in `S^ρ ⊗ S^ρ`. -/
def TensorSquareCovers (m : ℕ) : Prop :=
  ∀ (μ : YoungDiagram) (hμ : μ.card = (staircase m).card),
    Occurs (canonicalTableau μ hμ)
      ((spechtRep (canonicalTableau (staircase m) rfl)).tprod
        (spechtRep (canonicalTableau (staircase m) rfl)))

/-- `SaxlConjecture` follows from `TensorSquareCovers` at every `m ≥ 1`. -/
theorem saxlConjecture_of_covers (h : ∀ m, 1 ≤ m → TensorSquareCovers m) : SaxlConjecture :=
  fun m hm μ hμ => kronecker_pos_of_occurs _ _ _ (h m hm μ hμ)

end OAI.Saxl
