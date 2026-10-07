import Mathlib

/-!
# Conjugacy classes of `S_n` embed into Young diagrams of size `n`

A permutation's cycle type, padded with fixed points, is a partition of `n`; sorting it gives the row
lengths of a Young diagram.  Conjugate permutations give the same diagram and conversely, so this
descends to an injection `ConjClasses (Perm (Fin n)) → YoungDiagram` landing in diagrams of size `n`.
This is the only counting input needed to show that the Specht modules exhaust the irreducible
representations of `S_n`.
-/

namespace OAI.Saxl

open Equiv

variable {n : ℕ}

/-- The row lengths of a permutation: its partition (cycle type padded with `1`s), sorted
decreasingly. -/
def permRowLens (σ : Perm (Fin n)) : List ℕ := σ.partition.parts.sort (· ≥ ·)

theorem permRowLens_sortedGE (σ : Perm (Fin n)) : (permRowLens σ).SortedGE :=
  (Multiset.pairwise_sort _ _).sortedGE

theorem permRowLens_pos (σ : Perm (Fin n)) : ∀ x ∈ permRowLens σ, 0 < x := fun _ hx =>
  σ.partition.parts_pos ((Multiset.mem_sort _).1 hx)

theorem permRowLens_eq_iff {σ τ : Perm (Fin n)} :
    permRowLens σ = permRowLens τ ↔ σ.partition = τ.partition := by
  rw [Nat.Partition.ext_iff]
  constructor
  · intro h
    have := congrArg (fun l : List ℕ => (l : Multiset ℕ)) h
    simpa only [permRowLens, Multiset.sort_eq] using this
  · intro h
    unfold permRowLens
    rw [h]

/-- The Young diagram of a permutation's cycle type. -/
def permDiagram (σ : Perm (Fin n)) : YoungDiagram :=
  YoungDiagram.ofRowLens _ (permRowLens_sortedGE σ)

theorem rowLens_permDiagram (σ : Perm (Fin n)) : (permDiagram σ).rowLens = permRowLens σ :=
  YoungDiagram.rowLens_ofRowLens_eq_self (permRowLens_pos σ)

/-- Row lengths determine a Young diagram. -/
theorem rowLens_injective : Function.Injective YoungDiagram.rowLens := fun _ _ h =>
  YoungDiagram.equivListRowLens.injective (Subtype.ext h)

theorem card_permDiagram (σ : Perm (Fin n)) : (permDiagram σ).card = n := by
  rw [← YoungDiagram.sum_rowLens_eq_card, rowLens_permDiagram, permRowLens, ← Multiset.sum_coe,
    Multiset.sort_eq, σ.partition.parts_sum, Fintype.card_fin]

theorem permDiagram_eq_iff {σ τ : Perm (Fin n)} : permDiagram σ = permDiagram τ ↔ IsConj σ τ := by
  rw [Perm.partition_eq_of_isConj, ← permRowLens_eq_iff, ← rowLens_permDiagram,
    ← rowLens_permDiagram]
  exact rowLens_injective.eq_iff.symm

/-- The Young diagram of a conjugacy class of `S_n`. -/
def classDiagram : ConjClasses (Perm (Fin n)) → YoungDiagram :=
  Quotient.lift permDiagram fun _ _ (h : IsConj _ _) => permDiagram_eq_iff.2 h

theorem classDiagram_mk (σ : Perm (Fin n)) : classDiagram (ConjClasses.mk σ) = permDiagram σ := rfl

theorem card_classDiagram (c : ConjClasses (Perm (Fin n))) : (classDiagram c).card = n := by
  obtain ⟨σ, rfl⟩ := ConjClasses.exists_rep c
  rw [classDiagram_mk, card_permDiagram]

theorem classDiagram_injective : Function.Injective (classDiagram (n := n)) := by
  intro c c' h
  obtain ⟨σ, rfl⟩ := ConjClasses.exists_rep c
  obtain ⟨τ, rfl⟩ := ConjClasses.exists_rep c'
  rw [classDiagram_mk, classDiagram_mk, permDiagram_eq_iff] at h
  exact ConjClasses.mk_eq_mk_iff_isConj.2 h

instance : Finite (ConjClasses (Perm (Fin n))) := Quotient.finite _

end OAI.Saxl
