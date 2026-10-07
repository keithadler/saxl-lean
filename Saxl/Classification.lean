import Mathlib
import Saxl.ClassDiagram
import Saxl.SpechtDistinct

/-!
# Every irreducible representation of `S_n` contains a Specht module

Characters of pairwise non-isomorphic irreducible representations are linearly independent class
functions (orthogonality), and the space of class functions has dimension the number of conjugacy
classes.  The Specht modules `S^η`, `η ⊢ n`, are pairwise non-isomorphic (`eq_of_specht_equiv`) and
there are at least as many of them as conjugacy classes (`classDiagram_injective`).  So an
irreducible representation not isomorphic to any `S^η` would give one class function too many.
Hence every irreducible representation of `S_n` is (isomorphic to, and in particular contains) a
Specht module.
-/

namespace OAI.Saxl

open Equiv Representation

variable {n : ℕ}

/-- An isomorphism `S^μ ≅ ρ` gives an occurrence. -/
theorem occurs_of_equiv {μ : YoungDiagram} (t : Tableau n μ) {V : Type*} [AddCommMonoid V]
    [Module ℂ V] {ρ : Representation ℂ (Perm (Fin n)) V} (φ : (spechtRep t).Equiv ρ) :
    Occurs t ρ := by
  refine ⟨φ.toIntertwiningMap, fun h0 => ?_⟩
  have : φ.toIntertwiningMap ⟨polytabloid t, polytabloid_mem_specht t⟩ = 0 := by rw [h0]; rfl
  have h2 : (⟨polytabloid t, polytabloid_mem_specht t⟩ : Specht t) = 0 :=
    φ.toLinearEquiv.injective (by rw [Representation.Equiv.toLinearEquiv_apply, this, map_zero])
  exact polytabloid_ne_zero t (congrArg Subtype.val h2)

/-- The character of a representation, as a function on conjugacy classes. -/
noncomputable def classFun {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Perm (Fin n)) V) : ConjClasses (Perm (Fin n)) → ℂ :=
  Quotient.lift ρ.character fun a b (h : IsConj a b) => by
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    rw [← hc, char_conj]

theorem classFun_comp_mk {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Perm (Fin n)) V) : classFun ρ ∘ ConjClasses.mk = ρ.character := rfl

/-- `if p then 1 else 0` only depends on the truth value of `p`. -/
theorem ite_one_zero_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    (if p then (1 : ℂ) else 0) = if q then 1 else 0 := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (h.1 hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.2 hq))]

/-- **Every irreducible representation of `S_n` contains a Specht module.** -/
theorem exists_specht_occurs {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Perm (Fin n)) V) [ρ.IsIrreducible] :
    ∃ (η : YoungDiagram) (hη : η.card = n), Occurs (canonicalTableau η hη) ρ := by
  classical
  by_contra hno
  push Not at hno
  letI : Fintype (ConjClasses (Perm (Fin n))) := Fintype.ofFinite _
  letI : Invertible (Nat.card (Perm (Fin n)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  -- the candidate family of characters: `ρ` and all Specht modules
  let χ : Option (ConjClasses (Perm (Fin n))) → (Perm (Fin n) → ℂ) := fun i =>
    match i with
    | none => ρ.character
    | some c => (spechtRep (canonicalTableau (classDiagram c) (card_classDiagram c))).character
  let ψ : Option (ConjClasses (Perm (Fin n))) → (ConjClasses (Perm (Fin n)) → ℂ) := fun i =>
    match i with
    | none => classFun ρ
    | some c => classFun (spechtRep (canonicalTableau (classDiagram c) (card_classDiagram c)))
  have hψχ : ∀ i, ψ i ∘ ConjClasses.mk = χ i := by rintro (_ | c) <;> rfl
  -- orthogonality
  have horth : ∀ i j, (Nat.card (Perm (Fin n)) : ℂ)⁻¹ * ∑ g, χ i g * χ j g⁻¹ =
      if i = j then 1 else 0 := by
    rintro (_ | c) (_ | c')
    · show (Nat.card (Perm (Fin n)) : ℂ)⁻¹ * ∑ g, ρ.character g * ρ.character g⁻¹ = _
      rw [char_orthonormal]
      exact ite_one_zero_congr ⟨fun _ => rfl, fun _ => ⟨Representation.Equiv.refl ρ⟩⟩
    · show (Nat.card (Perm (Fin n)) : ℂ)⁻¹ * ∑ g, ρ.character g *
          (spechtRep (canonicalTableau (classDiagram c') (card_classDiagram c'))).character g⁻¹ = _
      rw [char_orthonormal]
      refine ite_one_zero_congr ⟨fun ⟨φ⟩ => absurd (occurs_of_equiv _ φ) (hno _ _), fun h => ?_⟩
      exact absurd h (by simp)
    · show (Nat.card (Perm (Fin n)) : ℂ)⁻¹ * ∑ g,
          (spechtRep (canonicalTableau (classDiagram c) (card_classDiagram c))).character g *
            ρ.character g⁻¹ = _
      rw [char_orthonormal]
      refine ite_one_zero_congr ⟨fun ⟨φ⟩ => absurd (occurs_of_equiv _ φ.symm) (hno _ _), fun h => ?_⟩
      exact absurd h (by simp)
    · show (Nat.card (Perm (Fin n)) : ℂ)⁻¹ * ∑ g,
          (spechtRep (canonicalTableau (classDiagram c) (card_classDiagram c))).character g *
            (spechtRep (canonicalTableau (classDiagram c') (card_classDiagram c'))).character g⁻¹ = _
      rw [char_orthonormal]
      refine ite_one_zero_congr ⟨fun ⟨φ⟩ => ?_, fun h => ?_⟩
      · have := eq_of_specht_equiv _ _ φ
        rw [classDiagram_injective this]
      · rw [Option.some_inj] at h
        subst h
        exact ⟨Representation.Equiv.refl _⟩
  -- linear independence of the class functions
  have hli : LinearIndependent ℂ ψ := by
    rw [linearIndependent_iff']
    intro s g hsum j hj
    have hsum' : ∑ i ∈ s, g i • χ i = 0 := by
      have := congrArg (LinearMap.funLeft ℂ ℂ (ConjClasses.mk : Perm (Fin n) → _)) hsum
      rw [map_sum, map_zero] at this
      have hL : ∀ i, LinearMap.funLeft ℂ ℂ (ConjClasses.mk : Perm (Fin n) → _) (ψ i) = χ i :=
        fun i => hψχ i
      simpa only [map_smul, hL] using this
    have h0 : (Nat.card (Perm (Fin n)) : ℂ)⁻¹ * ∑ x, (∑ i ∈ s, g i • χ i) x * χ j x⁻¹ = 0 := by
      rw [hsum']
      simp
    have h1 : (Nat.card (Perm (Fin n)) : ℂ)⁻¹ * ∑ x, (∑ i ∈ s, g i • χ i) x * χ j x⁻¹ = g j := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [Finset.mul_sum]
      simp_rw [mul_left_comm ((Nat.card (Perm (Fin n)) : ℂ)⁻¹), horth]
      simp [Finset.sum_ite_eq', hj]
    rw [h0] at h1
    exact h1.symm
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_option] at hcard
  omega

end OAI.Saxl
