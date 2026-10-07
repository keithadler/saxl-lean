import Mathlib
import Saxl.Main
import Saxl.Polytabloid

/-!
# Quotients of irreducibles are constituents

Over `ℂ` every representation of `S_n` is semisimple, so a nonzero intertwiner *onto* an
irreducible `S^μ` splits and `S^μ` occurs as a subrepresentation.  This is the "any irreducible
quotient is also a constituent" step used throughout the paper (§2.1).
-/

namespace OAI.Saxl

open Representation

variable {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)

theorem polytabloid_mem_specht : polytabloid t ∈ Specht t :=
  Submodule.subset_span ⟨1, by simp⟩

section lattice

variable {G : Type*} {V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

theorem subrep_mem_inf {ρ₁ ρ₂ : Subrepresentation ρ} {x : V} :
    x ∈ ρ₁ ⊓ ρ₂ ↔ x ∈ ρ₁ ∧ x ∈ ρ₂ := by
  rw [← SetLike.mem_coe, Subrepresentation.coe_inf]
  exact Set.mem_inter_iff _ _ _

theorem subrep_mem_bot {x : V} : x ∈ (⊥ : Subrepresentation ρ) ↔ x = 0 :=
  Submodule.mem_bot ℂ

theorem subrep_mem_top (x : V) : x ∈ (⊤ : Subrepresentation ρ) :=
  Submodule.mem_top

end lattice

theorem occurs_of_intertwiner_to [IsIrreducible (spechtRep t)] {V : Type*} [AddCommGroup V]
    [Module ℂ V] {σ : Representation ℂ (Equiv.Perm (Fin n)) V}
    (f : IntertwiningMap σ (spechtRep t)) (hf : f ≠ 0) : Occurs t σ := by
  have : NeZero (Nat.card (Equiv.Perm (Fin n)) : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨Q, hQ⟩ := exists_isCompl f.ker
  let g : IntertwiningMap Q.toRepresentation (spechtRep t) := f.comp (inclusion Q)
  have hg : ∀ x : Q.toSubmodule, g x = f x := fun _ => rfl
  have hinj : Function.Injective g := by
    intro x y hxy
    have h1 : ((x - y : Q.toSubmodule) : V) ∈ f.ker ⊓ Q := by
      rw [subrep_mem_inf]
      refine ⟨?_, (x - y).2⟩
      rw [IntertwiningMap.mem_ker, Submodule.coe_sub, map_sub, ← hg, ← hg, hxy, sub_self]
    rw [hQ.inf_eq_bot, subrep_mem_bot, Submodule.coe_sub, sub_eq_zero] at h1
    exact Subtype.ext h1
  have hg0 : g ≠ 0 := by
    intro h0
    apply hf
    have hle : Q ≤ f.ker := by
      intro x hx
      rw [IntertwiningMap.mem_ker, ← hg ⟨x, hx⟩, h0]
      rfl
    have hQbot : Q = ⊥ := by
      rw [← hQ.symm.inf_eq_bot, inf_eq_left.2 hle]
    have hker : f.ker = ⊤ := by
      rw [← hQ.sup_eq_top, hQbot, sup_bot_eq]
    refine DFunLike.ext f 0 fun v => ?_
    have := subrep_mem_top (ρ := σ) v
    rw [← hker, IntertwiningMap.mem_ker] at this
    exact this
  have hsurj : Function.Surjective g := by
    rcases IsIrreducible.surjective_or_eq_zero g with h | h
    · exact h
    · exact absurd h hg0
  let e := g.ofBijective ⟨hinj, hsurj⟩
  refine ⟨(inclusion Q).comp e.symm.toIntertwiningMap, fun h0 => ?_⟩
  let x : Specht t := ⟨polytabloid t, polytabloid_mem_specht t⟩
  have hx : x ≠ 0 := fun h => polytabloid_ne_zero t (congrArg Subtype.val h)
  have h1 : (((inclusion Q).comp e.symm.toIntertwiningMap) x : V) = 0 := by rw [h0]; rfl
  have h2 : (e.symm.toIntertwiningMap x : V) = 0 := h1
  have h3 : e.toLinearEquiv.symm x = 0 := Subtype.ext h2
  rw [LinearEquiv.map_eq_zero_iff] at h3
  exact hx h3

/-- Occurrence passes backwards along surjective intertwiners (the surjection splits). -/
theorem Occurs.of_surjective {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ (Equiv.Perm (Fin n)) V}
    {τ : Representation ℂ (Equiv.Perm (Fin n)) W} (π : IntertwiningMap σ τ)
    (hπ : Function.Surjective π) (h : Occurs t τ) : Occurs t σ := by
  have : NeZero (Nat.card (Equiv.Perm (Fin n)) : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨f, hf⟩ := h
  obtain ⟨Q, hQ⟩ := exists_isCompl π.ker
  let g : IntertwiningMap Q.toRepresentation τ := π.comp (inclusion Q)
  have hg : ∀ x : Q.toSubmodule, g x = π x := fun _ => rfl
  have hinj : Function.Injective g := by
    intro x y hxy
    have h1 : ((x - y : Q.toSubmodule) : V) ∈ π.ker ⊓ Q := by
      rw [subrep_mem_inf]
      refine ⟨?_, (x - y).2⟩
      rw [IntertwiningMap.mem_ker, Submodule.coe_sub, map_sub, ← hg, ← hg, hxy, sub_self]
    rw [hQ.inf_eq_bot, subrep_mem_bot, Submodule.coe_sub, sub_eq_zero] at h1
    exact Subtype.ext h1
  have hsurj : Function.Surjective g := by
    intro w
    obtain ⟨v, rfl⟩ := hπ w
    have hv : v ∈ π.ker ⊔ Q := by rw [hQ.sup_eq_top]; exact subrep_mem_top v
    rw [← SetLike.mem_coe, Subrepresentation.coe_sup] at hv
    obtain ⟨k, hk, q, hq, rfl⟩ := Set.mem_add.1 hv
    refine ⟨⟨q, hq⟩, ?_⟩
    show π q = π (k + q)
    rw [map_add, (IntertwiningMap.mem_ker _ _ π k).1 hk, zero_add]
  let e := g.ofBijective ⟨hinj, hsurj⟩
  refine ⟨(inclusion Q).comp (e.symm.toIntertwiningMap.comp f), fun h0 => hf ?_⟩
  refine DFunLike.ext f 0 fun x => ?_
  have h1 : (((inclusion Q).comp (e.symm.toIntertwiningMap.comp f)) x : V) = 0 := by rw [h0]; rfl
  have h2 : (e.symm.toIntertwiningMap (f x) : V) = 0 := h1
  have h3 : e.toLinearEquiv.symm (f x) = 0 := Subtype.ext h2
  rw [LinearEquiv.map_eq_zero_iff] at h3
  exact h3

end OAI.Saxl
