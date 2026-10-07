import Mathlib
import Saxl.WordSectors

/-!
# Word sectors for a letter predicate

`WordSectors.lean` projects onto words whose positions carrying one fixed letter `ℓ₀` form a given
set.  Here the same for a decidable predicate `P` on letters (for the width-`s` band: "both entries
`< s`").
-/

namespace OAI.Saxl

open Equiv

section sectorsP

variable {n : ℕ} {L : Type} [Fintype L] [DecidableEq L] (P : L → Prop) [DecidablePred P]

/-- Positions of a word whose letter satisfies `P`. -/
def letterSetP (u : Fin n → L) : Finset (Fin n) := Finset.univ.filter fun p => P (u p)

theorem mem_letterSetP (u : Fin n → L) (p : Fin n) : p ∈ letterSetP P u ↔ P (u p) := by
  simp [letterSetP]

theorem letterSetP_comp (u : Fin n → L) (g : Perm (Fin n)) :
    letterSetP P (u ∘ g) = (letterSetP P u).map g⁻¹.toEmbedding := by
  ext p
  rw [mem_letterSetP, Finset.mem_map]
  constructor
  · intro h; exact ⟨g p, (mem_letterSetP P u _).2 h, by simp [Perm.inv_def]⟩
  · rintro ⟨q, hq, rfl⟩
    show P (u (g (g⁻¹ q)))
    rw [Perm.inv_def, Equiv.apply_symm_apply]
    exact (mem_letterSetP P u q).1 hq

variable (b : ℕ)

/-- The sector projection onto words whose `P`-positions are exactly `A`. -/
def sectorProjP (A : Subsets n b) : WordSpaceL n L →ₗ[ℂ] WordSpaceL n L where
  toFun f u := if letterSetP P u = A.1 then f u else 0
  map_add' f g := by
    funext u; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c f := by
    funext u; simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; split_ifs <;> simp

theorem sectorProjP_apply (A : Subsets n b) (f : WordSpaceL n L) (u : Fin n → L) :
    sectorProjP P b A f u = if letterSetP P u = A.1 then f u else 0 := rfl

theorem sectorProjP_disj (A B : Subsets n b) (hAB : A ≠ B) :
    sectorProjP P b A ∘ₗ sectorProjP P b B = 0 := by
  refine LinearMap.ext fun f => funext fun u => ?_
  simp only [LinearMap.comp_apply, sectorProjP_apply, LinearMap.zero_apply, Pi.zero_apply]
  split_ifs with h1 h2
  · exact absurd (Subtype.ext (h1.symm.trans h2)) hAB
  · rfl
  · rfl

theorem sectorProjP_equiv (g : Perm (Fin n)) (A : Subsets n b) :
    wordRepL n L g ∘ₗ sectorProjP P b A = sectorProjP P b (g • A) ∘ₗ wordRepL n L g := by
  refine LinearMap.ext fun f => funext fun u => ?_
  simp only [LinearMap.comp_apply, wordRepL_apply, sectorProjP_apply, letterSetP_comp,
    smul_subsets_val]
  have : (letterSetP P u).map g⁻¹.toEmbedding = A.1 ↔ letterSetP P u = A.1.map g.toEmbedding := by
    constructor
    · intro h; rw [← h, Finset.map_map]; ext p; simp [Perm.inv_def]
    · intro h; rw [h, Finset.map_map]; ext p; simp [Perm.inv_def]
  by_cases h1 : (letterSetP P u).map g⁻¹.toEmbedding = A.1
  · rw [if_pos h1, if_pos (this.1 h1)]
  · rw [if_neg h1, if_neg (fun h => h1 (this.2 h))]

theorem sectorProjP_of_support (A : Subsets n b) (f : WordSpaceL n L)
    (hf : ∀ u, f u ≠ 0 → letterSetP P u = A.1) : sectorProjP P b A f = f := by
  funext u
  rw [sectorProjP_apply]
  by_cases h : f u = 0
  · rw [h]; split_ifs <;> rfl
  · rw [if_pos (hf u h)]

end sectorsP

end OAI.Saxl
