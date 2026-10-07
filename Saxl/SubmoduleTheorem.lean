import Mathlib
import Saxl.Statement
import Saxl.Polytabloid
import Saxl.Content
import Saxl.Antisymmetrizer
import Saxl.ColumnLemma
import Saxl.MaschkeBridge

/-!
# James's submodule theorem and irreducibility of Specht modules

For `u` of content `λ`, `κ_t u ∈ ℂ e_t`.  Hence for a subrepresentation `U ≤ M^λ` of the word
space, either `S^λ ≤ U` or `U ⊥ S^λ`.  Positive-definiteness of `form` then gives
`IsIrreducible (spechtRep t)`.
-/

namespace OAI.Saxl

open Equiv

attribute [local instance] Fintype.ofFinite

variable {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)

local notation "d" => μ.colLen 0

/-- `κ_t e_w` is a multiple of `e_t` for every word `w` of content `λ`. -/
theorem kappa_single_mem_span {w : Fin n → Fin d} (hc : content w = content (rowWord t)) :
    kappa t d (Pi.single w 1) ∈ Submodule.span ℂ {polytabloid t} := by
  by_cases hd : ColumnDistinct t w
  · obtain ⟨π, hπ, rfl⟩ := exists_columnPerm hc hd
    rw [← wordRep_single, kappa_wordRep t hπ, kappa_single_rowWord]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · unfold ColumnDistinct at hd
    push Not at hd
    obtain ⟨i, j, hcol, hw, hij⟩ := hd
    rw [kappa_single_eq_zero t hij hcol hw]
    exact Submodule.zero_mem _

/-- Decomposition of a word-space vector into basis words. -/
theorem eq_sum_single (u : WordSpace n d) : u = ∑ w, u w • (Pi.single w 1 : WordSpace n d) := by
  ext a
  rw [Finset.sum_apply, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `κ_t u ∈ ℂ e_t` for `u ∈ M^λ`. -/
theorem kappa_mem_span_of_mem_contentSub {u : WordSpace n d}
    (hu : u ∈ contentSub (content (rowWord t))) :
    kappa t d u ∈ Submodule.span ℂ {polytabloid t} := by
  rw [eq_sum_single u, map_sum]
  refine Submodule.sum_mem _ fun w _ => ?_
  rw [map_smul]
  by_cases hw : content w = content (rowWord t)
  · exact Submodule.smul_mem _ _ (kappa_single_mem_span t hw)
  · rw [(mem_contentSub.1 hu) w hw, zero_smul]
    exact Submodule.zero_mem _

/-- `κ_t` preserves every subrepresentation. -/
theorem kappa_mem {U : Subrepresentation (wordRep n d)} {u : WordSpace n d} (hu : u ∈ U) :
    kappa t d u ∈ U := by
  rw [kappa_apply]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (U.apply_mem_toSubmodule _ hu)

theorem form_wordRep_right (g : Perm (Fin n)) (u v : WordSpace n d) :
    form u (wordRep n d g v) = form (wordRep n d g⁻¹ u) v := by
  rw [form_wordRep_left, inv_inv]

/-- James's submodule theorem: a subrepresentation of `M^λ` contains `S^λ` or is orthogonal
to it. -/
theorem submodule_theorem (U : Subrepresentation (wordRep n d))
    (hU : ∀ u ∈ U, u ∈ contentSub (content (rowWord t))) :
    (spechtSub t).toSubmodule ≤ U.toSubmodule ∨
      ∀ u ∈ U, ∀ s ∈ Specht t, form u s = 0 := by
  by_cases h : ∃ u ∈ U, kappa t d u ≠ 0
  · left
    obtain ⟨u, hu, hκ⟩ := h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (kappa_mem_span_of_mem_contentSub t (hU u hu))
    have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc; exact hκ hc.symm
    have het : polytabloid t ∈ U := by
      have : c⁻¹ • kappa t d u ∈ U := Submodule.smul_mem _ _ (kappa_mem t hu)
      rwa [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    exact U.apply_mem_toSubmodule g het
  · right
    push Not at h
    intro u hu s hs
    have key : ∀ g : Perm (Fin n), form u (wordRep n d g (polytabloid t)) = 0 := fun g => by
      rw [form_wordRep_right, ← kappa_single_rowWord, ← form_kappa,
        h _ (U.apply_mem_toSubmodule g⁻¹ hu)]
      simp [form]
    refine Submodule.span_induction (p := fun s _ => form u s = 0) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨g, rfl⟩; exact key g
    · simp [form]
    · intro x y _ _ hx hy; rw [form_add_right, hx, hy, add_zero]
    · intro a x _ hx; rw [form_smul_right, hx, mul_zero]

/-- A subrepresentation of `spechtRep t`, pushed into the word space. -/
def liftSub (W : Subrepresentation (spechtRep t)) : Subrepresentation (wordRep n d) where
  toSubmodule := W.toSubmodule.map (Specht t).subtype
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_map] at hv ⊢
    obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨spechtRep t g x, W.apply_mem_toSubmodule g hx, rfl⟩

theorem mem_liftSub {W : Subrepresentation (spechtRep t)} {v : WordSpace n d} :
    v ∈ liftSub t W ↔ ∃ x ∈ W, (x : WordSpace n d) = v := by
  show v ∈ W.toSubmodule.map (Specht t).subtype ↔ _
  rw [Submodule.mem_map]
  rfl

/-- The Specht module is irreducible. -/
instance spechtRep_isIrreducible : Representation.IsIrreducible (spechtRep t) := by
  haveI : Nontrivial (Subrepresentation (spechtRep t)) := by
    refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
    have hx : (⟨polytabloid t, polytabloid_mem_specht t⟩ : Specht t) ∈ (⊤ : Subrepresentation (spechtRep t)) :=
      subrep_mem_top _
    rw [← h, subrep_mem_bot] at hx
    exact polytabloid_ne_zero t (congrArg Subtype.val hx)
  refine ⟨fun W => ?_⟩
  have hU : ∀ u ∈ liftSub t W, u ∈ contentSub (content (rowWord t)) := by
    intro u hu
    obtain ⟨x, _, rfl⟩ := (mem_liftSub t).1 hu
    exact spechtSub_le_contentSub t x.2
  rcases submodule_theorem t (liftSub t W) hU with h | h
  · right
    apply Subrepresentation.toSubmodule_injective
    rw [eq_top_iff]
    intro x _
    have : (x : WordSpace n d) ∈ liftSub t W := h x.2
    obtain ⟨y, hy, hyx⟩ := (mem_liftSub t).1 this
    rw [← Subtype.ext hyx]
    exact hy
  · left
    apply Subrepresentation.toSubmodule_injective
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : WordSpace n d) ∈ liftSub t W := (mem_liftSub t).2 ⟨x, hx, rfl⟩
    have := h _ hx' _ x.2
    have h0 := eq_zero_of_form_self_eq_zero this
    rw [Submodule.mem_bot]
    exact Subtype.ext h0

end OAI.Saxl
