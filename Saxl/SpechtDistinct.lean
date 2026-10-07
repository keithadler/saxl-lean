import Mathlib
import Saxl.Main
import Saxl.SubmoduleTheorem
import Saxl.Prop32

/-!
# Specht modules of different shapes are not isomorphic

If `S^η` occurs in the permutation module `M^θ` then `η ⊵ θ` (James's basic combinatorial lemma:
a word of content `θ` with distinct letters in every column of an `η`-tableau forces `η ⊵ θ`).
Since `S^θ ≤ M^θ`, an isomorphism `S^η ≅ S^θ` gives dominance both ways, hence `η = θ`.
-/

namespace OAI.Saxl

open Equiv YoungDiagram Finset Representation

attribute [local instance] Fintype.ofFinite

variable {n : ℕ}

section dominance

variable {η θ : YoungDiagram} (t : Tableau n η) (s : Tableau n θ)

/-- Dominance is antisymmetric. -/
theorem Dominates.antisymm {a b : YoungDiagram} (h₁ : Dominates a b) (h₂ : Dominates b a) :
    a = b := by
  have hrow : ∀ i, a.rowLen i = b.rowLen i := by
    intro i
    have e1 := le_antisymm (h₁ (i + 1)) (h₂ (i + 1))
    have e2 := le_antisymm (h₁ i) (h₂ i)
    simp only [rowSum, sum_range_succ] at e1 e2
    omega
  ext ⟨i, j⟩
  simp only [mem_cells, mem_iff_lt_rowLen, hrow]

/-- A word of content `θ` with distinct letters in every column of the `η`-tableau `t` forces
`η ⊵ θ`. -/
theorem dominates_of_colDistinct {w : Fin n → Fin (θ.colLen 0)}
    (hc : content w = content (rowWord s))
    (hd : ∀ i j, (t i).val.2 = (t j).val.2 → w i = w j → i = j) : Dominates η θ := by
  classical
  intro k
  set A : Finset (Fin n) := Finset.univ.filter fun p => (w p : ℕ) < k with hA
  have h1 : A.card = rowSum θ k := by
    rw [rowSum, Finset.card_eq_sum_card_fiberwise (f := fun p => (w p : ℕ)) (t := Finset.range k)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      by_cases hi' : i < θ.colLen 0
      · rw [← content_rowWord s ⟨i, hi'⟩, ← hc]
        unfold content
        congr 1
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hA, Fin.ext_iff]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨by omega, h⟩
      · push Not at hi'
        rw [rowLen_eq_zero_of_le hi', Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro p _ hp
        have := (w p).2
        omega
    · intro p hp
      rw [Finset.mem_coe, hA, Finset.mem_filter] at hp
      rw [Finset.mem_coe, Finset.mem_range]
      exact hp.2
  have h2 : A.card ≤ rowSum η k := by
    set N := η.rowLen 0 with hN
    have hcolN : ∀ p : Fin n, (t p).val.2 < N := fun p => by
      have hm : ((t p).val.1, (t p).val.2) ∈ η := (t p).2
      rw [mem_iff_lt_rowLen] at hm
      exact lt_of_lt_of_le hm (η.rowLen_anti 0 _ (Nat.zero_le _))
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p => (t p).val.2) (t := Finset.range N)
      (fun p _ => Finset.mem_coe.2 (Finset.mem_range.2 (hcolN p)))]
    have hfib : ∀ j ∈ Finset.range N,
        (A.filter fun p => (t p).val.2 = j).card ≤ min (η.colLen j) k := by
      intro j _
      refine le_min ?_ ?_
      · calc _ ≤ (colPositions t j).card := Finset.card_le_card (fun p hp => by
              rw [mem_colPositions]; exact (Finset.mem_filter.1 hp).2)
          _ = _ := card_colPositions t j
      · rw [← Finset.card_range k]
        refine Finset.card_le_card_of_injOn (fun p => (w p : ℕ)) ?_ ?_
        · intro p hp
          rw [Finset.mem_coe, Finset.mem_filter, hA, Finset.mem_filter] at hp
          rw [Finset.mem_coe, Finset.mem_range]
          exact hp.1.2
        · intro p hp q hq hpq
          rw [Finset.mem_coe, Finset.mem_filter] at hp hq
          exact hd p q (hp.2.trans hq.2.symm) (Fin.ext hpq)
    calc _ ≤ ∑ j ∈ Finset.range N, min (η.colLen j) k := Finset.sum_le_sum hfib
      _ = rowSum η k := by
        have := sum_colLen_eq_sum_min η.transpose (N := N) (by rw [colLen_transpose]) k
        simp only [colLen_transpose, rowLen_transpose] at this
        rw [rowSum, this]
  omega

end dominance

section kappa

variable {η : YoungDiagram} (t : Tableau n η)

/-- `κ_t e_t = |C_t| e_t`. -/
theorem kappa_polytabloid :
    kappa t (η.colLen 0) (polytabloid t) = (Nat.card (columnGroup t) : ℂ) • polytabloid t := by
  conv_lhs => rw [polytabloid_eq_sum, map_sum]
  have : ∀ g : columnGroup t, kappa t (η.colLen 0)
      ((((Perm.sign (g : Perm (Fin n))) : ℤ) : ℂ) •
        Pi.single (rowWord t ∘ ((g : Perm (Fin n))⁻¹ : Perm (Fin n))) 1) = polytabloid t := fun g => by
    rw [map_smul, ← wordRep_single, kappa_wordRep t g.2, kappa_single_rowWord, smul_smul, sign_sq,
      one_smul]
  simp_rw [this]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, Nat.card_eq_fintype_card]

/-- An intertwiner out of `S^η` vanishing on `e_t` is zero. -/
theorem intertwiner_eq_zero_of_polytabloid {V : Type*} [AddCommMonoid V] [Module ℂ V]
    {σ : Representation ℂ (Perm (Fin n)) V} (f : IntertwiningMap (spechtRep t) σ)
    (h0 : f ⟨polytabloid t, polytabloid_mem_specht t⟩ = 0) : f = 0 := by
  refine DFunLike.ext f 0 fun v => ?_
  obtain ⟨v, hv⟩ := v
  show f ⟨v, hv⟩ = 0
  refine Submodule.span_induction (p := fun v hv => f ⟨v, hv⟩ = 0) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨g, rfl⟩
    have := IntertwiningMap.isIntertwining _ _ f g (⟨polytabloid t, polytabloid_mem_specht t⟩ : Specht t)
    rw [h0, map_zero] at this
    exact this
  · exact map_zero f
  · intro x y hx hy ihx ihy
    have : (⟨x + y, Submodule.add_mem _ hx hy⟩ : Specht t) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add, ihx, ihy, add_zero]
  · intro c x hx ihx
    have : (⟨c • x, Submodule.smul_mem _ c hx⟩ : Specht t) = c • ⟨x, hx⟩ := rfl
    rw [this, map_smul, ihx, smul_zero]

end kappa

section occurs

variable {η θ : YoungDiagram} (t : Tableau n η) (s : Tableau n θ)

/-- If `S^η` occurs in `M^θ` then `η ⊵ θ`. -/
theorem dominates_of_occurs_contentSub
    (h : Occurs t (contentSub (content (rowWord s))).toRepresentation) : Dominates η θ := by
  classical
  obtain ⟨f, hf⟩ := h
  obtain ⟨e, he⟩ : ∃ e : Specht t, e = ⟨polytabloid t, polytabloid_mem_specht t⟩ := ⟨_, rfl⟩
  have hgen : f e ≠ 0 := fun h0 => hf (intertwiner_eq_zero_of_polytabloid t f (by rw [← he]; exact h0))
  obtain ⟨u, hu⟩ : ∃ u : WordSpace n (θ.colLen 0), u = (f e : WordSpace n (θ.colLen 0)) :=
    ⟨_, rfl⟩
  have hu0 : u ≠ 0 := fun h0 => hgen (Subtype.ext (hu ▸ h0))
  have hum : u ∈ contentSub (content (rowWord s)) := hu ▸ (f e).2
  -- `κ_t u = |C_t| u`
  have key : kappa t (θ.colLen 0) u = (Nat.card (columnGroup t) : ℂ) • u := by
    have hcomm : ∀ g : columnGroup t, wordRep n (θ.colLen 0) g u =
        (f (spechtRep t g e) : WordSpace n (θ.colLen 0)) := fun g => by
      rw [hu, IntertwiningMap.isIntertwining _ _ f]; rfl
    have hval : ∀ g : columnGroup t, ((spechtRep t g e : Specht t) : WordSpace n (η.colLen 0)) =
        wordRep n (η.colLen 0) g (polytabloid t) := fun g => by rw [he]; rfl
    rw [kappa_apply]
    simp_rw [hcomm, ← Submodule.coe_smul]
    rw [← Submodule.coe_sum]
    simp_rw [← map_smul f]
    rw [← map_sum, hu, ← Submodule.coe_smul, ← map_smul f]
    congr 2
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_smul]
    simp only [Submodule.coe_smul]
    simp_rw [hval]
    rw [he]
    have h1 := kappa_polytabloid t
    rw [kappa_apply] at h1
    exact h1
  have hκu : kappa t (θ.colLen 0) u ≠ 0 := by
    rw [key]
    intro h0
    rcases smul_eq_zero.1 h0 with h | h
    · exact Nat.cast_ne_zero.2 Nat.card_pos.ne' h
    · exact hu0 h
  -- expand `u` in basis words
  rw [eq_sum_single (μ := θ) u, map_sum] at hκu
  obtain ⟨w, _, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hκu
  rw [map_smul] at hw
  have hw1 : u w ≠ 0 := fun h0 => hw (by rw [h0, zero_smul])
  have hw2 : kappa t (θ.colLen 0) (Pi.single w 1) ≠ 0 := fun h0 => hw (by rw [h0, smul_zero])
  have hc : content w = content (rowWord s) := by
    by_contra hne
    exact hw1 ((mem_contentSub.1 hum) w hne)
  refine dominates_of_colDistinct t s hc fun i j hcol hwij => ?_
  by_contra hij
  exact hw2 (kappa_single_eq_zero t hij hcol hwij)

/-- Isomorphic Specht modules have the same shape. -/
theorem eq_of_specht_equiv (φ : (spechtRep s).Equiv (spechtRep t)) : η = θ := by
  have h1 : Occurs t (contentSub (content (rowWord s))).toRepresentation := by
    refine occurs_of_le t (spechtSub_le_contentSub s) ⟨φ.symm.toIntertwiningMap, fun h0 => ?_⟩
    have : φ.symm.toIntertwiningMap ⟨polytabloid t, polytabloid_mem_specht t⟩ = 0 := by
      rw [h0]; rfl
    have h2 : (⟨polytabloid t, polytabloid_mem_specht t⟩ : Specht t) = 0 :=
      φ.symm.toLinearEquiv.injective (by rw [Representation.Equiv.toLinearEquiv_apply, this, map_zero])
    exact polytabloid_ne_zero t (congrArg Subtype.val h2)
  have h2 : Occurs s (contentSub (content (rowWord t))).toRepresentation := by
    refine occurs_of_le s (spechtSub_le_contentSub t) ⟨φ.toIntertwiningMap, fun h0 => ?_⟩
    have : φ.toIntertwiningMap ⟨polytabloid s, polytabloid_mem_specht s⟩ = 0 := by
      rw [h0]; rfl
    have h2 : (⟨polytabloid s, polytabloid_mem_specht s⟩ : Specht s) = 0 :=
      φ.toLinearEquiv.injective (by rw [Representation.Equiv.toLinearEquiv_apply, this, map_zero])
    exact polytabloid_ne_zero s (congrArg Subtype.val h2)
  exact Dominates.antisymm (dominates_of_occurs_contentSub t s h1)
    (dominates_of_occurs_contentSub s t h2)

end occurs

end OAI.Saxl
