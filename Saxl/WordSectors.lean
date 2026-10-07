import Mathlib
import Saxl.WordRep
import Saxl.Branching
import Saxl.Sectors

/-!
# Sectors of a word space by the positions of a distinguished letter

For the sector lemma applied to `M^θ = ℂ[S_n] e_{w₀}`: `Ω` is the set of `b`-subsets of positions,
`S_n` acts transitively, the sector `π_A` keeps the words whose set of positions carrying the
letter `ℓ₀` is exactly `A`, and for `D` = the last `b` positions the stabiliser is presented by
`embPair : S_a × S_b →* S_{a+b}`.
-/

namespace OAI.Saxl

open Equiv

/-- `b`-subsets of `Fin n`. -/
abbrev Subsets (n b : ℕ) := {A : Finset (Fin n) // A.card = b}

instance (n b : ℕ) : MulAction (Perm (Fin n)) (Subsets n b) where
  smul g A := ⟨A.1.map g.toEmbedding, by rw [Finset.card_map]; exact A.2⟩
  one_smul A := by
    ext1; ext p
    show p ∈ A.1.map (1 : Perm (Fin n)).toEmbedding ↔ p ∈ A.1
    rw [Finset.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩; exact hq
    · intro h; exact ⟨p, h, rfl⟩
  mul_smul g h A := by
    ext1; ext p
    show p ∈ A.1.map (g * h).toEmbedding ↔ p ∈ (A.1.map h.toEmbedding).map g.toEmbedding
    simp only [Finset.mem_map, Equiv.coe_toEmbedding, Perm.mul_apply]
    constructor
    · rintro ⟨q, hq, rfl⟩; exact ⟨h q, ⟨q, hq, rfl⟩, rfl⟩
    · rintro ⟨q', ⟨q, hq, rfl⟩, rfl⟩; exact ⟨q, hq, rfl⟩

theorem smul_subsets_val {n b : ℕ} (g : Perm (Fin n)) (A : Subsets n b) :
    (g • A).1 = A.1.map g.toEmbedding := rfl

theorem mem_smul_subsets {n b : ℕ} (g : Perm (Fin n)) (A : Subsets n b) (p : Fin n) :
    p ∈ (g • A).1 ↔ g⁻¹ p ∈ A.1 := by
  rw [smul_subsets_val, Finset.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩; simpa [Perm.inv_def] using hq
  · intro h; exact ⟨g⁻¹ p, h, by simp [Perm.inv_def]⟩

/-- `S_n` acts transitively on `b`-subsets. -/
instance (n b : ℕ) : MulAction.IsPretransitive (Perm (Fin n)) (Subsets n b) where
  exists_smul_eq A B := by
    classical
    have hc : Fintype.card {p // p ∈ A.1} = Fintype.card {p // p ∈ B.1} := by
      simp [A.2, B.2]
    have hc' : Fintype.card {p // ¬ p ∈ A.1} = Fintype.card {p // ¬ p ∈ B.1} := by
      simp only [Fintype.card_subtype_compl, hc]
    let e := Fintype.equivOfCardEq hc
    let e' := Fintype.equivOfCardEq hc'
    let g : Perm (Fin n) :=
      (Equiv.sumCompl (· ∈ A.1)).symm.trans ((e.sumCongr e').trans (Equiv.sumCompl (· ∈ B.1)))
    refine ⟨g, ?_⟩
    ext1
    ext p
    rw [smul_subsets_val, Finset.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩
      show g q ∈ B.1
      simp only [g, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hq, Equiv.sumCongr_apply,
        Sum.map_inl, Equiv.sumCompl_apply_inl]
      exact (e ⟨q, hq⟩).2
    · intro hp
      refine ⟨g.symm p, ?_, by simp⟩
      show g.symm p ∈ A.1
      simp only [g, Equiv.symm_trans_apply, Equiv.sumCompl_symm_apply_of_pos hp,
        Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl, Equiv.symm_symm,
        Equiv.sumCompl_apply_inl]
      exact (e.symm ⟨p, hp⟩).2

section strip

variable {a b : ℕ}

/-- The last `b` positions, as a `b`-subset of `Fin (a + b)`. -/
def lastPositions (a b : ℕ) : Subsets (a + b) b :=
  ⟨Finset.univ.map ⟨Fin.natAdd a, fun i j h => Fin.ext (by simpa using congrArg Fin.val h)⟩, by simp⟩

theorem mem_lastPositions (p : Fin (a + b)) :
    p ∈ (lastPositions a b).1 ↔ ∃ j, p = Fin.natAdd a j := by
  simp only [lastPositions, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j, hj.symm⟩
  · rintro ⟨j, hj⟩; exact ⟨j, hj.symm⟩

theorem castAdd_not_mem_lastPositions (i : Fin a) :
    Fin.castAdd b i ∉ (lastPositions a b).1 := by
  rw [mem_lastPositions]
  rintro ⟨j, hj⟩
  have := congrArg Fin.val hj
  simp at this
  omega

/-- `embPair` fixes the last `b` positions. -/
theorem embPair_smul_lastPositions (p : Perm (Fin a) × Perm (Fin b)) :
    embPair p • lastPositions a b = lastPositions a b := by
  ext1
  ext q
  rw [mem_smul_subsets, mem_lastPositions, mem_lastPositions]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨p.2 j, ?_⟩
    have : q = embPair p (Fin.natAdd a j) := by rw [← hj]; simp
    rw [this, embPair_natAdd]
  · rintro ⟨j, rfl⟩
    refine ⟨p.2⁻¹ j, ?_⟩
    rw [Perm.inv_eq_iff_eq, embPair_natAdd]
    simp

/-- Every permutation fixing the last `b` positions (as a set) comes from `S_a × S_b`. -/
theorem exists_embPair_of_smul_eq {g : Perm (Fin (a + b))}
    (hg : g • lastPositions a b = lastPositions a b) :
    ∃ p : Perm (Fin a) × Perm (Fin b), g = embPair p := by
  have hD : ∀ q, q ∈ (lastPositions a b).1 ↔ g⁻¹ q ∈ (lastPositions a b).1 := fun q => by
    rw [← mem_smul_subsets, hg]
  have hnat : ∀ j, ∃ j', g (Fin.natAdd a j) = Fin.natAdd a j' := fun j => by
    have := (hD (g (Fin.natAdd a j))).2 (by rw [perm_inv_apply']; exact (mem_lastPositions _).2 ⟨j, rfl⟩)
    exact (mem_lastPositions _).1 this
  have hcast : ∀ i, ∃ i', g (Fin.castAdd b i) = Fin.castAdd b i' := fun i => by
    rcases StripTableau.exists_castAdd_or_natAdd (g (Fin.castAdd b i)) with ⟨i', hi'⟩ | ⟨j, hj⟩
    · exact ⟨i', hi'⟩
    · exfalso
      have h1 : g (Fin.castAdd b i) ∈ (lastPositions a b).1 := by
        rw [hj]; exact (mem_lastPositions _).2 ⟨j, rfl⟩
      rw [hD, perm_inv_apply'] at h1
      exact castAdd_not_mem_lastPositions i h1
  choose σf hσf using hcast
  choose τf hτf using hnat
  have hσinj : Function.Injective σf := by
    intro i i' h
    have := g.injective ((hσf i).trans ((congrArg (Fin.castAdd b) h).trans (hσf i').symm))
    exact Fin.ext (by simpa using congrArg Fin.val this)
  have hτinj : Function.Injective τf := by
    intro j j' h
    have := g.injective ((hτf j).trans ((congrArg (Fin.natAdd a) h).trans (hτf j').symm))
    exact Fin.ext (by simpa using congrArg Fin.val this)
  refine ⟨(Equiv.ofBijective σf (Finite.injective_iff_bijective.1 hσinj),
    Equiv.ofBijective τf (Finite.injective_iff_bijective.1 hτinj)), ?_⟩
  ext q
  refine Fin.addCases (fun i => ?_) (fun j => ?_) q
  · rw [embPair_castAdd, hσf i]; rfl
  · rw [embPair_natAdd, hτf j]; rfl
where
  perm_inv_apply' : ∀ {α : Type} (g : Perm α) (x : α), g⁻¹ (g x) = x := fun g x => by
    rw [Perm.inv_def]; exact Equiv.symm_apply_apply _ _

end strip

section sectors

variable {n : ℕ} {L : Type} [Fintype L] [DecidableEq L] (ℓ₀ : L)

/-- Positions of a word carrying the letter `ℓ₀`. -/
def letterSet (u : Fin n → L) : Finset (Fin n) := Finset.univ.filter fun p => u p = ℓ₀

theorem mem_letterSet (u : Fin n → L) (p : Fin n) : p ∈ letterSet ℓ₀ u ↔ u p = ℓ₀ := by
  simp [letterSet]

theorem letterSet_comp (u : Fin n → L) (g : Perm (Fin n)) :
    letterSet ℓ₀ (u ∘ g) = (letterSet ℓ₀ u).map g⁻¹.toEmbedding := by
  ext p
  rw [mem_letterSet, Finset.mem_map]
  constructor
  · intro h; exact ⟨g p, (mem_letterSet ℓ₀ u _).2 h, by simp [Perm.inv_def]⟩
  · rintro ⟨q, hq, rfl⟩
    show u (g (g⁻¹ q)) = ℓ₀
    rw [Perm.inv_def, Equiv.apply_symm_apply]
    exact (mem_letterSet ℓ₀ u q).1 hq

variable (b : ℕ)

/-- The sector projection onto words whose `ℓ₀`-positions are exactly `A`. -/
def sectorProj (A : Subsets n b) : WordSpaceL n L →ₗ[ℂ] WordSpaceL n L where
  toFun f u := if letterSet ℓ₀ u = A.1 then f u else 0
  map_add' f g := by
    funext u; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c f := by
    funext u; simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; split_ifs <;> simp

theorem sectorProj_apply (A : Subsets n b) (f : WordSpaceL n L) (u : Fin n → L) :
    sectorProj ℓ₀ b A f u = if letterSet ℓ₀ u = A.1 then f u else 0 := rfl

theorem sectorProj_disj (A B : Subsets n b) (hAB : A ≠ B) :
    sectorProj ℓ₀ b A ∘ₗ sectorProj ℓ₀ b B = 0 := by
  refine LinearMap.ext fun f => funext fun u => ?_
  simp only [LinearMap.comp_apply, sectorProj_apply, LinearMap.zero_apply, Pi.zero_apply]
  split_ifs with h1 h2
  · exact absurd (Subtype.ext (h1.symm.trans h2)) hAB
  · rfl
  · rfl

theorem sectorProj_equiv (g : Perm (Fin n)) (A : Subsets n b) :
    wordRepL n L g ∘ₗ sectorProj ℓ₀ b A = sectorProj ℓ₀ b (g • A) ∘ₗ wordRepL n L g := by
  refine LinearMap.ext fun f => funext fun u => ?_
  simp only [LinearMap.comp_apply, wordRepL_apply, sectorProj_apply, letterSet_comp,
    smul_subsets_val]
  have : (letterSet ℓ₀ u).map g⁻¹.toEmbedding = A.1 ↔ letterSet ℓ₀ u = A.1.map g.toEmbedding := by
    constructor
    · intro h; rw [← h, Finset.map_map]; ext p; simp [Perm.inv_def]
    · intro h; rw [h, Finset.map_map]; ext p; simp [Perm.inv_def]
  by_cases h1 : (letterSet ℓ₀ u).map g⁻¹.toEmbedding = A.1
  · rw [if_pos h1, if_pos (this.1 h1)]
  · rw [if_neg h1, if_neg (fun h => h1 (this.2 h))]

theorem sectorProj_single (A : Subsets n b) (w : Fin n → L) (hw : letterSet ℓ₀ w = A.1) :
    sectorProj ℓ₀ b A (Pi.single w 1) = Pi.single w 1 := by
  funext u
  rw [sectorProj_apply]
  by_cases h : u = w
  · subst h; rw [if_pos hw]
  · rw [Pi.single_eq_of_ne h]; split_ifs <;> rfl

end sectors

end OAI.Saxl
