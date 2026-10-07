import Mathlib
import Saxl.Statement
import Saxl.Polytabloid
import Saxl.Strips
import Saxl.Young

/-!
# Branching along a horizontal strip (towards Pieri-occurrence)

Setting: `n = a + b`, `ν ⊆ λ` with `λ/ν` a horizontal strip of size `b`, and a `λ`-tableau `t`
whose first `a` positions (`Fin.castAdd b i`) carry the cells of `ν` and whose last `b` positions
(`Fin.natAdd a j`) carry the strip.  We build

* the embedding `embPair : S_a × S_b →* S_{a+b}`;
* the `ν`-tableau `nuTableau` cut out of `t`;
* the restriction map `Φ f = f ∘ extend` from words on `a + b` positions to words on `a` positions,
  which is `S_a`-equivariant;
* the `S_b`-symmetrised polytabloid `symmPolytabloid`, an `S_b`-fixed vector of `S^λ`.

Part 2 (to come) computes `Φ symmPolytabloid = c • polytabloid nuTableau` with `c ≠ 0`.
-/

namespace OAI.Saxl

open Equiv YoungDiagram

attribute [local instance] Fintype.ofFinite

section embedding

variable {a b : ℕ}

/-- `S_a × S_b ↪ S_{a+b}`, acting on the first `a` and last `b` positions. -/
def embPair : Perm (Fin a) × Perm (Fin b) →* Perm (Fin (a + b)) where
  toFun p := finSumFinEquiv.permCongr (Perm.sumCongrHom _ _ p)
  map_one' := by ext x; simp [Equiv.permCongr_apply]
  map_mul' x y := by ext z; simp [Equiv.permCongr_apply, Perm.mul_apply]

/-- `S_a` acting on the first `a` positions. -/
def embA (σ : Perm (Fin a)) : Perm (Fin (a + b)) := embPair (σ, 1)

/-- `S_b` acting on the last `b` positions. -/
def embB (τ : Perm (Fin b)) : Perm (Fin (a + b)) := embPair (1, τ)

@[simp] theorem embPair_castAdd (p : Perm (Fin a) × Perm (Fin b)) (i : Fin a) :
    embPair p (Fin.castAdd b i) = Fin.castAdd b (p.1 i) := by
  simp [embPair, Equiv.permCongr_apply, ← finSumFinEquiv_apply_left]

@[simp] theorem embPair_natAdd (p : Perm (Fin a) × Perm (Fin b)) (j : Fin b) :
    embPair p (Fin.natAdd a j) = Fin.natAdd a (p.2 j) := by
  simp [embPair, Equiv.permCongr_apply, ← finSumFinEquiv_apply_right]

@[simp] theorem embA_castAdd (σ : Perm (Fin a)) (i : Fin a) :
    embA (b := b) σ (Fin.castAdd b i) = Fin.castAdd b (σ i) := by simp [embA]

@[simp] theorem embA_natAdd (σ : Perm (Fin a)) (j : Fin b) :
    embA σ (Fin.natAdd a j) = Fin.natAdd a j := by simp [embA]

@[simp] theorem embB_castAdd (τ : Perm (Fin b)) (i : Fin a) :
    embB (a := a) τ (Fin.castAdd b i) = Fin.castAdd b i := by simp [embB]

@[simp] theorem embB_natAdd (τ : Perm (Fin b)) (j : Fin b) :
    embB (a := a) τ (Fin.natAdd a j) = Fin.natAdd a (τ j) := by simp [embB]

theorem embA_mul (σ σ' : Perm (Fin a)) : embA (b := b) (σ * σ') = embA σ * embA σ' := by
  simp [embA, ← map_mul]

theorem embB_mul (τ τ' : Perm (Fin b)) : embB (a := a) (τ * τ') = embB τ * embB τ' := by
  simp [embB, ← map_mul]

theorem embA_one : embA (a := a) (b := b) 1 = 1 := by
  show embPair 1 = 1
  exact map_one _

end embedding

/-- A `λ`-tableau on `a + b` positions whose first `a` positions carry `ν` and whose last `b`
positions carry `λ/ν`. -/
structure StripTableau (a b : ℕ) (nu lam : YoungDiagram) where
  /-- The underlying `λ`-tableau. -/
  t : Tableau (a + b) lam
  /-- The first `a` positions carry cells of `ν`. -/
  mem_nu : ∀ i : Fin a, (t (Fin.castAdd b i)).val ∈ nu
  /-- The last `b` positions carry cells outside `ν`. -/
  not_mem_nu : ∀ j : Fin b, (t (Fin.natAdd a j)).val ∉ nu

namespace StripTableau

variable {a b : ℕ} {nu lam : YoungDiagram} (T : StripTableau a b nu lam)

/-- Every position is a `castAdd` or a `natAdd`. -/
theorem exists_castAdd_or_natAdd (p : Fin (a + b)) :
    (∃ i : Fin a, p = Fin.castAdd b i) ∨ (∃ j : Fin b, p = Fin.natAdd a j) :=
  Fin.addCases (motive := fun p => (∃ i : Fin a, p = Fin.castAdd b i) ∨ (∃ j, p = Fin.natAdd a j))
    (fun i => Or.inl ⟨i, rfl⟩) (fun j => Or.inr ⟨j, rfl⟩) p

/-- The `ν`-tableau carried by the first `a` positions. -/
noncomputable def nuTableau (hle : nu ≤ lam) : Tableau a nu :=
  Equiv.ofBijective (fun i => ⟨(T.t (Fin.castAdd b i)).val, T.mem_nu i⟩) <| by
    refine ⟨fun i i' h => ?_, fun c => ?_⟩
    · have h' := congrArg Subtype.val h
      have h2 : T.t (Fin.castAdd b i) = T.t (Fin.castAdd b i') := Subtype.ext h'
      exact Fin.ext (by simpa using congrArg Fin.val (T.t.injective h2))
    · have hc : c.val ∈ lam := hle c.2
      rcases exists_castAdd_or_natAdd (T.t.symm ⟨c.val, hc⟩) with ⟨i, hi⟩ | ⟨j, hj⟩
      · refine ⟨i, Subtype.ext ?_⟩
        show (T.t (Fin.castAdd b i)).val = c.val
        rw [← hi]; simp
      · exfalso
        apply T.not_mem_nu j
        have : (T.t (Fin.natAdd a j)).val = c.val := by rw [← hj]; simp
        rw [this]; exact c.2

theorem nuTableau_apply (hle : nu ≤ lam) (i : Fin a) :
    (T.nuTableau hle i).val = (T.t (Fin.castAdd b i)).val := rfl

theorem rowWord_nuTableau (hle : nu ≤ lam) (i : Fin a) :
    (rowWord (T.nuTableau hle) i : ℕ) = rowWord T.t (Fin.castAdd b i) := rfl

/-- The row of the strip cell at position `natAdd a j`, as a letter. -/
def stripRow (j : Fin b) : Fin (lam.colLen 0) :=
  ⟨(T.t (Fin.natAdd a j)).val.1, by
    have h : ((T.t (Fin.natAdd a j)).val.1, (T.t (Fin.natAdd a j)).val.2) ∈ lam :=
      (T.t (Fin.natAdd a j)).2
    rw [mem_iff_lt_colLen] at h
    exact lt_of_lt_of_le h (lam.colLen_anti 0 _ (Nat.zero_le _))⟩

theorem stripRow_eq (j : Fin b) : (T.stripRow j : ℕ) = rowWord T.t (Fin.natAdd a j) := rfl

/-- Extend a word on the first `a` positions by the strip rows on the last `b`. -/
def extend (hd : nu.colLen 0 ≤ lam.colLen 0) (w : Fin a → Fin (nu.colLen 0)) :
    Fin (a + b) → Fin (lam.colLen 0) :=
  Fin.addCases (fun i => Fin.castLE hd (w i)) (fun j => T.stripRow j)

@[simp] theorem extend_castAdd (hd : nu.colLen 0 ≤ lam.colLen 0) (w : Fin a → Fin (nu.colLen 0))
    (i : Fin a) : T.extend hd w (Fin.castAdd b i) = Fin.castLE hd (w i) := by
  simp [extend]

@[simp] theorem extend_natAdd (hd : nu.colLen 0 ≤ lam.colLen 0) (w : Fin a → Fin (nu.colLen 0))
    (j : Fin b) : T.extend hd w (Fin.natAdd a j) = T.stripRow j := by
  simp [extend]

/-- The restriction map `Φ f = f ∘ extend` from `λ`-words to `ν`-words. -/
noncomputable def Φ (hd : nu.colLen 0 ≤ lam.colLen 0) :
    WordSpace (a + b) (lam.colLen 0) →ₗ[ℂ] WordSpace a (nu.colLen 0) :=
  LinearMap.funLeft ℂ ℂ (T.extend hd)

theorem Φ_apply (hd : nu.colLen 0 ≤ lam.colLen 0) (f : WordSpace (a + b) (lam.colLen 0))
    (w : Fin a → Fin (nu.colLen 0)) : T.Φ hd f w = f (T.extend hd w) := rfl

theorem extend_comp_embA (hd : nu.colLen 0 ≤ lam.colLen 0) (w : Fin a → Fin (nu.colLen 0))
    (σ : Perm (Fin a)) : T.extend hd w ∘ embA σ = T.extend hd (w ∘ σ) := by
  funext p
  refine Fin.addCases (fun i => ?_) (fun j => ?_) p <;> simp

/-- `Φ` is `S_a`-equivariant. -/
theorem Φ_wordRep (hd : nu.colLen 0 ≤ lam.colLen 0) (σ : Perm (Fin a))
    (f : WordSpace (a + b) (lam.colLen 0)) :
    T.Φ hd (wordRep (a + b) (lam.colLen 0) (embA σ) f) =
      wordRep a (nu.colLen 0) σ (T.Φ hd f) := by
  funext w
  rw [Φ_apply, wordRep_apply, wordRep_apply, Φ_apply, extend_comp_embA]

/-- The `S_b`-symmetrised polytabloid. -/
noncomputable def symmPolytabloid : WordSpace (a + b) (lam.colLen 0) :=
  ∑ τ : Perm (Fin b), wordRep (a + b) (lam.colLen 0) (embB τ) (polytabloid T.t)

/-- `symmPolytabloid` lies in `S^λ`. -/
theorem symmPolytabloid_mem : T.symmPolytabloid ∈ Specht T.t :=
  Submodule.sum_mem _ fun τ _ => Submodule.subset_span ⟨embB τ, rfl⟩

/-- `symmPolytabloid` is fixed by `S_b`. -/
theorem wordRep_embB_symmPolytabloid (τ : Perm (Fin b)) :
    wordRep (a + b) (lam.colLen 0) (embB τ) T.symmPolytabloid = T.symmPolytabloid := by
  unfold symmPolytabloid
  rw [map_sum]
  apply Fintype.sum_equiv (Equiv.mulLeft τ)
  intro τ'
  rw [Equiv.coe_mulLeft, embB_mul, map_mul, Module.End.mul_apply]

end StripTableau

end OAI.Saxl
