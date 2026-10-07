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

/-! ### Part 2: the key computation `Φ u = c • e_{t_ν}` -/

/-- The strip cell is the bottom of its column: any cell of `λ` in that column has row `≤`. -/
theorem row_le_stripRow (hstrip : HorizontalStrip nu lam) (j : Fin b) {q : Fin (a + b)}
    (hq : (T.t q).val.2 = (T.t (Fin.natAdd a j)).val.2) :
    (T.t q).val.1 ≤ (T.t (Fin.natAdd a j)).val.1 := by
  have h1 : ((T.t (Fin.natAdd a j)).val.1, (T.t (Fin.natAdd a j)).val.2) ∈ lam :=
    (T.t (Fin.natAdd a j)).2
  have h2 : ((T.t (Fin.natAdd a j)).val.1, (T.t (Fin.natAdd a j)).val.2) ∉ nu := T.not_mem_nu j
  have h3 : ((T.t q).val.1, (T.t q).val.2) ∈ lam := (T.t q).2
  rw [hq] at h3
  rw [mem_iff_lt_colLen] at h1 h2 h3
  have := hstrip.2 (T.t (Fin.natAdd a j)).val.2
  omega

/-- Column permutations matching the strip rows (up to `τ`) fix every strip position, and `τ`
preserves strip rows. -/
theorem fixes_strip_of_rows (hstrip : HorizontalStrip nu lam) {g : Perm (Fin (a + b))}
    (hg : g ∈ columnGroup T.t) (τ : Perm (Fin b))
    (h : ∀ j, (T.stripRow (τ j) : ℕ) = rowWord T.t (g⁻¹ (Fin.natAdd a j))) :
    (∀ j, g⁻¹ (Fin.natAdd a j) = Fin.natAdd a j) ∧ ∀ j, T.stripRow (τ j) = T.stripRow j := by
  have hg' := (columnGroup T.t).inv_mem hg
  have hle : ∀ j, (rowWord T.t (g⁻¹ (Fin.natAdd a j)) : ℕ) ≤ (T.stripRow j : ℕ) := fun j =>
    T.row_le_stripRow hstrip j ((mem_columnGroup T.t).1 hg' (Fin.natAdd a j))
  have hsum : ∑ j, (rowWord T.t (g⁻¹ (Fin.natAdd a j)) : ℕ) = ∑ j, (T.stripRow j : ℕ) := by
    rw [← Equiv.sum_comp τ (fun j => (T.stripRow j : ℕ))]
    exact Finset.sum_congr rfl fun j _ => (h j).symm
  have heq := (Finset.sum_eq_sum_iff_of_le fun j _ => hle j).1 hsum
  refine ⟨fun j => ?_, fun j => ?_⟩
  · apply T.t.injective
    apply Subtype.ext
    apply Prod.ext
    · exact heq j (Finset.mem_univ _)
    · exact (mem_columnGroup T.t).1 hg' (Fin.natAdd a j)
  · apply Fin.ext
    rw [h j]
    exact heq j (Finset.mem_univ _)

/-- A permutation fixing every strip position comes from `S_a`. -/
theorem exists_embA_of_fixes {g : Perm (Fin (a + b))}
    (hfix : ∀ j, g (Fin.natAdd a j) = Fin.natAdd a j) : ∃ h : Perm (Fin a), g = embA h := by
  have hlt : ∀ i : Fin a, (g (Fin.castAdd b i)).val < a := by
    intro i
    rcases exists_castAdd_or_natAdd (g (Fin.castAdd b i)) with ⟨i', hi'⟩ | ⟨j, hj⟩
    · rw [hi']; simp
    · exfalso
      have := g.injective (hj.trans (hfix j).symm)
      have := congrArg Fin.val this
      simp at this
      omega
  let f : Fin a → Fin a := fun i => ⟨(g (Fin.castAdd b i)).val, hlt i⟩
  have hinj : Function.Injective f := by
    intro i i' h
    have := congrArg Fin.val h
    simp only [f] at this
    have h2 : g (Fin.castAdd b i) = g (Fin.castAdd b i') := Fin.ext this
    exact Fin.ext (by simpa using congrArg Fin.val (g.injective h2))
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), ?_⟩
  ext p
  refine Fin.addCases (fun i => ?_) (fun j => ?_) p
  · simp [f]
  · simp [hfix]

/-- `h ∈ C_{t_ν}` iff `embA h ∈ C_t`. -/
theorem embA_mem_columnGroup_iff (hle : nu ≤ lam) (h : Perm (Fin a)) :
    embA (b := b) h ∈ columnGroup T.t ↔ h ∈ columnGroup (T.nuTableau hle) := by
  simp only [mem_columnGroup]
  constructor
  · intro H i
    have := H (Fin.castAdd b i)
    simpa [nuTableau_apply] using this
  · intro H p
    refine Fin.addCases (fun i => ?_) (fun j => ?_) p
    · have := H i
      simpa [nuTableau_apply] using this
    · simp

/-- `sign (embA h) = sign h`. -/
theorem sign_embA (h : Perm (Fin a)) : Perm.sign (embA (b := b) h) = Perm.sign h := by
  simp [embA, embPair, Perm.sign_permCongr, Perm.sign_sumCongr]

/-- `(embA h)⁻¹ = embA h⁻¹`. -/
theorem embA_inv (h : Perm (Fin a)) : (embA (b := b) h)⁻¹ = embA h⁻¹ := by
  rw [embA, embA, ← map_inv, Prod.inv_mk, inv_one]

theorem rowWord_embA_inv_castAdd (hle : nu ≤ lam) (h : Perm (Fin a)) (i : Fin a) :
    (rowWord T.t ((embA h)⁻¹ (Fin.castAdd b i)) : ℕ) = rowWord (T.nuTableau hle) (h⁻¹ i) := by
  rw [embA_inv, embA_castAdd, rowWord_nuTableau]

/-- The key equivalence: when does the extended word match a term of the polytabloid? -/
theorem extend_comp_embB_eq_iff (hstrip : HorizontalStrip nu lam) (hd : nu.colLen 0 ≤ lam.colLen 0)
    (w : Fin a → Fin (nu.colLen 0)) (τ : Perm (Fin b)) {g : Perm (Fin (a + b))}
    (hg : g ∈ columnGroup T.t) :
    T.extend hd w ∘ embB τ = rowWord T.t ∘ ⇑(g⁻¹ : Perm (Fin (a + b))) ↔
      (∀ j, T.stripRow (τ j) = T.stripRow j) ∧ (∀ j, g (Fin.natAdd a j) = Fin.natAdd a j) ∧
        ∀ i, (w i : ℕ) = rowWord T.t (g⁻¹ (Fin.castAdd b i)) := by
  constructor
  · intro H
    have hrow : ∀ j, (T.stripRow (τ j) : ℕ) = rowWord T.t (g⁻¹ (Fin.natAdd a j)) := fun j => by
      have := congrFun H (Fin.natAdd a j)
      simp only [Function.comp_apply, embB_natAdd, extend_natAdd] at this
      exact congrArg Fin.val this
    obtain ⟨hfix, hτ⟩ := T.fixes_strip_of_rows hstrip hg τ hrow
    refine ⟨hτ, fun j => ?_, fun i => ?_⟩
    · have := hfix j
      rw [Perm.inv_eq_iff_eq] at this
      exact this.symm
    · have := congrFun H (Fin.castAdd b i)
      simp only [Function.comp_apply, embB_castAdd, extend_castAdd] at this
      have := congrArg Fin.val this
      simpa using this
  · rintro ⟨hτ, hfix, hw⟩
    funext p
    refine Fin.addCases (fun i => ?_) (fun j => ?_) p
    · simp only [Function.comp_apply, embB_castAdd, extend_castAdd]
      exact Fin.ext (by simpa using hw i)
    · simp only [Function.comp_apply, embB_natAdd, extend_natAdd]
      have hfix' : g⁻¹ (Fin.natAdd a j) = Fin.natAdd a j := by
        rw [Perm.inv_eq_iff_eq]; exact (hfix j).symm
      rw [hτ j, hfix']
      rfl

/-- Number of strip-row-preserving permutations of the strip positions. -/
def stripCount : ℕ :=
  (Finset.univ.filter fun τ : Perm (Fin b) => ∀ j, T.stripRow (τ j) = T.stripRow j).card

theorem stripCount_pos : 0 < T.stripCount :=
  Finset.card_pos.2 ⟨1, by simp⟩

/-- Coefficient of a polytabloid at a word. -/
theorem polytabloid_coeff {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (v : Fin n → Fin (μ.colLen 0)) :
    polytabloid t v = ∑ g : columnGroup t, (((Perm.sign (g : Perm (Fin n))) : ℤ) : ℂ) *
      (if v = rowWord t ∘ ⇑((g : Perm (Fin n))⁻¹ : Perm (Fin n)) then 1 else 0) := by
  rw [polytabloid_eq_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul]

/-- **The key computation**: `Φ u = stripCount • e_{t_ν}`. -/
theorem Φ_symmPolytabloid (hle : nu ≤ lam) (hstrip : HorizontalStrip nu lam)
    (hd : nu.colLen 0 ≤ lam.colLen 0) :
    T.Φ hd T.symmPolytabloid = (T.stripCount : ℂ) • polytabloid (T.nuTableau hle) := by
  funext w
  rw [Φ_apply, symmPolytabloid, Finset.sum_apply, Pi.smul_apply, polytabloid_coeff, smul_eq_mul]
  simp_rw [wordRep_apply, polytabloid_coeff]
  have hsplit : ∀ (τ : Perm (Fin b)) (g : columnGroup T.t),
      (if T.extend hd w ∘ embB τ =
          rowWord T.t ∘ ⇑((g : Perm (Fin (a + b)))⁻¹ : Perm (Fin (a + b))) then (1 : ℂ) else 0) =
        (if ∀ j, T.stripRow (τ j) = T.stripRow j then (1 : ℂ) else 0) *
        (if (∀ j, (g : Perm (Fin (a + b))) (Fin.natAdd a j) = Fin.natAdd a j) ∧
            ∀ i, (w i : ℕ) = rowWord T.t ((g : Perm (Fin (a + b)))⁻¹ (Fin.castAdd b i))
          then (1 : ℂ) else 0) := by
    intro τ g
    have hiff := T.extend_comp_embB_eq_iff hstrip hd w τ g.2
    by_cases h1 : T.extend hd w ∘ embB τ =
        rowWord T.t ∘ ⇑((g : Perm (Fin (a + b)))⁻¹ : Perm (Fin (a + b)))
    · obtain ⟨hP, hQ, hR⟩ := hiff.1 h1
      rw [if_pos h1, if_pos hP, if_pos ⟨hQ, hR⟩, one_mul]
    · rw [if_neg h1]
      split_ifs with hP hQR <;> first | exact absurd (hiff.2 ⟨hP, hQR⟩) h1 | simp
  have hcount : (∑ τ : Perm (Fin b), if ∀ j, T.stripRow (τ j) = T.stripRow j then (1 : ℂ) else 0) =
      (T.stripCount : ℂ) := by
    rw [Finset.sum_boole]; rfl
  have hbij : (∑ h : columnGroup (T.nuTableau hle), (((Perm.sign (h : Perm (Fin a))) : ℤ) : ℂ) *
        (if w = rowWord (T.nuTableau hle) ∘ ⇑((h : Perm (Fin a))⁻¹ : Perm (Fin a)) then 1 else 0)) =
      ∑ g : columnGroup T.t, (((Perm.sign (g : Perm (Fin (a + b)))) : ℤ) : ℂ) *
        (if (∀ j, (g : Perm (Fin (a + b))) (Fin.natAdd a j) = Fin.natAdd a j) ∧
            ∀ i, (w i : ℕ) = rowWord T.t ((g : Perm (Fin (a + b)))⁻¹ (Fin.castAdd b i))
          then (1 : ℂ) else 0) := by
    refine Finset.sum_bij_ne_zero
      (fun h _ _ => (⟨embA h, (T.embA_mem_columnGroup_iff hle h).2 h.2⟩ : columnGroup T.t))
      (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro h₁ _ _ h₂ _ _ heq
      have heq' : embA (b := b) (h₁ : Perm (Fin a)) = embA h₂ := congrArg Subtype.val heq
      ext1
      ext i
      have := congrArg (fun σ : Perm (Fin (a + b)) => (σ (Fin.castAdd b i)).val) heq'
      simpa using this
    · intro g _ hne
      have hQR : (∀ j, (g : Perm (Fin (a + b))) (Fin.natAdd a j) = Fin.natAdd a j) ∧
          ∀ i, (w i : ℕ) = rowWord T.t ((g : Perm (Fin (a + b)))⁻¹ (Fin.castAdd b i)) := by
        by_contra hcon
        apply hne
        rw [if_neg hcon, mul_zero]
      obtain ⟨h, hh⟩ := exists_embA_of_fixes hQR.1
      have hmem : h ∈ columnGroup (T.nuTableau hle) :=
        (T.embA_mem_columnGroup_iff hle h).1 (by rw [← hh]; exact g.2)
      have hw : w = rowWord (T.nuTableau hle) ∘ ⇑(h⁻¹ : Perm (Fin a)) := by
        funext i
        apply Fin.ext
        rw [Function.comp_apply, ← T.rowWord_embA_inv_castAdd hle, ← hh]
        exact hQR.2 i
      refine ⟨⟨h, hmem⟩, Finset.mem_univ _, ?_, ?_⟩
      · show (((Perm.sign h) : ℤ) : ℂ) *
            (if w = rowWord (T.nuTableau hle) ∘ ⇑(h⁻¹ : Perm (Fin a)) then 1 else 0) ≠ 0
        rw [if_pos hw, mul_one]
        rcases Int.units_eq_one_or (Perm.sign (h : Perm (Fin a))) with hs | hs <;> simp [hs]
      · ext1; exact hh.symm
    · intro h _ _
      show (((Perm.sign (h : Perm (Fin a))) : ℤ) : ℂ) * _ =
        (((Perm.sign (embA (b := b) (h : Perm (Fin a)))) : ℤ) : ℂ) * _
      rw [sign_embA]
      congr 1
      have hQ : ∀ j, embA (b := b) (h : Perm (Fin a)) (Fin.natAdd a j) = Fin.natAdd a j :=
        fun j => embA_natAdd _ _
      have hR : (∀ i, (w i : ℕ) = rowWord T.t ((embA (b := b) (h : Perm (Fin a)))⁻¹ (Fin.castAdd b i)))
          ↔ w = rowWord (T.nuTableau hle) ∘ ⇑((h : Perm (Fin a))⁻¹ : Perm (Fin a)) := by
        simp_rw [T.rowWord_embA_inv_castAdd hle]
        constructor
        · intro H; funext i; exact Fin.ext (H i)
        · intro H i; rw [H]; rfl
      by_cases hw : w = rowWord (T.nuTableau hle) ∘ ⇑((h : Perm (Fin a))⁻¹ : Perm (Fin a))
      · rw [if_pos hw, if_pos ⟨hQ, hR.2 hw⟩]
      · rw [if_neg hw, if_neg (fun H => hw (hR.1 H.2))]
  rw [hbij, ← hcount, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun g _ => ?_
  rw [hsplit τ g]
  ring

end StripTableau

end OAI.Saxl
