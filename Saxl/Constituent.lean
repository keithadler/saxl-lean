import Mathlib
import Saxl.Classification
import Saxl.MaschkeBridge

/-!
# Extracting a Specht constituent

* `exists_irreducible_subrep` : a nonzero finite-dimensional representation has an irreducible
  subrepresentation (a nonzero subrepresentation of minimal dimension).
* `exists_specht_occurs_of_nontrivial` : hence every nonzero finite-dimensional representation of
  `S_n` contains a Specht module.
* `boxTensor ρ A` : the external tensor product `ρ ⊠ A` of representations of `G` and `H`, as a
  representation of `G × H`.
* `exists_specht_boxTensor` : if `ρ ⊠ A → τ` is a nonzero intertwiner then for some Specht module
  `S^η ⊂ A` the composite `ρ ⊠ S^η → τ` is still nonzero (paper, proof of Theorem 3.1, case (ii):
  "Equation (6.3) provides some `η` with `a_η > 0` and `c^λ_{ν,η} > 0`").
* `exists_specht_boxTensor_contentSub` : the same with `A = M^θ`, and then `η ⊵ θ`.
-/

namespace OAI.Saxl

open Equiv Representation

open scoped TensorProduct

section irreducibleSub

variable {G : Type*} [Group G] {X : Type*} [AddCommGroup X] [Module ℂ X]
  (ρ : Representation ℂ G X)

/-- A subrepresentation is `⊥` iff it has no nonzero element. -/
theorem subrep_eq_bot_iff {Z : Subrepresentation ρ} : Z = ⊥ ↔ ∀ v ∈ Z, v = 0 := by
  constructor
  · rintro rfl v hv
    exact subrep_mem_bot.1 hv
  · intro h
    apply Subrepresentation.toSubmodule_injective
    show Z.toSubmodule = ⊥
    rw [Submodule.eq_bot_iff]
    exact h

/-- A subrepresentation of `Z.toRepresentation`, pushed into the ambient representation. -/
def pushSub (Z : Subrepresentation ρ) (W : Subrepresentation Z.toRepresentation) :
    Subrepresentation ρ where
  toSubmodule := W.toSubmodule.map Z.toSubmodule.subtype
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_map] at hv ⊢
    obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨Z.toRepresentation g x, W.apply_mem_toSubmodule g hx, rfl⟩

theorem mem_pushSub {Z : Subrepresentation ρ} {W : Subrepresentation Z.toRepresentation} {v : X} :
    v ∈ pushSub ρ Z W ↔ ∃ x ∈ W, (x : X) = v := by
  show v ∈ W.toSubmodule.map Z.toSubmodule.subtype ↔ _
  rw [Submodule.mem_map]
  rfl

theorem pushSub_le (Z : Subrepresentation ρ) (W : Subrepresentation Z.toRepresentation) :
    pushSub ρ Z W ≤ Z := by
  intro v hv
  obtain ⟨x, _, rfl⟩ := (mem_pushSub ρ).1 hv
  exact x.2

theorem finrank_pushSub (Z : Subrepresentation ρ) (W : Subrepresentation Z.toRepresentation) :
    Module.finrank ℂ (pushSub ρ Z W).toSubmodule = Module.finrank ℂ W.toSubmodule :=
  (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective Z.toSubmodule.subtype Subtype.val_injective W.toSubmodule)).symm

variable [FiniteDimensional ℂ X]

/-- A nonzero finite-dimensional representation has an irreducible subrepresentation. -/
theorem exists_irreducible_subrep [Nontrivial X] :
    ∃ Z : Subrepresentation ρ, Z ≠ ⊥ ∧ IsIrreducible Z.toRepresentation := by
  classical
  have htop : (⊤ : Subrepresentation ρ) ≠ ⊥ := by
    rw [Ne, subrep_eq_bot_iff]
    push Not
    obtain ⟨v, hv⟩ := exists_ne (0 : X)
    exact ⟨v, subrep_mem_top v, hv⟩
  have hex : ∃ d, ∃ Z : Subrepresentation ρ, Z ≠ ⊥ ∧ Module.finrank ℂ Z.toSubmodule = d :=
    ⟨_, ⊤, htop, rfl⟩
  obtain ⟨Z, hZ, hd⟩ := Nat.find_spec hex
  refine ⟨Z, hZ, ?_⟩
  obtain ⟨v, hvZ, hv0⟩ : ∃ v ∈ Z, v ≠ 0 := by
    by_contra h
    push Not at h
    exact hZ (subrep_eq_bot_iff ρ |>.2 h)
  have : Nontrivial (Subrepresentation Z.toRepresentation) := by
    refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
    have hx : (⟨v, hvZ⟩ : Z.toSubmodule) ∈ (⊤ : Subrepresentation Z.toRepresentation) :=
      subrep_mem_top _
    rw [← h, subrep_mem_bot] at hx
    exact hv0 (congrArg Subtype.val hx)
  refine ⟨fun W => ?_⟩
  by_contra hW
  push Not at hW
  obtain ⟨hWbot, hWtop⟩ := hW
  -- the pushed subrepresentation is a proper nonzero subrepresentation of `Z`
  have hne : pushSub ρ Z W ≠ ⊥ := by
    rw [Ne, subrep_eq_bot_iff]
    push Not
    obtain ⟨x, hxW, hx0⟩ : ∃ x ∈ W, x ≠ 0 := by
      by_contra h
      push Not at h
      exact hWbot (subrep_eq_bot_iff _ |>.2 h)
    exact ⟨x, (mem_pushSub ρ).2 ⟨x, hxW, rfl⟩, fun h => hx0 (Subtype.ext h)⟩
  have hlt : (pushSub ρ Z W).toSubmodule < Z.toSubmodule := by
    refine lt_of_le_of_ne (pushSub_le ρ Z W) fun heq => hWtop ?_
    apply Subrepresentation.toSubmodule_injective
    show W.toSubmodule = ⊤
    rw [eq_top_iff]
    intro x _
    have hx : (x : X) ∈ pushSub ρ Z W := by
      show (x : X) ∈ (pushSub ρ Z W).toSubmodule
      rw [heq]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := (mem_pushSub ρ).1 hx
    rw [← Subtype.ext hyx]
    exact hy
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := Nat.find_min' hex ⟨pushSub ρ Z W, hne, rfl⟩
  omega

end irreducibleSub

section spechtSub

variable {n : ℕ}

/-- Every nonzero finite-dimensional representation of `S_n` contains a Specht module. -/
theorem exists_specht_occurs_of_nontrivial {X : Type*} [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] [Nontrivial X] (ρ : Representation ℂ (Perm (Fin n)) X) :
    ∃ (η : YoungDiagram) (hη : η.card = n), Occurs (canonicalTableau η hη) ρ := by
  obtain ⟨Z, _, hirr⟩ := exists_irreducible_subrep ρ
  obtain ⟨η, hη, h⟩ := exists_specht_occurs Z.toRepresentation
  exact ⟨η, hη, Occurs.mono _ Z h⟩

end spechtSub

section boxTensor

variable {G H : Type*} [Group G] [Group H] {V U : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup U] [Module ℂ U]

/-- The external tensor product `ρ ⊠ A` as a representation of `G × H`. -/
noncomputable def boxTensor (ρ : Representation ℂ G V) (A : Representation ℂ H U) :
    Representation ℂ (G × H) (V ⊗[ℂ] U) :=
  Representation.tprod (ρ.comp (MonoidHom.fst G H)) (A.comp (MonoidHom.snd G H))

theorem boxTensor_tmul (ρ : Representation ℂ G V) (A : Representation ℂ H U) (p : G × H)
    (x : V) (z : U) : boxTensor ρ A p (x ⊗ₜ z) = ρ p.1 x ⊗ₜ A p.2 z := by
  simp only [boxTensor, tprod_apply, TensorProduct.map_tmul]
  rfl

/-- An intertwiner `σ → A` of `H`-representations gives `ρ ⊠ σ → ρ ⊠ A`. -/
noncomputable def boxMap (ρ : Representation ℂ G V) {U' : Type*} [AddCommGroup U'] [Module ℂ U']
    {σ : Representation ℂ H U'} {A : Representation ℂ H U} (g : IntertwiningMap σ A) :
    IntertwiningMap (boxTensor ρ σ) (boxTensor ρ A) where
  toLinearMap := TensorProduct.map LinearMap.id g.toLinearMap
  isIntertwining' p := TensorProduct.ext' fun x z => by
    simp only [LinearMap.comp_apply, boxTensor_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
    exact congrArg (fun w => ρ p.1 x ⊗ₜ w) (IntertwiningMap.isIntertwining _ _ g p.2 z)

theorem boxMap_tmul (ρ : Representation ℂ G V) {U' : Type*} [AddCommGroup U'] [Module ℂ U']
    {σ : Representation ℂ H U'} {A : Representation ℂ H U} (g : IntertwiningMap σ A) (x : V)
    (y : U') : boxMap ρ g (x ⊗ₜ y) = x ⊗ₜ g y := rfl

/-- An intertwiner out of a tensor product vanishing on pure tensors is zero. -/
theorem intertwiner_eq_zero_of_tmul {P : Type*} [AddCommGroup P] [Module ℂ P]
    {ρ : Representation ℂ G V} {A : Representation ℂ H U}
    {τ : Representation ℂ (G × H) P} (f : IntertwiningMap (boxTensor ρ A) τ)
    (h : ∀ x z, f (x ⊗ₜ z) = 0) : f = 0 :=
  IntertwiningMap.ext (TensorProduct.ext' fun x z => h x z)

end boxTensor

section extraction

variable {a b : ℕ} {V U P : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  [FiniteDimensional ℂ U] [AddCommGroup P] [Module ℂ P]
  (ρ : Representation ℂ (Perm (Fin a)) V) (A : Representation ℂ (Perm (Fin b)) U)
  (τ : Representation ℂ (Perm (Fin a) × Perm (Fin b)) P)

/-- The subrepresentation of `A` killed by `f` against every vector of `ρ`. -/
def boxKer (f : IntertwiningMap (boxTensor ρ A) τ) : Subrepresentation A where
  toSubmodule :=
    { carrier := {z | ∀ x, f (x ⊗ₜ z) = 0}
      add_mem' := fun {z z'} hz hz' x => by
        rw [TensorProduct.tmul_add, map_add, hz x, hz' x, add_zero]
      zero_mem' := fun x => by rw [TensorProduct.tmul_zero, map_zero]
      smul_mem' := fun c {z} hz x => by
        rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul', map_smul, hz x, smul_zero] }
  apply_mem_toSubmodule k z hz x := by
    have : (x ⊗ₜ A k z : V ⊗[ℂ] U) = boxTensor ρ A (1, k) (x ⊗ₜ z) := by
      rw [boxTensor_tmul, map_one, Module.End.one_apply]
    rw [this, IntertwiningMap.isIntertwining _ _ f, hz x, map_zero]

theorem mem_boxKer {f : IntertwiningMap (boxTensor ρ A) τ} {z : U} :
    z ∈ boxKer ρ A τ f ↔ ∀ x, f (x ⊗ₜ z) = 0 := Iff.rfl

/-- **Constituent extraction.**  A nonzero intertwiner `ρ ⊠ A → τ` stays nonzero on `ρ ⊠ S^η`
for some Specht module `S^η ⊂ A`. -/
theorem exists_specht_boxTensor (f : IntertwiningMap (boxTensor ρ A) τ) (hf : f ≠ 0) :
    ∃ (η : YoungDiagram) (hη : η.card = b) (g : IntertwiningMap (spechtRep (canonicalTableau η hη)) A),
      g ≠ 0 ∧ f.comp (boxMap ρ g) ≠ 0 := by
  classical
  have : NeZero (Nat.card (Perm (Fin b)) : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  set N := boxKer ρ A τ f with hN
  obtain ⟨Q, hQ⟩ := exists_isCompl N
  have hNtop : N ≠ ⊤ := by
    intro h
    apply hf
    refine intertwiner_eq_zero_of_tmul f fun x z => ?_
    have hz : z ∈ N := h ▸ subrep_mem_top z
    exact (mem_boxKer ρ A τ).1 hz x
  have hQbot : Q ≠ ⊥ := by
    intro h
    apply hNtop
    rw [← hQ.sup_eq_top, h, sup_bot_eq]
  obtain ⟨q, hqQ, hq0⟩ : ∃ q ∈ Q, q ≠ 0 := by
    by_contra h
    push Not at h
    exact hQbot (subrep_eq_bot_iff A |>.2 h)
  have : Nontrivial Q.toSubmodule := ⟨⟨⟨q, hqQ⟩, 0, fun h => hq0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨η, hη, g₀, hg₀⟩ := exists_specht_occurs_of_nontrivial Q.toRepresentation
  refine ⟨η, hη, (inclusion Q).comp g₀, fun h0 => hg₀ ?_, fun h0 => ?_⟩
  · refine DFunLike.ext g₀ 0 fun y => ?_
    have h1 : ((inclusion Q).comp g₀) y = 0 := by rw [h0]; rfl
    rw [IntertwiningMap.comp_apply] at h1
    exact inclusion_injective Q (h1.trans (map_zero _).symm)
  · -- pick `y` with `g₀ y ≠ 0`; then `g₀ y ∉ N`, so some `x` detects it
    obtain ⟨y, hy⟩ : ∃ y, g₀ y ≠ 0 := by
      by_contra h
      push Not at h
      exact hg₀ (DFunLike.ext g₀ 0 fun y => by rw [h y]; rfl)
    have hz : (g₀ y : U) ∉ N := by
      intro hmem
      have h1 : (g₀ y : U) ∈ N ⊓ Q := subrep_mem_inf.2 ⟨hmem, (g₀ y).2⟩
      rw [hQ.inf_eq_bot, subrep_mem_bot] at h1
      exact hy (Subtype.ext h1)
    rw [mem_boxKer] at hz
    push Not at hz
    obtain ⟨x, hx⟩ := hz
    apply hx
    have h1 : (f.comp (boxMap ρ ((inclusion Q).comp g₀))) (x ⊗ₜ y) = 0 := by rw [h0]; rfl
    rw [IntertwiningMap.comp_apply, boxMap_tmul] at h1
    exact h1

/-- Constituent extraction with `A = M^θ`: the extracted `S^η` satisfies `η ⊵ θ`. -/
theorem exists_specht_boxTensor_contentSub {θ : YoungDiagram} (s : Tableau b θ)
    (f : IntertwiningMap (boxTensor ρ (contentSub (content (rowWord s))).toRepresentation) τ)
    (hf : f ≠ 0) :
    ∃ (η : YoungDiagram) (hη : η.card = b), Dominates η θ ∧
      ∃ g : IntertwiningMap (spechtRep (canonicalTableau η hη))
        (contentSub (content (rowWord s))).toRepresentation, g ≠ 0 ∧ f.comp (boxMap ρ g) ≠ 0 := by
  obtain ⟨η, hη, g, hg, hfg⟩ := exists_specht_boxTensor ρ _ τ f hf
  exact ⟨η, hη, dominates_of_occurs_contentSub _ s ⟨g, hg⟩, g, hg, hfg⟩

end extraction

end OAI.Saxl
