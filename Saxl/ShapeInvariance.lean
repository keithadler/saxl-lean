import Mathlib
import Saxl.Statement
import Saxl.Polytabloid
import Saxl.Main

/-!
# Occurrence depends only on the shape

For two tableaux `t t'` of the same shape, `σ = t'⁻¹ ∘ t` satisfies `t' ∘ σ = t`;
`wordRep σ⁻¹` carries `e_{t'}` to `e_t` and `S^{t'}` onto `S^t`, and the resulting twist of the
`S_n`-action by the inner automorphism of `σ` is undone by `ρ_V σ`.  Hence
`Occurs t V ↔ Occurs t' V`.
-/

namespace OAI.Saxl

open Equiv

attribute [local instance] Fintype.ofFinite

variable {n : ℕ} {μ : YoungDiagram}

/-- The position permutation with `t' ∘ σ = t`. -/
def shift (t t' : Tableau n μ) : Perm (Fin n) := t.trans t'.symm

theorem shift_apply (t t' : Tableau n μ) (i : Fin n) : shift t t' i = t'.symm (t i) := rfl

theorem apply_shift (t t' : Tableau n μ) (i : Fin n) : t' (shift t t' i) = t i := by
  simp [shift_apply]

theorem shift_inv (t t' : Tableau n μ) : (shift t t')⁻¹ = shift t' t := by
  ext i
  simp [shift, Perm.inv_def]

theorem rowWord_eq_comp (t t' : Tableau n μ) : rowWord t = rowWord t' ∘ shift t t' := by
  funext i
  apply Fin.ext
  simp [rowWord_apply, apply_shift]

/-- Column groups are conjugate: `g ∈ C_t ↔ σ g σ⁻¹ ∈ C_{t'}`. -/
theorem mem_columnGroup_conj (t t' : Tableau n μ) (g : Perm (Fin n)) :
    g ∈ columnGroup t ↔ shift t t' * g * (shift t t')⁻¹ ∈ columnGroup t' := by
  simp only [mem_columnGroup, Perm.mul_apply]
  constructor
  · intro h j
    have := h ((shift t t')⁻¹ j)
    rw [← apply_shift t t', ← apply_shift t t' ((shift t t')⁻¹ j)] at this
    simpa using this
  · intro h i
    have := h (shift t t' i)
    rw [Perm.inv_def, Equiv.symm_apply_apply] at this
    rwa [← apply_shift t t' (g i), ← apply_shift t t' i]

/-- Conjugation by `σ` as an equivalence `C_t ≃ C_{t'}`. -/
def conjEquiv (t t' : Tableau n μ) : columnGroup t ≃ columnGroup t' where
  toFun g := ⟨shift t t' * g * (shift t t')⁻¹, (mem_columnGroup_conj t t' g).1 g.2⟩
  invFun g' := ⟨(shift t t')⁻¹ * g' * shift t t', by
    rw [mem_columnGroup_conj t t']
    simpa [mul_assoc] using g'.2⟩
  left_inv g := by ext1; simp [mul_assoc]
  right_inv g' := by ext1; simp [mul_assoc]

theorem sign_conj (σ g : Perm (Fin n)) : Perm.sign (σ * g * σ⁻¹) = Perm.sign g := by
  rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, mul_comm, ← mul_assoc, Int.units_mul_self,
    one_mul]

/-- `e_t = σ⁻¹ • e_{t'}`. -/
theorem polytabloid_eq_wordRep (t t' : Tableau n μ) :
    polytabloid t = wordRep n (μ.colLen 0) (shift t t')⁻¹ (polytabloid t') := by
  rw [polytabloid_eq_sum, polytabloid_eq_sum, map_sum]
  apply Fintype.sum_equiv (conjEquiv t t')
  intro g
  simp only [conjEquiv, Equiv.coe_fn_mk, map_smul, wordRep_single, inv_inv, sign_conj]
  congr 2
  rw [rowWord_eq_comp t t']
  funext i
  simp

/-- `σ⁻¹ • S^{t'} ⊆ S^t`. -/
theorem wordRep_shift_mem (t t' : Tableau n μ) {x : WordSpace n (μ.colLen 0)}
    (hx : x ∈ Specht t') : wordRep n (μ.colLen 0) (shift t t')⁻¹ x ∈ Specht t := by
  refine Submodule.span_induction (p := fun x _ => wordRep n (μ.colLen 0) (shift t t')⁻¹ x ∈ Specht t)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨g, rfl⟩
    dsimp only
    rw [← Module.End.mul_apply, ← map_mul,
      show (shift t t')⁻¹ * g = ((shift t t')⁻¹ * g * shift t t') * (shift t t')⁻¹ by group,
      map_mul, Module.End.mul_apply, ← polytabloid_eq_wordRep]
    exact Submodule.subset_span ⟨_, rfl⟩
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- Transport an intertwiner out of `S^t` to one out of `S^{t'}`. -/
noncomputable def transport (t t' : Tableau n μ) {V : Type*} [AddCommMonoid V] [Module ℂ V]
    {ρ : Representation ℂ (Perm (Fin n)) V} (f : Representation.IntertwiningMap (spechtRep t) ρ) :
    Representation.IntertwiningMap (spechtRep t') ρ where
  toLinearMap := ρ (shift t t') ∘ₗ f.toLinearMap ∘ₗ
    (wordRep n (μ.colLen 0) (shift t t')⁻¹).restrict fun x hx => wordRep_shift_mem t t' hx
  isIntertwining' g := by
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.restrict_apply,
      Representation.IntertwiningMap.toLinearMap_apply]
    -- `σ⁻¹ (g y) = (σ⁻¹ g σ) (σ⁻¹ y)` inside `S^t`, then equivariance of `f`
    have h1 : (⟨wordRep n (μ.colLen 0) (shift t t')⁻¹ ((spechtRep t') g y),
        wordRep_shift_mem t t' ((spechtRep t') g y).2⟩ : Specht t) =
        (spechtRep t) ((shift t t')⁻¹ * g * shift t t')
          ⟨wordRep n (μ.colLen 0) (shift t t')⁻¹ y, wordRep_shift_mem t t' y.2⟩ := by
      apply Subtype.ext
      show wordRep n (μ.colLen 0) (shift t t')⁻¹ (wordRep n (μ.colLen 0) g y) =
        wordRep n (μ.colLen 0) ((shift t t')⁻¹ * g * shift t t') (wordRep n (μ.colLen 0) (shift t t')⁻¹ y)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [h1, Representation.IntertwiningMap.isIntertwining _ _ f, ← Module.End.mul_apply, ← map_mul,
      ← Module.End.mul_apply, ← map_mul]
    congr 2
    group

theorem transport_apply (t t' : Tableau n μ) {V : Type*} [AddCommMonoid V] [Module ℂ V]
    {ρ : Representation ℂ (Perm (Fin n)) V} (f : Representation.IntertwiningMap (spechtRep t) ρ)
    (y : Specht t') :
    transport t t' f y = ρ (shift t t')
      (f ⟨wordRep n (μ.colLen 0) (shift t t')⁻¹ y, wordRep_shift_mem t t' y.2⟩) := rfl

/-- **Occurrence depends only on the shape.** -/
theorem occurs_of_occurs (t t' : Tableau n μ) {V : Type*} [AddCommMonoid V] [Module ℂ V]
    {ρ : Representation ℂ (Perm (Fin n)) V} (h : Occurs t ρ) : Occurs t' ρ := by
  obtain ⟨f, hf⟩ := h
  refine ⟨transport t t' f, fun h0 => hf ?_⟩
  refine DFunLike.ext f 0 fun x => ?_
  -- `x = σ⁻¹ • (σ • x)` with `σ • x ∈ S^{t'}`
  have hx' : wordRep n (μ.colLen 0) (shift t t') x ∈ Specht t' := by
    have := wordRep_shift_mem t' t x.2
    rwa [shift_inv] at this
  have h1 := congrArg (fun k : Representation.IntertwiningMap (spechtRep t') ρ =>
    k ⟨_, hx'⟩) h0
  simp only [transport_apply] at h1
  have h2 : (⟨wordRep n (μ.colLen 0) (shift t t')⁻¹ (wordRep n (μ.colLen 0) (shift t t') x),
      wordRep_shift_mem t t' hx'⟩ : Specht t) = x := by
    apply Subtype.ext
    show wordRep n (μ.colLen 0) (shift t t')⁻¹ (wordRep n (μ.colLen 0) (shift t t') x) = x
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have h3 : ρ (shift t t') (f x) = 0 := by rw [h2] at h1; exact h1
  show f x = (0 : Representation.IntertwiningMap (spechtRep t) ρ) x
  have h4 := congrArg (ρ (shift t t')⁻¹) h3
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    map_zero] at h4
  exact h4

end OAI.Saxl
