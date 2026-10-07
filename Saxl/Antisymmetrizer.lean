import Mathlib
import Saxl.Statement
import Saxl.Polytabloid

/-!
# The column antisymmetriser and the Hermitian form on the word space

`kappa t d = Σ_{g ∈ C_t} sign g • wordRep g` on `WordSpace n d`.  Facts:
* `kappa_single_rowWord` : `κ_t {t} = e_t`;
* `kappa_wordRep` : `κ_t ∘ g = sign g • κ_t` for `g ∈ C_t`;
* `kappa_single_eq_zero` : `κ_t e_w = 0` when `w` repeats a letter inside a column of `t`;
* `form` : the standard Hermitian form, `S_n`-invariant, with `κ_t` self-adjoint and `form` definite.
-/

namespace OAI.Saxl

open Equiv

attribute [local instance] Fintype.ofFinite

variable {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)

/-- The column antisymmetriser `κ_t = Σ_{g ∈ C_t} sign g · g`. -/
noncomputable def kappa (d : ℕ) : WordSpace n d →ₗ[ℂ] WordSpace n d :=
  ∑ g : columnGroup t, (((Perm.sign (g : Perm (Fin n))) : ℤ) : ℂ) • wordRep n d (g : Perm (Fin n))

theorem kappa_apply (v : WordSpace n d) :
    kappa t d v = ∑ g : columnGroup t,
      (((Perm.sign (g : Perm (Fin n))) : ℤ) : ℂ) • wordRep n d (g : Perm (Fin n)) v := by
  simp [kappa, LinearMap.sum_apply]

theorem kappa_single_rowWord :
    kappa t (μ.colLen 0) (Pi.single (rowWord t) 1) = polytabloid t := by
  rw [kappa_apply]; rfl

theorem sign_sq (g : Perm (Fin n)) :
    ((Perm.sign g : ℤ) : ℂ) * ((Perm.sign g : ℤ) : ℂ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

/-- Column permutations on the right: `κ_t ∘ g = sign g • κ_t`. -/
theorem kappa_wordRep {g : Perm (Fin n)} (hg : g ∈ columnGroup t) (v : WordSpace n d) :
    kappa t d (wordRep n d g v) = ((Perm.sign g : ℤ) : ℂ) • kappa t d v := by
  rw [kappa_apply, kappa_apply, Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.mulRight (⟨g, hg⟩ : columnGroup t))
  intro y
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul,
    Units.val_mul, Int.cast_mul]
  congr 1
  rw [mul_comm, mul_assoc, sign_sq, mul_one]

/-- A word repeating a letter inside a column of `t` is killed by `κ_t`. -/
theorem kappa_single_eq_zero {w : Fin n → Fin d} {i j : Fin n} (hij : i ≠ j)
    (hcol : (t i).val.2 = (t j).val.2) (hw : w i = w j) :
    kappa t d (Pi.single w 1) = 0 := by
  have hs : swap i j ∈ columnGroup t := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [swap_apply_left, hcol]
    by_cases hk' : k = j
    · subst hk'; simp [swap_apply_right, hcol]
    simp [swap_apply_of_ne_of_ne hk hk']
  have h1 : wordRep n d (swap i j) (Pi.single w (1 : ℂ)) = Pi.single w 1 := by
    rw [wordRep_single]
    congr 1
    ext k
    simp only [Function.comp_apply, swap_inv]
    by_cases hk : k = i
    · subst hk; simp [swap_apply_left, hw]
    by_cases hk' : k = j
    · subst hk'; simp [swap_apply_right, hw]
    simp [swap_apply_of_ne_of_ne hk hk']
  have h2 := kappa_wordRep t hs (Pi.single w (1 : ℂ))
  rw [h1, Perm.sign_swap hij] at h2
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_smul, one_smul] at h2
  exact self_eq_neg.1 h2

/-! ### The Hermitian form -/

/-- Standard Hermitian form on the word space, antilinear in the first slot. -/
noncomputable def form (u v : WordSpace n d) : ℂ := ∑ w, star (u w) * v w

theorem form_add_left (u u' v : WordSpace n d) : form (u + u') v = form u v + form u' v := by
  simp [form, add_mul, Finset.sum_add_distrib]

theorem form_smul_left (c : ℂ) (u v : WordSpace n d) : form (c • u) v = star c * form u v := by
  simp [form, Finset.mul_sum, mul_assoc]

theorem form_add_right (u v v' : WordSpace n d) : form u (v + v') = form u v + form u v' := by
  simp [form, mul_add, Finset.sum_add_distrib]

theorem form_smul_right (c : ℂ) (u v : WordSpace n d) : form u (c • v) = c * form u v := by
  simp [form, Finset.mul_sum, mul_left_comm]

theorem form_sum_left {ι : Type*} (s : Finset ι) (f : ι → WordSpace n d) (v : WordSpace n d) :
    form (∑ i ∈ s, f i) v = ∑ i ∈ s, form (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [form]
  | insert a s ha ih => rw [Finset.sum_insert ha, form_add_left, ih, Finset.sum_insert ha]

theorem form_sum_right {ι : Type*} (s : Finset ι) (u : WordSpace n d) (f : ι → WordSpace n d) :
    form u (∑ i ∈ s, f i) = ∑ i ∈ s, form u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [form]
  | insert a s ha ih => rw [Finset.sum_insert ha, form_add_right, ih, Finset.sum_insert ha]

/-- The position action is unitary for `form`. -/
theorem form_wordRep (g : Perm (Fin n)) (u v : WordSpace n d) :
    form (wordRep n d g u) (wordRep n d g v) = form u v := by
  unfold form
  exact Fintype.sum_equiv (Equiv.arrowCongr g.symm (Equiv.refl (Fin d))) _ _
    fun w => rfl

theorem form_wordRep_left (g : Perm (Fin n)) (u v : WordSpace n d) :
    form (wordRep n d g u) v = form u (wordRep n d g⁻¹ v) := by
  conv_lhs => rw [← form_wordRep g⁻¹]
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- `κ_t` is self-adjoint for `form`. -/
theorem form_kappa (u v : WordSpace n d) : form (kappa t d u) v = form u (kappa t d v) := by
  rw [kappa_apply, kappa_apply, form_sum_left, form_sum_right]
  apply Fintype.sum_equiv (Equiv.inv (columnGroup t))
  intro g
  rw [form_smul_left, form_smul_right, form_wordRep_left, star_intCast]
  simp only [Equiv.inv_apply, Subgroup.coe_inv, Perm.sign_inv]

/-- Definiteness: `form u u = 0 → u = 0`. -/
theorem eq_zero_of_form_self_eq_zero {u : WordSpace n d} (h : form u u = 0) : u = 0 := by
  unfold form at h
  have h' : ∑ w, (Complex.normSq (u w) : ℂ) = 0 := by
    rw [← h]
    exact Finset.sum_congr rfl fun w _ => by rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at h'
  rw [Finset.sum_eq_zero_iff_of_nonneg fun w _ => Complex.normSq_nonneg _] at h'
  ext w
  exact Complex.normSq_eq_zero.1 (h' w (Finset.mem_univ _))

end OAI.Saxl
