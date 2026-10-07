import Mathlib
import Saxl.Statement

/-!
# Polytabloids in the word space

Basic facts about the challenge's `polytabloid t`:
* `wordRep_single` : the position action permutes basis words, `g • e_w = e_{w ∘ g⁻¹}`;
* `polytabloid_apply_rowWord` : the coefficient of `polytabloid t` at its own row word is `1`,
  so `polytabloid_ne_zero`;
* `wordRep_polytabloid` : column permutations act on the polytabloid by their sign.
-/

namespace OAI.Saxl

open Equiv

attribute [local instance] Fintype.ofFinite

variable {n d : ℕ}

/-- Unfolding the position action: `(g • f) a = f (a ∘ g)`. -/
theorem wordRep_apply (g : Perm (Fin n)) (f : WordSpace n d) (a : Fin n → Fin d) :
    wordRep n d g f a = f (a ∘ g) := rfl

/-- The position action permutes basis words: `g • e_w = e_{w ∘ g⁻¹}`. -/
theorem wordRep_single (g : Perm (Fin n)) (w : Fin n → Fin d) :
    wordRep n d g (Pi.single w (1 : ℂ)) = Pi.single (w ∘ (g⁻¹ : Perm (Fin n))) 1 := by
  ext a
  rw [wordRep_apply]
  by_cases h : a ∘ g = w
  · have h' : a = w ∘ (g⁻¹ : Perm (Fin n)) := by
      rw [← h]; ext i; simp
    rw [h, h', Pi.single_eq_same, Pi.single_eq_same]
  · have h' : a ≠ w ∘ (g⁻¹ : Perm (Fin n)) := fun h' => h (by rw [h']; ext i; simp)
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

variable {μ : YoungDiagram} (t : Tableau n μ)

/-- The row word records the row index of each position's cell. -/
theorem rowWord_apply (i : Fin n) : (rowWord t i : ℕ) = (t i).val.1 := rfl

/-- Unfolding membership in the column group. -/
theorem mem_columnGroup {g : Perm (Fin n)} :
    g ∈ columnGroup t ↔ ∀ i, (t (g i)).val.2 = (t i).val.2 := Iff.rfl

/-- A column permutation preserving every row is the identity. -/
theorem eq_one_of_mem_columnGroup_of_rowWord {g : Perm (Fin n)} (hg : g ∈ columnGroup t)
    (hr : rowWord t ∘ g = rowWord t) : g = 1 := by
  refine Equiv.ext fun i => ?_
  have h2 := (mem_columnGroup t).1 hg i
  have h1 : (t (g i)).val.1 = (t i).val.1 := by
    have := congrFun hr i
    simp only [Function.comp_apply] at this
    exact congrArg Fin.val this
  have : t (g i) = t i := Subtype.ext (Prod.ext h1 h2)
  rw [Perm.one_apply]
  exact t.injective this

/-- `polytabloid t` as a signed sum of basis words. -/
theorem polytabloid_eq_sum :
    polytabloid t = ∑ g : columnGroup t,
      (((Perm.sign (g : Perm (Fin n))) : ℤ) : ℂ) •
        Pi.single (rowWord t ∘ ((g : Perm (Fin n))⁻¹ : Perm (Fin n))) 1 := by
  unfold polytabloid
  simp only [wordRep_single]

/-- The coefficient of `polytabloid t` at its own row word is `1`. -/
theorem polytabloid_apply_rowWord : polytabloid t (rowWord t) = 1 := by
  rw [polytabloid_eq_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single (1 : columnGroup t)]
  · simp
  · intro g _ hg
    have hne : rowWord t ∘ ((g : Perm (Fin n))⁻¹ : Perm (Fin n)) ≠ rowWord t := by
      intro h
      apply hg
      have h1 : (g : Perm (Fin n))⁻¹ ∈ columnGroup t := (columnGroup t).inv_mem g.2
      have := eq_one_of_mem_columnGroup_of_rowWord t h1 h
      ext1
      simpa using congrArg (·⁻¹) this
    rw [Pi.smul_apply, Pi.single_eq_of_ne hne.symm, smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Polytabloids are nonzero. -/
theorem polytabloid_ne_zero : polytabloid t ≠ 0 := fun h => by
  have := polytabloid_apply_rowWord t
  rw [h] at this
  simp at this

/-- Column permutations act on the polytabloid by their sign. -/
theorem wordRep_polytabloid {g : Perm (Fin n)} (hg : g ∈ columnGroup t) :
    wordRep n (μ.colLen 0) g (polytabloid t) =
      (((Perm.sign g) : ℤ) : ℂ) • polytabloid t := by
  rw [polytabloid_eq_sum, map_sum, Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : columnGroup t))
  intro y
  simp only [Equiv.coe_mulLeft, map_smul, wordRep_single, smul_smul, Subgroup.coe_mul,
    mul_inv_rev, Perm.sign_mul, Units.val_mul, Int.cast_mul, Perm.coe_mul, Function.comp_assoc]
  have hs : ((Perm.sign g : ℤ) : ℂ) * ((Perm.sign g : ℤ) : ℂ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [← mul_assoc, hs, one_mul]

end OAI.Saxl
