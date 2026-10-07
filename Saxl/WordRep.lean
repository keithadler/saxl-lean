import Mathlib
import Saxl.Statement
import Saxl.Polytabloid

/-!
# Word representations over an arbitrary letter type

`WordSpaceL n L = (Fin n → L) → ℂ` with the position action `(g • f) a = f (a ∘ g)`.  The
challenge's `WordSpace n d` is the case `L = Fin d` (definitionally).  We add

* `letterPush q` : pushforward along a letter map `q : L → L'`, equivariant;
* `pairLift` : the equivariant map `WordSpaceL n L ⊗ WordSpaceL n L' → WordSpaceL n (L × L')`,
  `e_w ⊗ e_{w'} ↦ e_{(w, w')}`, which lets us compute in the "pair-letter" model of `E^{⊗B} ⊗ E^{⊗B}`.
-/

namespace OAI.Saxl

open Equiv

/-- Word space over an arbitrary finite letter type. -/
abbrev WordSpaceL (n : ℕ) (L : Type) := (Fin n → L) → ℂ

/-- The position action. -/
def wordRepL (n : ℕ) (L : Type) : Representation ℂ (Perm (Fin n)) (WordSpaceL n L) where
  toFun g :=
    { toFun := fun f a => f (a ∘ g)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f a; rfl
  map_mul' g h := by ext f a; rfl

theorem wordRepL_apply {n : ℕ} {L : Type} (g : Perm (Fin n)) (f : WordSpaceL n L) (a : Fin n → L) :
    wordRepL n L g f a = f (a ∘ g) := rfl

theorem wordRepL_eq_wordRep (n d : ℕ) : wordRepL n (Fin d) = wordRep n d := rfl

theorem wordRepL_single {n : ℕ} {L : Type} [DecidableEq L] (g : Perm (Fin n)) (w : Fin n → L) :
    wordRepL n L g (Pi.single w (1 : ℂ)) = Pi.single (w ∘ ⇑(g⁻¹ : Perm (Fin n))) 1 := by
  ext a
  rw [wordRepL_apply]
  by_cases h : a ∘ g = w
  · have h' : a = w ∘ ⇑(g⁻¹ : Perm (Fin n)) := by
      rw [← h]; ext i; simp
    rw [h, h', Pi.single_eq_same, Pi.single_eq_same]
  · have h' : a ≠ w ∘ ⇑(g⁻¹ : Perm (Fin n)) := fun h' => h (by rw [h']; ext i; simp)
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

section letterPush

variable {n : ℕ} {L L' : Type} [Fintype L] [DecidableEq L] [DecidableEq L'] (q : L → L')

/-- Pushforward along a letter map. -/
def letterPush : WordSpaceL n L →ₗ[ℂ] WordSpaceL n L' where
  toFun f u' := ∑ u, if q ∘ u = u' then f u else 0
  map_add' f g := by
    funext u'
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs <;> simp
  map_smul' c f := by
    funext u'
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs <;> simp

theorem letterPush_apply (f : WordSpaceL n L) (u' : Fin n → L') :
    letterPush q f u' = ∑ u, if q ∘ u = u' then f u else 0 := rfl

theorem letterPush_single (w : Fin n → L) :
    letterPush q (Pi.single w 1) = Pi.single (q ∘ w) 1 := by
  funext u'
  rw [letterPush_apply, Finset.sum_eq_single w]
  · simp only [Pi.single_eq_same]
    by_cases h : q ∘ w = u'
    · rw [if_pos h, h, Pi.single_eq_same]
    · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h)]
  · intro u _ hu; simp [Pi.single_eq_of_ne hu]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Pushforward is equivariant. -/
theorem letterPush_wordRepL (g : Perm (Fin n)) (f : WordSpaceL n L) :
    letterPush q (wordRepL n L g f) = wordRepL n L' g (letterPush q f) := by
  funext u'
  rw [wordRepL_apply, letterPush_apply, letterPush_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr g.symm (Equiv.refl L)) _ _ fun u => ?_
  have h1 : (Equiv.arrowCongr g.symm (Equiv.refl L)) u = u ∘ g := rfl
  rw [h1, wordRepL_apply]
  have h2 : (q ∘ u ∘ ⇑g = u' ∘ ⇑g) ↔ (q ∘ u = u') := by
    constructor
    · intro h; funext i
      have := congrFun h (g.symm i)
      simpa using this
    · intro h; rw [← h]; rfl
  by_cases h : q ∘ u = u'
  · rw [if_pos h, if_pos (h2.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (h2.1 h'))]

end letterPush

section pair

variable {n : ℕ} {L L' : Type} [DecidableEq L] [DecidableEq L']

open scoped TensorProduct

/-- The bilinear pointwise product landing in the pair-letter space. -/
def pairMul : WordSpaceL n L →ₗ[ℂ] WordSpaceL n L' →ₗ[ℂ] WordSpaceL n (L × L') where
  toFun f :=
    { toFun := fun g u => f (Prod.fst ∘ u) * g (Prod.snd ∘ u)
      map_add' := fun g g' => by funext u; simp [mul_add]
      map_smul' := fun c g => by funext u; simp [mul_left_comm] }
  map_add' f f' := by ext g u; simp [add_mul]
  map_smul' c f := by ext g u; simp [mul_assoc]

theorem pairMul_apply (f : WordSpaceL n L) (g : WordSpaceL n L') (u : Fin n → L × L') :
    pairMul f g u = f (Prod.fst ∘ u) * g (Prod.snd ∘ u) := rfl

/-- `e_w ⊗ e_{w'} ↦ e_{(w, w')}`. -/
noncomputable def pairLift : WordSpaceL n L ⊗[ℂ] WordSpaceL n L' →ₗ[ℂ] WordSpaceL n (L × L') :=
  TensorProduct.lift pairMul

theorem pairLift_tmul (f : WordSpaceL n L) (g : WordSpaceL n L') :
    pairLift (f ⊗ₜ g) = pairMul f g := rfl

theorem pairMul_single (w : Fin n → L) (w' : Fin n → L') :
    pairMul (Pi.single w (1 : ℂ)) (Pi.single w' 1) = Pi.single (fun i => (w i, w' i)) 1 := by
  funext u
  rw [pairMul_apply]
  by_cases h : u = fun i => (w i, w' i)
  · subst h
    simp [Function.comp_def]
  · rw [Pi.single_eq_of_ne h]
    have : ¬ (Prod.fst ∘ u = w ∧ Prod.snd ∘ u = w') := by
      rintro ⟨h1, h2⟩
      apply h
      funext i
      exact Prod.ext (congrFun h1 i) (congrFun h2 i)
    rcases not_and_or.1 this with h1 | h1
    · rw [Pi.single_eq_of_ne h1, zero_mul]
    · rw [Pi.single_eq_of_ne h1, mul_zero]

/-- `pairLift` is equivariant for the diagonal action. -/
theorem pairLift_tprod (g : Perm (Fin n)) (x : WordSpaceL n L ⊗[ℂ] WordSpaceL n L') :
    pairLift ((wordRepL n L).tprod (wordRepL n L') g x) = wordRepL n (L × L') g (pairLift x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f f' =>
    rw [Representation.tprod_apply, TensorProduct.map_tmul, pairLift_tmul, pairLift_tmul]
    funext u
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end pair

end OAI.Saxl
