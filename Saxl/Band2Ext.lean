import Mathlib
import Saxl.Band2Shift
import Saxl.Constituent

/-!
# Extension by zero along the band split

For `T : StripTableau a b (staircase (m - s)) (staircase m)`, a pair word on `a + b` positions is
*of extended form* (`IsExt s`) when its first `a` positions carry high pairs (both entries `≥ s`)
and its last `b` positions carry low pairs (both `< s`).  Such words are exactly
`extendPairS T hs w y` for `w` on `a` positions with letters shifted by `s` and `y` on the band with
letters `< s`.  `extLift T hs : WordSpaceL a (hi) ⊗ WordSpaceL b (lo) → WordSpaceL (a + b) L` sends
`f ⊗ g` to the function `f w * g y` on extended words and `0` elsewhere; it is injective
(`extBack` is a left inverse) and `S_a × S_b`-equivariant (`extLift_box`).
-/

namespace OAI.Saxl

open Equiv YoungDiagram Finset

open scoped TensorProduct

/-- Number of band letters, `(bandShape m s).colLen 0` (equal to `s` when `s ≤ m`). -/
abbrev dB (m s : ℕ) : ℕ := (bandShape m s).colLen 0

section swap

variable {m s a b : ℕ} (T : StripTableau a b (staircase (m - s)) (staircase m))

/-- The strip tableau with swapped coordinates. -/
def StripTableau.swapSTS : StripTableau a b (staircase (m - s)) (staircase m) where
  t := swapTableau T.t
  mem_nu i := by
    have h : ((T.t (Fin.castAdd b i)).val.1, (T.t (Fin.castAdd b i)).val.2) ∈ staircase (m - s) :=
      T.mem_nu i
    show ((T.t (Fin.castAdd b i)).val.2, (T.t (Fin.castAdd b i)).val.1) ∈ staircase (m - s)
    rw [mem_staircase] at h ⊢; omega
  not_mem_nu j := by
    have h : ((T.t (Fin.natAdd a j)).val.1, (T.t (Fin.natAdd a j)).val.2) ∉ staircase (m - s) :=
      T.not_mem_nu j
    show ((T.t (Fin.natAdd a j)).val.2, (T.t (Fin.natAdd a j)).val.1) ∉ staircase (m - s)
    rw [mem_staircase] at h ⊢; omega

theorem swapSTS_t : T.swapSTS.t = swapTableau T.t := rfl

theorem swapSTS_nuTableau : T.swapSTS.nuTableau (staircase_sub_le m s) =
    swapTableau (T.nuTableau (staircase_sub_le m s)) :=
  Equiv.ext fun i => Subtype.ext rfl

end swap

section ext

variable {m s a b : ℕ} (T : StripTableau a b (staircase (m - s)) (staircase m))

/-- The extended pair word. -/
def extendPairS (_T : StripTableau a b (staircase (m - s)) (staircase m)) (hs : s ≤ m)
    (w : Fin a → Fin (dR (m - s)) × Fin (dR (m - s)))
    (y : Fin b → Fin (dB m s) × Fin (dB m s)) : Fin (a + b) → Fin (dR m) × Fin (dR m) :=
  fun p => (extendS hs (Prod.fst ∘ w) (Prod.fst ∘ y) p, extendS hs (Prod.snd ∘ w) (Prod.snd ∘ y) p)

theorem extendS_comp_embPair (hs : s ≤ m) (v : Fin a → Fin (dR (m - s))) (y : Fin b → Fin (dB m s))
    (p : Perm (Fin a) × Perm (Fin b)) :
    extendS hs v y ∘ embPair p = extendS hs (v ∘ p.1) (y ∘ p.2) := by
  funext q
  apply Fin.ext
  refine Fin.addCases (fun i => ?_) (fun j => ?_) q
  · simp only [Function.comp_apply, embPair_castAdd, extendS_castAdd]
  · simp only [Function.comp_apply, embPair_natAdd, extendS_natAdd]

theorem extendPairS_comp_embPair (hs : s ≤ m) (w : Fin a → Fin (dR (m - s)) × Fin (dR (m - s)))
    (y : Fin b → Fin (dB m s) × Fin (dB m s)) (p : Perm (Fin a) × Perm (Fin b)) :
    extendPairS T hs w y ∘ embPair p = extendPairS T hs (w ∘ p.1) (y ∘ p.2) := by
  funext q
  simp only [Function.comp_apply, extendPairS]
  rw [← Function.comp_apply (f := extendS hs (Prod.fst ∘ w) (Prod.fst ∘ y)), extendS_comp_embPair,
    ← Function.comp_apply (f := extendS hs (Prod.snd ∘ w) (Prod.snd ∘ y)), extendS_comp_embPair]
  rfl

/-- Words of extended form: high on the first `a` positions, low on the band. -/
def IsExt (_T : StripTableau a b (staircase (m - s)) (staircase m))
    (u : Fin (a + b) → Fin (dR m) × Fin (dR m)) : Prop :=
  (∀ i, s ≤ ((u (Fin.castAdd b i)).1 : ℕ) ∧ s ≤ ((u (Fin.castAdd b i)).2 : ℕ)) ∧
  (∀ j, ((u (Fin.natAdd a j)).1 : ℕ) < s ∧ ((u (Fin.natAdd a j)).2 : ℕ) < s)

instance (u : Fin (a + b) → Fin (dR m) × Fin (dR m)) : Decidable (IsExt T u) := by
  unfold IsExt; infer_instance

/-- The high part of an extended word, letters shifted down by `s`. -/
def hiPart (u : Fin (a + b) → Fin (dR m) × Fin (dR m)) (h : IsExt T u) :
    Fin a → Fin (dR (m - s)) × Fin (dR (m - s)) := fun i =>
  (⟨((u (Fin.castAdd b i)).1 : ℕ) - s, by
      have := (u (Fin.castAdd b i)).1.2; have := (h.1 i).1
      have := dR_eq m; have := dR_eq (m - s); omega⟩,
   ⟨((u (Fin.castAdd b i)).2 : ℕ) - s, by
      have := (u (Fin.castAdd b i)).2.2; have := (h.1 i).2
      have := dR_eq m; have := dR_eq (m - s); omega⟩)

/-- The low part of an extended word. -/
def loPart (hs : s ≤ m) (u : Fin (a + b) → Fin (dR m) × Fin (dR m)) (h : IsExt T u) :
    Fin b → Fin (dB m s) × Fin (dB m s) := fun j =>
  (⟨((u (Fin.natAdd a j)).1 : ℕ), by rw [dB, colLen_bandShape m s hs]; exact (h.2 j).1⟩,
   ⟨((u (Fin.natAdd a j)).2 : ℕ), by rw [dB, colLen_bandShape m s hs]; exact (h.2 j).2⟩)

theorem isExt_extendPairS (hs : s ≤ m) (w : Fin a → Fin (dR (m - s)) × Fin (dR (m - s)))
    (y : Fin b → Fin (dB m s) × Fin (dB m s)) : IsExt T (extendPairS T hs w y) := by
  refine ⟨fun i => ?_, fun j => ?_⟩
  · simp only [extendPairS, extendS_castAdd]; omega
  · have h1 := (y j).1.2; have h2 := (y j).2.2
    have := colLen_bandShape m s hs
    simp only [extendPairS, extendS_natAdd]; omega

theorem hiPart_extendPairS (hs : s ≤ m) (w : Fin a → Fin (dR (m - s)) × Fin (dR (m - s)))
    (y : Fin b → Fin (dB m s) × Fin (dB m s)) :
    hiPart T (extendPairS T hs w y) (isExt_extendPairS T hs w y) = w := by
  funext i
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · show ((extendPairS T hs w y (Fin.castAdd b i)).1 : ℕ) - s = ((w i).1 : ℕ)
    simp only [extendPairS, extendS_castAdd, Function.comp_apply]; omega
  · show ((extendPairS T hs w y (Fin.castAdd b i)).2 : ℕ) - s = ((w i).2 : ℕ)
    simp only [extendPairS, extendS_castAdd, Function.comp_apply]; omega

theorem loPart_extendPairS (hs : s ≤ m) (w : Fin a → Fin (dR (m - s)) × Fin (dR (m - s)))
    (y : Fin b → Fin (dB m s) × Fin (dB m s)) :
    loPart T hs (extendPairS T hs w y) (isExt_extendPairS T hs w y) = y := by
  funext j
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · show ((extendPairS T hs w y (Fin.natAdd a j)).1 : ℕ) = ((y j).1 : ℕ)
    simp only [extendPairS, extendS_natAdd]; rfl
  · show ((extendPairS T hs w y (Fin.natAdd a j)).2 : ℕ) = ((y j).2 : ℕ)
    simp only [extendPairS, extendS_natAdd]; rfl

theorem extendPairS_hiPart_loPart (hs : s ≤ m) {u : Fin (a + b) → Fin (dR m) × Fin (dR m)} (h : IsExt T u) :
    extendPairS T hs (hiPart T u h) (loPart T hs u h) = u := by
  funext p
  refine Fin.addCases (fun i => ?_) (fun j => ?_) p
  · refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show ((extendS hs _ _ (Fin.castAdd b i) : ℕ)) = _
      rw [extendS_castAdd]
      show ((u (Fin.castAdd b i)).1 : ℕ) - s + s = _
      have := (h.1 i).1; omega
    · show ((extendS hs _ _ (Fin.castAdd b i) : ℕ)) = _
      rw [extendS_castAdd]
      show ((u (Fin.castAdd b i)).2 : ℕ) - s + s = _
      have := (h.1 i).2; omega
  · refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show ((extendS hs _ _ (Fin.natAdd a j) : ℕ)) = _
      rw [extendS_natAdd]; rfl
    · show ((extendS hs _ _ (Fin.natAdd a j) : ℕ)) = _
      rw [extendS_natAdd]; rfl

theorem isExt_comp_embPair (u : Fin (a + b) → Fin (dR m) × Fin (dR m))
    (p : Perm (Fin a) × Perm (Fin b)) : IsExt T (u ∘ embPair p) ↔ IsExt T u := by
  unfold IsExt
  simp only [Function.comp_apply, embPair_castAdd, embPair_natAdd]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => by simpa using h1 (p.1.symm i), fun j => by simpa using h2 (p.2.symm j)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => h1 _, fun j => h2 _⟩

theorem hiPart_comp_embPair (u : Fin (a + b) → Fin (dR m) × Fin (dR m))
    (p : Perm (Fin a) × Perm (Fin b)) (h : IsExt T u) :
    hiPart T (u ∘ embPair p) ((isExt_comp_embPair T u p).2 h) = hiPart T u h ∘ p.1 := by
  funext i
  simp only [hiPart, Function.comp_apply, embPair_castAdd]

theorem loPart_comp_embPair (hs : s ≤ m) (u : Fin (a + b) → Fin (dR m) × Fin (dR m))
    (p : Perm (Fin a) × Perm (Fin b)) (h : IsExt T u) :
    loPart T hs (u ∘ embPair p) ((isExt_comp_embPair T u p).2 h) = loPart T hs u h ∘ p.2 := by
  funext j
  simp only [loPart, Function.comp_apply, embPair_natAdd]

/-- `(f, g) ↦ (u ↦ f w * g y)` on extended words `u = extendPairS w y`, zero elsewhere. -/
noncomputable def extMul (hs : s ≤ m) : WordSpaceL a (Fin (dR (m - s)) × Fin (dR (m - s))) →ₗ[ℂ]
    WordSpaceL b (Fin (dB m s) × Fin (dB m s)) →ₗ[ℂ] WordSpaceL (a + b) (Fin (dR m) × Fin (dR m)) where
  toFun f :=
    { toFun := fun g u => if h : IsExt T u then f (hiPart T u h) * g (loPart T hs u h) else 0
      map_add' := fun g g' => funext fun u => by
        show (if h : IsExt T u then f (hiPart T u h) * (g + g') (loPart T hs u h) else 0) =
          (if h : IsExt T u then f (hiPart T u h) * g (loPart T hs u h) else 0) +
          (if h : IsExt T u then f (hiPart T u h) * g' (loPart T hs u h) else 0)
        split_ifs <;> simp [mul_add]
      map_smul' := fun c g => funext fun u => by
        show (if h : IsExt T u then f (hiPart T u h) * (c • g) (loPart T hs u h) else 0) =
          c • (if h : IsExt T u then f (hiPart T u h) * g (loPart T hs u h) else 0)
        split_ifs <;> simp [mul_left_comm] }
  map_add' f f' := LinearMap.ext fun g => funext fun u => by
    show (if h : IsExt T u then (f + f') (hiPart T u h) * g (loPart T hs u h) else 0) =
      (if h : IsExt T u then f (hiPart T u h) * g (loPart T hs u h) else 0) +
      (if h : IsExt T u then f' (hiPart T u h) * g (loPart T hs u h) else 0)
    split_ifs <;> simp [add_mul]
  map_smul' c f := LinearMap.ext fun g => funext fun u => by
    show (if h : IsExt T u then (c • f) (hiPart T u h) * g (loPart T hs u h) else 0) =
      c • (if h : IsExt T u then f (hiPart T u h) * g (loPart T hs u h) else 0)
    split_ifs <;> simp [mul_assoc]

theorem extMul_apply (hs : s ≤ m) (f : WordSpaceL a (Fin (dR (m - s)) × Fin (dR (m - s))))
    (g : WordSpaceL b (Fin (dB m s) × Fin (dB m s))) (u : Fin (a + b) → Fin (dR m) × Fin (dR m)) :
    extMul T hs f g u = if h : IsExt T u then f (hiPart T u h) * g (loPart T hs u h) else 0 := rfl

theorem extMul_apply_ext (hs : s ≤ m) (f : WordSpaceL a (Fin (dR (m - s)) × Fin (dR (m - s))))
    (g : WordSpaceL b (Fin (dB m s) × Fin (dB m s))) (w : Fin a → Fin (dR (m - s)) × Fin (dR (m - s)))
    (y : Fin b → Fin (dB m s) × Fin (dB m s)) :
    extMul T hs f g (extendPairS T hs w y) = f w * g y := by
  rw [extMul_apply, dif_pos (isExt_extendPairS T hs w y), hiPart_extendPairS, loPart_extendPairS]

theorem extMul_apply_of_not (hs : s ≤ m) (f : WordSpaceL a (Fin (dR (m - s)) × Fin (dR (m - s))))
    (g : WordSpaceL b (Fin (dB m s) × Fin (dB m s))) {u : Fin (a + b) → Fin (dR m) × Fin (dR m)}
    (hu : ¬ IsExt T u) : extMul T hs f g u = 0 := by
  rw [extMul_apply, dif_neg hu]

/-- Extension by zero along the band split, on the tensor product. -/
noncomputable def extLift (hs : s ≤ m) : WordSpaceL a (Fin (dR (m - s)) × Fin (dR (m - s))) ⊗[ℂ]
    WordSpaceL b (Fin (dB m s) × Fin (dB m s)) →ₗ[ℂ] WordSpaceL (a + b) (Fin (dR m) × Fin (dR m)) :=
  TensorProduct.lift (extMul T hs)

theorem extLift_tmul (hs : s ≤ m) (f : WordSpaceL a (Fin (dR (m - s)) × Fin (dR (m - s))))
    (g : WordSpaceL b (Fin (dB m s) × Fin (dB m s))) : extLift T hs (f ⊗ₜ g) = extMul T hs f g := rfl

/-- Basis expansion of a word-space vector (any letter type). -/
theorem eq_sum_single' {n : ℕ} {L : Type} [Fintype L] [DecidableEq L] (u : WordSpaceL n L) :
    u = ∑ w, u w • (Pi.single w 1 : WordSpaceL n L) := by
  ext a
  rw [Finset.sum_apply, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- A left inverse of `extLift`: read off the coefficients on extended words. -/
noncomputable def extBack (T : StripTableau a b (staircase (m - s)) (staircase m)) (hs : s ≤ m) :
    WordSpaceL (a + b) (Fin (dR m) × Fin (dR m)) →ₗ[ℂ]
    WordSpaceL a (Fin (dR (m - s)) × Fin (dR (m - s))) ⊗[ℂ] WordSpaceL b (Fin (dB m s) × Fin (dB m s)) where
  toFun F := ∑ w, ∑ y, F (extendPairS T hs w y) •
    ((Pi.single w 1 : WordSpaceL a _) ⊗ₜ (Pi.single y 1 : WordSpaceL b _))
  map_add' F F' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c F := by simp [smul_smul, Finset.smul_sum]

theorem extBack_extLift (hs : s ≤ m) (x : WordSpaceL a (Fin (dR (m - s)) × Fin (dR (m - s))) ⊗[ℂ]
    WordSpaceL b (Fin (dB m s) × Fin (dB m s))) : extBack T hs (extLift T hs x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    rw [extLift_tmul]
    show (∑ w, ∑ y, extMul T hs f g (extendPairS T hs w y) • _) = _
    simp_rw [extMul_apply_ext]
    calc (∑ w, ∑ y, (f w * g y) •
            ((Pi.single w 1 : WordSpaceL a _) ⊗ₜ[ℂ] (Pi.single y 1 : WordSpaceL b _)))
        = (∑ w, f w • (Pi.single w 1 : WordSpaceL a _)) ⊗ₜ[ℂ]
            (∑ y, g y • (Pi.single y 1 : WordSpaceL b _)) := by
          rw [TensorProduct.sum_tmul]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [TensorProduct.tmul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul, mul_comm]
      _ = f ⊗ₜ[ℂ] g := by rw [← eq_sum_single', ← eq_sum_single']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem extLift_injective (hs : s ≤ m) : Function.Injective (extLift T hs) :=
  Function.LeftInverse.injective (extBack_extLift T hs)

/-- `extLift` is `S_a × S_b`-equivariant. -/
theorem extLift_box (hs : s ≤ m) (p : Perm (Fin a) × Perm (Fin b))
    (x : WordSpaceL a (Fin (dR (m - s)) × Fin (dR (m - s))) ⊗[ℂ] WordSpaceL b (Fin (dB m s) × Fin (dB m s))) :
    extLift T hs (boxTensor (wordRepL a _) (wordRepL b _) p x) =
      wordRepL (a + b) _ (embPair p) (extLift T hs x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    rw [boxTensor_tmul, extLift_tmul, extLift_tmul]
    funext u
    rw [wordRepL_apply, extMul_apply, extMul_apply]
    by_cases h : IsExt T u
    · rw [dif_pos h, dif_pos ((isExt_comp_embPair T u p).2 h), hiPart_comp_embPair,
        loPart_comp_embPair]
      rfl
    · rw [dif_neg h, dif_neg (fun h' => h ((isExt_comp_embPair T u p).1 h'))]
  | add x y hx hy => simp only [map_add, hx, hy]

end ext

end OAI.Saxl
