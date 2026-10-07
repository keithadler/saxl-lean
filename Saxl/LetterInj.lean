import Mathlib
import Saxl.Orbit
import Saxl.CastN

/-!
# Transport of occurrence for cyclic word modules

* `occurs_letterPush` : along an injective letter map `q`, `ℂ[S_n] e_w → ℂ[S_n] e_{q ∘ w}`;
* `occurs_cycG_castN` : along a position bijection `e : Fin n ≃ Fin n'`,
  `ℂ[S_n] e_w → ℂ[S_{n'}] e_{w ∘ e.symm}`.
-/

namespace OAI.Saxl

open Equiv

section inj

variable {n : ℕ} {L L' : Type} [Fintype L] [DecidableEq L] [DecidableEq L'] (q : L → L')
  (hq : Function.Injective q)

include hq in
theorem letterPush_apply_comp (f : WordSpaceL n L) (w : Fin n → L) :
    letterPush q f (q ∘ w) = f w := by
  rw [letterPush_apply, Finset.sum_eq_single w]
  · simp
  · intro u _ hu
    rw [if_neg]
    intro h; apply hu
    funext i; exact hq (congrFun h i)
  · intro h; exact absurd (Finset.mem_univ _) h

include hq in
theorem letterPush_injective : Function.Injective (letterPush (n := n) q) := by
  intro f g h
  funext w
  rw [← letterPush_apply_comp q hq f w, ← letterPush_apply_comp q hq g w, h]

theorem letterPush_mem_cycG (w : Fin n → L) {x : WordSpaceL n L}
    (hx : x ∈ cycG (wordRepL n L) (Pi.single w 1)) :
    letterPush q x ∈ cycG (wordRepL n L') (Pi.single (q ∘ w) 1) := by
  rw [mem_cycG_iff] at hx
  refine Submodule.span_induction
    (p := fun x _ => letterPush q x ∈ cycG (wordRepL n L') (Pi.single (q ∘ w) 1)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨g, rfl⟩
    dsimp only
    rw [letterPush_wordRepL, letterPush_single]
    exact Submodule.subset_span ⟨g, rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx

include hq in
/-- Occurrence transports along an injective letter map. -/
theorem occurs_letterPush {μ : YoungDiagram} (t : Tableau n μ) (w : Fin n → L)
    (h : Occurs t (cycG (wordRepL n L) (Pi.single w 1)).toRepresentation) :
    Occurs t (cycG (wordRepL n L') (Pi.single (q ∘ w) 1)).toRepresentation := by
  obtain ⟨f, hf⟩ := h
  let R : Representation.IntertwiningMap (cycG (wordRepL n L) (Pi.single w 1)).toRepresentation
      (cycG (wordRepL n L') (Pi.single (q ∘ w) 1)).toRepresentation :=
    { toLinearMap := (letterPush q).restrict fun x hx => letterPush_mem_cycG q w hx
      isIntertwining' := fun g => LinearMap.ext fun x => Subtype.ext (letterPush_wordRepL q g x) }
  refine ⟨R.comp f, fun h0 => hf ?_⟩
  refine DFunLike.ext f 0 fun x => ?_
  have h1 : (R.comp f) x = 0 := by rw [h0]; rfl
  rw [Representation.IntertwiningMap.comp_apply] at h1
  have h2 : letterPush q (f x : WordSpaceL n L) = 0 := congrArg Subtype.val h1
  have h3 : (f x : WordSpaceL n L) = 0 := letterPush_injective q hq (by rw [h2, map_zero])
  exact Subtype.ext h3

end inj

section cast

variable {n n' : ℕ} (e : Fin n ≃ Fin n') {L : Type} [DecidableEq L]

theorem wordCast_mem_cycG (w : Fin n → L) {x : WordSpaceL n L}
    (hx : x ∈ cycG (wordRepL n L) (Pi.single w 1)) :
    wordCast e x ∈ cycG (wordRepL n' L) (Pi.single (w ∘ e.symm) 1) := by
  rw [mem_cycG_iff] at hx
  refine Submodule.span_induction
    (p := fun x _ => wordCast e x ∈ cycG (wordRepL n' L) (Pi.single (w ∘ e.symm) 1)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨g, rfl⟩
    dsimp only
    rw [wordCast_wordRepL, wordCast_single]
    exact Submodule.subset_span ⟨permHom e g, rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- Occurrence in a cyclic word module transports along a position bijection. -/
theorem occurs_cycG_castN {μ : YoungDiagram} (t : Tableau n μ) (w : Fin n → L)
    (h : Occurs t (cycG (wordRepL n L) (Pi.single w 1)).toRepresentation) :
    Occurs (castTableau e t) (cycG (wordRepL n' L) (Pi.single (w ∘ e.symm) 1)).toRepresentation := by
  apply occurs_castN e t
  obtain ⟨f, hf⟩ := h
  let R : Representation.IntertwiningMap (cycG (wordRepL n L) (Pi.single w 1)).toRepresentation
      (pullback e (cycG (wordRepL n' L) (Pi.single (w ∘ e.symm) 1)).toRepresentation) :=
    { toLinearMap := (wordCast e).toLinearMap.restrict fun x hx => wordCast_mem_cycG e w hx
      isIntertwining' := fun g => LinearMap.ext fun x => Subtype.ext (by
        show wordCast e (wordRepL n L g (x : WordSpaceL n L)) =
          wordRepL n' L (permHom e g) (wordCast e (x : WordSpaceL n L))
        exact wordCast_wordRepL e g x.1) }
  refine ⟨R.comp f, fun h0 => hf ?_⟩
  refine DFunLike.ext f 0 fun x => ?_
  have h1 : (R.comp f) x = 0 := by rw [h0]; rfl
  rw [Representation.IntertwiningMap.comp_apply] at h1
  have h2 : wordCast e (f x : WordSpaceL n L) = 0 := congrArg Subtype.val h1
  rw [LinearEquiv.map_eq_zero_iff] at h2
  exact Subtype.ext h2

end cast

end OAI.Saxl
