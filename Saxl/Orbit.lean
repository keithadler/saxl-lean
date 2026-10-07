import Mathlib
import Saxl.WordRep
import Saxl.Content
import Saxl.Sectors
import Saxl.Main

/-!
# Orbits of words and relabelling of letters

* `exists_perm_of_content_eq` : words with the same content are `S_n`-conjugate;
* `cycG_single_comp` : hence they generate the same cyclic module;
* `relabel` : a bijection of letters induces an equivariant linear isomorphism of word spaces,
  and `occurs_relabel` transports occurrence along it.
-/

namespace OAI.Saxl

open Equiv

section orbit

variable {n d : ℕ}

/-- Words with equal content differ by a position permutation. -/
theorem exists_perm_of_content_eq {w w' : Fin n → Fin d} (h : content w = content w') :
    ∃ g : Perm (Fin n), w' = w ∘ g := by
  classical
  have hcard : ∀ ℓ : Fin d, Fintype.card {p // w' p = ℓ} = Fintype.card {p // w p = ℓ} := by
    intro ℓ
    have := congrFun h ℓ
    unfold content at this
    simp only [Fintype.card_subtype]
    exact this.symm
  let e : ∀ ℓ : Fin d, {p // w' p = ℓ} ≃ {p // w p = ℓ} := fun ℓ => Fintype.equivOfCardEq (hcard ℓ)
  let g : Perm (Fin n) :=
    (Equiv.sigmaFiberEquiv w').symm.trans ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv w))
  refine ⟨g, funext fun p => ?_⟩
  show w' p = w ((e (w' p) ⟨p, rfl⟩).1)
  exact ((e (w' p) ⟨p, rfl⟩).2).symm

variable {L : Type} [DecidableEq L]

/-- `e_{w ∘ g} = g⁻¹ • e_w`. -/
theorem single_comp_eq_wordRepL (w : Fin n → L) (g : Perm (Fin n)) :
    (Pi.single (w ∘ g) (1 : ℂ) : WordSpaceL n L) = wordRepL n L g⁻¹ (Pi.single w 1) := by
  rw [wordRepL_single, inv_inv]

/-- Conjugate words generate the same cyclic module. -/
theorem cycG_single_comp (w : Fin n → L) (g : Perm (Fin n)) :
    cycG (wordRepL n L) (Pi.single (w ∘ g) 1) = cycG (wordRepL n L) (Pi.single w 1) := by
  apply Subrepresentation.toSubmodule_injective
  show Submodule.span ℂ _ = Submodule.span ℂ _
  rw [single_comp_eq_wordRepL]
  congr 1
  ext f
  simp only [Set.mem_range]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h * g⁻¹, by rw [map_mul, Module.End.mul_apply]⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h * g, by rw [← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel, mul_one]⟩

theorem cycG_single_eq_of_content_eq {w w' : Fin n → Fin d} (h : content w = content w') :
    cycG (wordRepL n (Fin d)) (Pi.single w' 1) = cycG (wordRepL n (Fin d)) (Pi.single w 1) := by
  obtain ⟨g, rfl⟩ := exists_perm_of_content_eq h
  exact cycG_single_comp w g

end orbit

section relabel

variable {n : ℕ} {L L' : Type} [DecidableEq L] [DecidableEq L'] (q : L ≃ L')

/-- Relabelling letters along a bijection. -/
def relabel : WordSpaceL n L ≃ₗ[ℂ] WordSpaceL n L' :=
  LinearEquiv.funCongrLeft ℂ ℂ (Equiv.arrowCongr (Equiv.refl (Fin n)) q.symm)

theorem relabel_apply (f : WordSpaceL n L) (u : Fin n → L') : relabel q f u = f (q.symm ∘ u) := rfl

theorem relabel_single (w : Fin n → L) :
    relabel q (Pi.single w (1 : ℂ)) = Pi.single (q ∘ w) 1 := by
  funext u
  rw [relabel_apply]
  by_cases h : u = q ∘ w
  · subst h
    simp [Function.comp_def]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'
    apply h
    funext i
    exact (q.symm_apply_eq).1 (congrFun h' i)

theorem relabel_wordRepL (g : Perm (Fin n)) (f : WordSpaceL n L) :
    relabel q (wordRepL n L g f) = wordRepL n L' g (relabel q f) := by
  funext u; rfl

/-- `relabel` carries `ℂ[S_n] e_w` into `ℂ[S_n] e_{q ∘ w}`. -/
theorem relabel_mem_cycG (w : Fin n → L) {x : WordSpaceL n L}
    (hx : x ∈ cycG (wordRepL n L) (Pi.single w 1)) :
    relabel q x ∈ cycG (wordRepL n L') (Pi.single (q ∘ w) 1) := by
  rw [mem_cycG_iff] at hx
  refine Submodule.span_induction
    (p := fun x _ => relabel q x ∈ cycG (wordRepL n L') (Pi.single (q ∘ w) 1)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨g, rfl⟩
    dsimp only
    rw [relabel_wordRepL, relabel_single]
    exact Submodule.subset_span ⟨g, rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- Occurrence transports along relabelling of letters. -/
theorem occurs_relabel {μ : YoungDiagram} (t : Tableau n μ) (w : Fin n → L)
    (h : Occurs t (cycG (wordRepL n L) (Pi.single w 1)).toRepresentation) :
    Occurs t (cycG (wordRepL n L') (Pi.single (q ∘ w) 1)).toRepresentation := by
  obtain ⟨f, hf⟩ := h
  let R : Representation.IntertwiningMap (cycG (wordRepL n L) (Pi.single w 1)).toRepresentation
      (cycG (wordRepL n L') (Pi.single (q ∘ w) 1)).toRepresentation :=
    { toLinearMap := (relabel q).toLinearMap.restrict fun x hx => relabel_mem_cycG q w hx
      isIntertwining' := fun g => LinearMap.ext fun x => Subtype.ext (relabel_wordRepL q g x) }
  refine ⟨R.comp f, fun h0 => hf ?_⟩
  refine DFunLike.ext f 0 fun x => ?_
  have h1 : (R.comp f) x = 0 := by rw [h0]; rfl
  rw [Representation.IntertwiningMap.comp_apply] at h1
  have h2 : relabel q (f x : WordSpaceL n L) = 0 := congrArg Subtype.val h1
  rw [LinearEquiv.map_eq_zero_iff] at h2
  exact Subtype.ext h2

end relabel

end OAI.Saxl
