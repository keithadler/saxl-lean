import Mathlib
import Saxl.Statement
import Saxl.Polytabloid
import Saxl.Main
import Saxl.WordRep

/-!
# Transport of occurrence along a bijection of position sets

For `e : Fin n ≃ Fin n'`, a tableau `t : Tableau n μ` becomes `e.symm.trans t : Tableau n' μ`,
`S_n ≃* S_{n'}` by conjugation, and word spaces correspond by `wordCast e`.  Occurrence of `S^μ`
is transported accordingly (`occurs_castN`).
-/

namespace OAI.Saxl

open Equiv

variable {n n' : ℕ} (e : Fin n ≃ Fin n')

/-- Conjugation `S_n →* S_{n'}` by `e`. -/
def permHom : Perm (Fin n) →* Perm (Fin n') where
  toFun g := e.permCongr g
  map_one' := by ext x; simp [Equiv.permCongr_apply]
  map_mul' g h := by ext x; simp [Equiv.permCongr_apply, Perm.mul_apply]

theorem permHom_apply (g : Perm (Fin n)) (x : Fin n') : permHom e g x = e (g (e.symm x)) := rfl

theorem permHom_surjective : Function.Surjective (permHom e) := fun g' =>
  ⟨e.symm.permCongr g', by ext x; simp [permHom_apply, Equiv.permCongr_apply]⟩

/-- Position relabelling of word spaces: `(wordCast f) u = f (u ∘ e)`. -/
def wordCast {L : Type} : WordSpaceL n L ≃ₗ[ℂ] WordSpaceL n' L :=
  LinearEquiv.funCongrLeft ℂ ℂ (Equiv.arrowCongr e.symm (Equiv.refl L))

theorem wordCast_apply {L : Type} (f : WordSpaceL n L) (u : Fin n' → L) :
    wordCast e f u = f (u ∘ e) := rfl

theorem wordCast_single {L : Type} [DecidableEq L] (w : Fin n → L) :
    wordCast e (Pi.single w (1 : ℂ)) = Pi.single (w ∘ e.symm) 1 := by
  funext u
  rw [wordCast_apply]
  by_cases h : u = w ∘ e.symm
  · subst h
    have : (w ∘ ⇑e.symm) ∘ ⇑e = w := by funext i; simp
    rw [this, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'; apply h; rw [← h']; funext i; simp

theorem wordCast_wordRepL {L : Type} (g : Perm (Fin n)) (f : WordSpaceL n L) :
    wordCast e (wordRepL n L g f) = wordRepL n' L (permHom e g) (wordCast e f) := by
  funext u
  rw [wordCast_apply, wordRepL_apply, wordRepL_apply, wordCast_apply]
  congr 1
  funext i
  simp [permHom_apply]

variable {μ : YoungDiagram}

/-- The relabelled tableau. -/
def castTableau (t : Tableau n μ) : Tableau n' μ := e.symm.trans t

theorem rowWord_castTableau (t : Tableau n μ) : rowWord (castTableau e t) = rowWord t ∘ e.symm := by
  funext i; rfl

theorem mem_columnGroup_castTableau (t : Tableau n μ) (g : Perm (Fin n)) :
    permHom e g ∈ columnGroup (castTableau e t) ↔ g ∈ columnGroup t := by
  simp only [mem_columnGroup, castTableau, Equiv.trans_apply, permHom_apply, Equiv.symm_apply_apply]
  constructor
  · intro h i
    have := h (e i)
    simpa using this
  · intro h i
    exact h (e.symm i)

/-- Conjugation as an equivalence of column groups. -/
def columnGroupCast (t : Tableau n μ) : columnGroup t ≃ columnGroup (castTableau e t) where
  toFun g := ⟨permHom e g, (mem_columnGroup_castTableau e t g).2 g.2⟩
  invFun g' := ⟨e.symm.permCongr g', by
    have : permHom e (e.symm.permCongr g') = g' := by
      ext x; simp [permHom_apply, Equiv.permCongr_apply]
    rw [← mem_columnGroup_castTableau e t, this]; exact g'.2⟩
  left_inv g := by ext1; ext x; simp [permHom_apply, Equiv.permCongr_apply]
  right_inv g' := by ext1; ext x; simp [permHom_apply, Equiv.permCongr_apply]

theorem sign_permHom (g : Perm (Fin n)) : Perm.sign (permHom e g) = Perm.sign g := by
  show Perm.sign (e.permCongr g) = Perm.sign g
  exact Perm.sign_permCongr e g

theorem polytabloid_castTableau (t : Tableau n μ) :
    polytabloid (castTableau e t) = wordCast e (polytabloid t) := by
  rw [polytabloid_eq_sum, polytabloid_eq_sum, map_sum]
  letI := Fintype.ofFinite (columnGroup t)
  letI := Fintype.ofFinite (columnGroup (castTableau e t))
  refine (Fintype.sum_equiv (columnGroupCast e t) _ _ fun g => ?_).symm
  simp only [columnGroupCast, Equiv.coe_fn_mk, map_smul, wordCast_single, sign_permHom]
  congr 2
  rw [rowWord_castTableau]
  have key : ∀ i, (permHom e (g : Perm (Fin n)))⁻¹ i = e ((g : Perm (Fin n))⁻¹ (e.symm i)) :=
    fun i => by rw [← map_inv, permHom_apply]
  funext i
  simp only [Function.comp_apply, key, Equiv.symm_apply_apply]

theorem wordCast_mem_specht (t : Tableau n μ) {x : WordSpace n (μ.colLen 0)} (hx : x ∈ Specht t) :
    wordCast e x ∈ Specht (castTableau e t) := by
  refine Submodule.span_induction (p := fun x _ => wordCast e x ∈ Specht (castTableau e t))
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨g, rfl⟩
    dsimp only
    rw [show (wordRep n (μ.colLen 0)) = wordRepL n (Fin (μ.colLen 0)) from rfl, wordCast_wordRepL,
      ← polytabloid_castTableau]
    exact Submodule.subset_span ⟨permHom e g, rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- A representation of `S_{n'}` pulled back to `S_n`. -/
def pullback {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (ρ : Representation ℂ (Perm (Fin n')) V) : Representation ℂ (Perm (Fin n)) V :=
  ρ.comp (permHom e)

/-- Occurrence transports along position relabelling. -/
theorem occurs_castN (t : Tableau n μ) {V : Type*} [AddCommMonoid V] [Module ℂ V]
    {ρ : Representation ℂ (Perm (Fin n')) V} (h : Occurs t (pullback e ρ)) :
    Occurs (castTableau e t) ρ := by
  obtain ⟨f, hf⟩ := h
  -- `S^{t'} → S^t` by `wordCast e.symm` ... we use the inverse direction via `castTableau e.symm`?
  -- Simpler: `wordCast e` restricted is a linear iso `S^t ≃ S^{t'}`; invert it.
  let W : Specht t →ₗ[ℂ] Specht (castTableau e t) :=
    (wordCast e).toLinearMap.restrict fun x hx => wordCast_mem_specht e t hx
  have hWinj : Function.Injective W := by
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext ((wordCast e).injective this)
  have hWsurj : Function.Surjective W := by
    intro y
    -- `y = wordCast e (wordCast e.symm y)` and `wordCast e.symm y ∈ Specht t`
    have hmem : (wordCast e).symm (y : WordSpace n' (μ.colLen 0)) ∈ Specht t := by
      have h1 := wordCast_mem_specht e.symm (castTableau e t) y.2
      have h2 : castTableau e.symm (castTableau e t) = t := by
        refine Equiv.ext fun i => ?_
        simp [castTableau]
      rw [h2] at h1
      have h3 : wordCast e.symm (y : WordSpace n' (μ.colLen 0)) =
          (wordCast e).symm (y : WordSpace n' (μ.colLen 0)) := by
        apply (wordCast e).injective
        rw [LinearEquiv.apply_symm_apply]
        funext u
        rw [wordCast_apply, wordCast_apply]
        have hu : (u ∘ ⇑e) ∘ ⇑e.symm = u := by funext i; simp
        rw [hu]
      rw [h3] at h1
      exact h1
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    show wordCast e ((wordCast e).symm (y : WordSpace n' (μ.colLen 0))) = y
    rw [LinearEquiv.apply_symm_apply]
  let Weq : Specht t ≃ₗ[ℂ] Specht (castTableau e t) := LinearEquiv.ofBijective W ⟨hWinj, hWsurj⟩
  refine ⟨{ toLinearMap := f.toLinearMap ∘ₗ Weq.symm.toLinearMap
            isIntertwining' := fun g' => ?_ }, fun h0 => hf ?_⟩
  · refine LinearMap.ext fun y => ?_
    obtain ⟨g, rfl⟩ := permHom_surjective e g'
    -- reduce to `x := Weq.symm y ∈ S^t`
    obtain ⟨x, rfl⟩ := Weq.surjective y
    have hx : Weq.symm (Weq x) = x := Weq.symm_apply_apply x
    have hcomm : (spechtRep (castTableau e t)) (permHom e g) (Weq x) = Weq ((spechtRep t) g x) := by
      apply Subtype.ext
      show wordRepL n' (Fin (μ.colLen 0)) (permHom e g) (wordCast e (x : WordSpace n (μ.colLen 0))) =
        wordCast e (wordRepL n (Fin (μ.colLen 0)) g (x : WordSpace n (μ.colLen 0)))
      rw [wordCast_wordRepL]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Representation.IntertwiningMap.toLinearMap_apply]
    rw [hcomm, Weq.symm_apply_apply, hx]
    exact Representation.IntertwiningMap.isIntertwining _ _ f g x
  · refine DFunLike.ext f 0 fun x => ?_
    have := congrArg (fun k : Representation.IntertwiningMap (spechtRep (castTableau e t)) ρ =>
      k (Weq x)) h0
    simp only at this
    change f (Weq.symm (Weq x)) = (0 : Representation.IntertwiningMap _ _) (Weq x) at this
    rw [Weq.symm_apply_apply] at this
    exact this

end OAI.Saxl
