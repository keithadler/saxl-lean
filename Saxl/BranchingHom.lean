import Mathlib
import Saxl.Branching
import Saxl.MaschkeBridge
import Saxl.SubmoduleTheorem

/-!
# The branching intertwiner

From `Φ_symmPolytabloid` we extract a nonzero `S_a`-intertwiner `S^ν → Res_{S_a} S^λ` whose image
consists of `S_b`-fixed vectors (paper: `S^ν ⊠ 1` occurs in `Res^{S_{a+b}}_{S_a × S_b} S^λ`).
-/

namespace OAI.Saxl

open Equiv Representation

attribute [local instance] Fintype.ofFinite

section embedding

variable {a b : ℕ}

/-- `embA` as a monoid homomorphism. -/
def embAHom : Perm (Fin a) →* Perm (Fin (a + b)) := embPair.comp (MonoidHom.inl _ _)

theorem embAHom_apply (σ : Perm (Fin a)) : embAHom (b := b) σ = embA σ := rfl

/-- `S_a` and `S_b` commute inside `S_{a+b}`. -/
theorem embB_mul_embA (σ : Perm (Fin a)) (τ : Perm (Fin b)) :
    embB τ * embA σ = embA σ * embB τ := by
  simp only [embA, embB, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

end embedding

namespace StripTableau

variable {a b : ℕ} {nu lam : YoungDiagram} (T : StripTableau a b nu lam)

/-- `S^λ` as an `S_a`-representation, by restriction along `embA`. -/
noncomputable def resA : Representation ℂ (Perm (Fin a)) (Specht T.t) :=
  (spechtRep T.t).comp embAHom

theorem resA_apply (σ : Perm (Fin a)) (x : Specht T.t) :
    (T.resA σ x : WordSpace (a + b) (lam.colLen 0)) =
      wordRep (a + b) (lam.colLen 0) (embA σ) x := rfl

/-- The ambient word space as an `S_a`-representation, by restriction along `embA`. -/
noncomputable def _root_.OAI.Saxl.resAmb (a b : ℕ) (lam : YoungDiagram) :
    Representation ℂ (Perm (Fin a)) (WordSpace (a + b) (lam.colLen 0)) :=
  (wordRep (a + b) (lam.colLen 0)).comp embAHom

theorem _root_.OAI.Saxl.resAmb_apply (a b : ℕ) (lam : YoungDiagram) (σ : Perm (Fin a))
    (x : WordSpace (a + b) (lam.colLen 0)) :
    (resAmb a b lam) σ x = wordRep (a + b) (lam.colLen 0) (embA σ) x := rfl

/-- `Φ` as an `S_a`-intertwiner on the ambient word space. -/
noncomputable def ΦAmb (hd : nu.colLen 0 ≤ lam.colLen 0) :
    IntertwiningMap (resAmb a b lam) (wordRep a (nu.colLen 0)) where
  toLinearMap := T.Φ hd
  isIntertwining' σ := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, resAmb_apply, Φ_wordRep]

/-- The `S_a`-subrepresentation `A = ℂ[S_a] u` of the ambient word space. -/
noncomputable def cycA : Subrepresentation (resAmb a b lam) := cyclic (resAmb a b lam) T.symmPolytabloid

theorem symmPolytabloid_mem_cycA : T.symmPolytabloid ∈ T.cycA :=
  Submodule.subset_span ⟨1, by simp⟩

/-- Every element of `A` is fixed by `S_b`. -/
theorem wordRep_embB_of_mem_cycA (τ : Perm (Fin b)) {x : WordSpace (a + b) (lam.colLen 0)}
    (hx : x ∈ T.cycA) : wordRep (a + b) (lam.colLen 0) (embB τ) x = x := by
  have hx' : x ∈ Submodule.span ℂ (Set.range fun σ => (resAmb a b lam) σ T.symmPolytabloid) := hx
  refine Submodule.span_induction
    (p := fun (y : WordSpace (a + b) (lam.colLen 0)) _ =>
      wordRep (a + b) (lam.colLen 0) (embB τ) y = y) ?_ ?_ ?_ ?_ hx'
  · rintro _ ⟨σ, rfl⟩
    dsimp only
    rw [resAmb_apply, ← Module.End.mul_apply, ← map_mul, embB_mul_embA, map_mul,
      Module.End.mul_apply, wordRep_embB_symmPolytabloid]
  · simp
  · intro y z _ _ hy hz
    rw [map_add, hy, hz]
  · intro c y _ hy
    rw [map_smul, hy]

/-- `A ⊆ S^λ`. -/
theorem cycA_le_specht : T.cycA.toSubmodule ≤ Specht T.t := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨σ, rfl⟩
  exact (spechtSub T.t).apply_mem_toSubmodule _ T.symmPolytabloid_mem

/-- `Φ` restricted to `A`. -/
noncomputable def ΦA (hd : nu.colLen 0 ≤ lam.colLen 0) :
    IntertwiningMap T.cycA.toRepresentation (wordRep a (nu.colLen 0)) :=
  (T.ΦAmb hd).comp (inclusion T.cycA)

/-- Corestriction of an intertwiner onto its range. -/
noncomputable def _root_.OAI.Saxl.corestrict {G : Type*} [Group G] {V W : Type*} [AddCommGroup V]
    [AddCommGroup W] [Module ℂ V] [Module ℂ W] {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (f : IntertwiningMap ρ σ) :
    IntertwiningMap ρ f.range.toRepresentation where
  toLinearMap := f.toLinearMap.rangeRestrict
  isIntertwining' g := by
    ext x
    exact IntertwiningMap.isIntertwining _ _ f g x

theorem corestrict_surjective {G : Type*} [Group G] {V W : Type*} [AddCommGroup V]
    [AddCommGroup W] [Module ℂ V] [Module ℂ W] {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (f : IntertwiningMap ρ σ) :
    Function.Surjective (corestrict f) :=
  f.toLinearMap.surjective_rangeRestrict

/-- `S^ν` lies in the range of `Φ|_A`. -/
theorem spechtSub_le_range (hle : nu ≤ lam) (hstrip : HorizontalStrip nu lam)
    (hd : nu.colLen 0 ≤ lam.colLen 0) :
    (spechtSub (T.nuTableau hle)).toSubmodule ≤ (T.ΦA hd).range.toSubmodule := by
  have het : polytabloid (T.nuTableau hle) ∈ (T.ΦA hd).range := by
    have hc : (T.stripCount : ℂ) ≠ 0 := by exact_mod_cast T.stripCount_pos.ne'
    have h1 : T.ΦA hd ⟨T.symmPolytabloid, T.symmPolytabloid_mem_cycA⟩ =
        (T.stripCount : ℂ) • polytabloid (T.nuTableau hle) := by
      show T.Φ hd T.symmPolytabloid = _
      exact T.Φ_symmPolytabloid hle hstrip hd
    have h2 : polytabloid (T.nuTableau hle) =
        (T.stripCount : ℂ)⁻¹ • T.ΦA hd ⟨T.symmPolytabloid, T.symmPolytabloid_mem_cycA⟩ := by
      rw [h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ ⟨_, rfl⟩
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, rfl⟩
  exact (T.ΦA hd).range.apply_mem_toSubmodule g het

/-- `S^ν` occurs in the range of `Φ|_A`. -/
theorem occurs_range (hle : nu ≤ lam) (hstrip : HorizontalStrip nu lam)
    (hd : nu.colLen 0 ≤ lam.colLen 0) :
    Occurs (T.nuTableau hle) (T.ΦA hd).range.toRepresentation := by
  refine ⟨{ toLinearMap := Submodule.inclusion (T.spechtSub_le_range hle hstrip hd)
            isIntertwining' := fun g => LinearMap.ext fun x => Subtype.ext rfl }, fun h0 => ?_⟩
  have := congrArg (fun k => (k ⟨polytabloid _, polytabloid_mem_specht _⟩ :
    WordSpace a (nu.colLen 0))) h0
  exact polytabloid_ne_zero _ this

/-- `S^ν` occurs in `A = ℂ[S_a] u`. -/
theorem occurs_cycA (hle : nu ≤ lam) (hstrip : HorizontalStrip nu lam)
    (hd : nu.colLen 0 ≤ lam.colLen 0) :
    Occurs (T.nuTableau hle) T.cycA.toRepresentation :=
  Occurs.of_surjective _ (corestrict (T.ΦA hd)) (corestrict_surjective _)
    (T.occurs_range hle hstrip hd)

/-- The inclusion `A ↪ S^λ` as an `S_a`-intertwiner. -/
noncomputable def inclA : IntertwiningMap T.cycA.toRepresentation T.resA where
  toLinearMap := Submodule.inclusion T.cycA_le_specht
  isIntertwining' σ := LinearMap.ext fun x => Subtype.ext rfl

theorem inclA_apply (x : T.cycA.toSubmodule) : (T.inclA x : WordSpace (a + b) (lam.colLen 0)) = x :=
  rfl

/-- **Branching**: a nonzero `S_a`-intertwiner `S^ν → Res S^λ` with `S_b`-fixed image. -/
theorem exists_branching_intertwiner (hle : nu ≤ lam) (hstrip : HorizontalStrip nu lam)
    (hd : nu.colLen 0 ≤ lam.colLen 0) :
    ∃ f : IntertwiningMap (spechtRep (T.nuTableau hle)) T.resA, f ≠ 0 ∧
      ∀ (τ : Perm (Fin b)) (x : Specht (T.nuTableau hle)),
        wordRep (a + b) (lam.colLen 0) (embB τ) (Subtype.val (f x)) = Subtype.val (f x) := by
  obtain ⟨f₀, hf₀⟩ := T.occurs_cycA hle hstrip hd
  refine ⟨T.inclA.comp f₀, fun h0 => hf₀ ?_, fun τ x => ?_⟩
  · refine DFunLike.ext f₀ 0 fun v => ?_
    have h1 : (T.inclA.comp f₀) v = 0 := by rw [h0]; rfl
    rw [IntertwiningMap.comp_apply] at h1
    have h2 : ((f₀ v : T.cycA.toSubmodule) : WordSpace (a + b) (lam.colLen 0)) = 0 := by
      rw [← T.inclA_apply, h1]; rfl
    exact Subtype.ext h2
  · rw [IntertwiningMap.comp_apply, inclA_apply]
    exact T.wordRep_embB_of_mem_cycA τ (f₀ x).2

end StripTableau

end OAI.Saxl
