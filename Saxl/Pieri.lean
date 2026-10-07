import Mathlib
import Saxl.BranchingHom

/-!
# Pieri-occurrence

If `λ/ν` is a horizontal strip and `S^ν` occurs in an `S_a`-representation `W`, then `S^λ` occurs
in `Ind_{S_a × S_b}^{S_{a+b}} (W ⊠ 1)` (paper Lemma 2.2, occurrence direction).  Route:
branching intertwiner (`BranchingHom.lean`) → `S_a × S_b`-map `S^ν ⊠ 1 → Res S^λ` → extend to
`W ⊠ 1` by Maschke → Frobenius reciprocity (`Rep.indResHomEquiv`) → `occurs_of_intertwiner_to`.
-/

namespace OAI.Saxl

open Equiv Representation CategoryTheory

/-- Maschke extension: a nonzero intertwiner out of a subrepresentation extends. -/
theorem exists_extension {G : Type} [Group G] [Finite G] {V W P : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup P] [Module ℂ P]
    {σ : Representation ℂ G V} {ρ : Representation ℂ G W} {τ : Representation ℂ G P}
    (i : IntertwiningMap σ ρ) (hi : Function.Injective i) (f : IntertwiningMap σ τ) :
    ∃ h : IntertwiningMap ρ τ, h.comp i = f := by
  have : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨H, hH⟩ := IsSemisimpleModule.extension_property
    (IntertwiningMap.equivLinearMapAsModule σ ρ i) hi (IntertwiningMap.equivLinearMapAsModule σ τ f)
  refine ⟨(IntertwiningMap.equivLinearMapAsModule ρ τ).symm H, ?_⟩
  refine (IntertwiningMap.equivLinearMapAsModule σ τ).injective (LinearMap.ext fun x => ?_)
  exact DFunLike.congr_fun hH x

section pair

variable {a b : ℕ}

/-- An `S_a`-representation viewed as an `S_a × S_b`-representation with `S_b` acting trivially
(`W ⊠ 1`). -/
def pairRep {V : Type} [AddCommMonoid V] [Module ℂ V] (ρ : Representation ℂ (Perm (Fin a)) V) :
    Representation ℂ (Perm (Fin a) × Perm (Fin b)) V :=
  ρ.comp (MonoidHom.fst _ _)

theorem pairRep_apply {V : Type} [AddCommMonoid V] [Module ℂ V]
    (ρ : Representation ℂ (Perm (Fin a)) V) (p : Perm (Fin a) × Perm (Fin b)) (x : V) :
    pairRep (b := b) ρ p x = ρ p.1 x := rfl

theorem embPair_eq_mul (σ : Perm (Fin a)) (τ : Perm (Fin b)) :
    embPair (σ, τ) = embA σ * embB τ := by
  simp only [embA, embB, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

end pair

namespace StripTableau

variable {a b : ℕ} {nu lam : YoungDiagram} (T : StripTableau a b nu lam)

/-- `S^λ` restricted to `S_a × S_b`. -/
noncomputable def resPair : Representation ℂ (Perm (Fin a) × Perm (Fin b)) (Specht T.t) :=
  (spechtRep T.t).comp embPair

/-- The branching intertwiner as an `S_a × S_b`-map `S^ν ⊠ 1 → Res S^λ`. -/
theorem exists_pair_intertwiner (hle : nu ≤ lam) (hstrip : HorizontalStrip nu lam)
    (hd : nu.colLen 0 ≤ lam.colLen 0) :
    ∃ f : IntertwiningMap (pairRep (b := b) (spechtRep (T.nuTableau hle))) T.resPair, f ≠ 0 := by
  obtain ⟨f, hf, hfix⟩ := T.exists_branching_intertwiner hle hstrip hd
  refine ⟨⟨f.toLinearMap, fun p => ?_⟩, fun h0 => hf ?_⟩
  · refine LinearMap.ext fun x => ?_
    obtain ⟨σ, τ⟩ := p
    have h1 : f ((spechtRep (T.nuTableau hle)) σ x) = T.resA σ (f x) :=
      IntertwiningMap.isIntertwining _ _ f σ x
    have h2 : (spechtRep T.t) (embB τ) (f x) = f x := Subtype.ext (hfix τ x)
    show f ((spechtRep (T.nuTableau hle)) σ x) = (spechtRep T.t) (embPair (σ, τ)) (f x)
    rw [h1, embPair_eq_mul, map_mul, Module.End.mul_apply, h2]
    rfl
  · have h1 := congrArg IntertwiningMap.toLinearMap h0
    exact IntertwiningMap.ext h1

/-- Extension to any `W` in which `S^ν` occurs. -/
theorem exists_pair_intertwiner_of_occurs (hle : nu ≤ lam) (hstrip : HorizontalStrip nu lam)
    (hd : nu.colLen 0 ≤ lam.colLen 0) {V : Type} [AddCommGroup V] [Module ℂ V]
    {W : Representation ℂ (Perm (Fin a)) V} (hW : Occurs (T.nuTableau hle) W) :
    ∃ f : IntertwiningMap (pairRep (b := b) W) T.resPair, f ≠ 0 := by
  obtain ⟨i, hi⟩ := hW
  have hinj : Function.Injective i := (IsIrreducible.injective_or_eq_zero i).resolve_right hi
  -- `i` as an `S_a × S_b`-map `S^ν ⊠ 1 → W ⊠ 1`
  let i' : IntertwiningMap (pairRep (b := b) (spechtRep (T.nuTableau hle))) (pairRep (b := b) W) :=
    ⟨i.toLinearMap, fun p => IntertwiningMap.isIntertwining' i p.1⟩
  have hi' : Function.Injective i' := hinj
  obtain ⟨g, hg⟩ := T.exists_pair_intertwiner hle hstrip hd
  obtain ⟨h, hh⟩ := exists_extension i' hi' g
  exact ⟨h, fun h0 => hg (by rw [← hh, h0]; rfl)⟩

/-- Frobenius: a nonzero `S_a × S_b`-map `A → Res S^λ` gives a nonzero `S_{a+b}`-map
`Ind A → S^λ`. -/
theorem exists_ind_intertwiner {V : Type} [AddCommGroup V] [Module ℂ V]
    {A : Representation ℂ (Perm (Fin a) × Perm (Fin b)) V}
    (f : IntertwiningMap A T.resPair) (hf : f ≠ 0) :
    ∃ F : IntertwiningMap (Rep.ind embPair (Rep.of A)).ρ (spechtRep T.t), F ≠ 0 := by
  let fR : Rep.of A ⟶ Rep.res embPair (Rep.of (spechtRep T.t)) := Rep.ofHom f
  have hfR : fR ≠ 0 := fun h0 => hf (by
    have : (Rep.ofHom f).hom = (0 : Rep.of A ⟶ Rep.res embPair (Rep.of (spechtRep T.t))).hom := by
      rw [← h0]; rfl
    exact this)
  let FR := (Rep.indResHomEquiv embPair (Rep.of A) (Rep.of (spechtRep T.t))).symm fR
  have hFR : FR ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 hfR
  refine ⟨FR.hom, fun h0 => hFR ?_⟩
  have : FR = Rep.ofHom FR.hom := rfl
  rw [this, h0, Rep.ofHom_zero]

/-- **Pieri-occurrence**: if `S^ν` occurs in `W` then `S^λ` occurs in
`Ind_{S_a × S_b}^{S_{a+b}} (W ⊠ 1)`. -/
theorem occurs_ind_of_occurs (hle : nu ≤ lam) (hstrip : HorizontalStrip nu lam)
    (hd : nu.colLen 0 ≤ lam.colLen 0) {V : Type} [AddCommGroup V] [Module ℂ V]
    {W : Representation ℂ (Perm (Fin a)) V} (hW : Occurs (T.nuTableau hle) W) :
    Occurs T.t (Rep.ind embPair (Rep.of (pairRep (b := b) W))).ρ := by
  obtain ⟨f, hf⟩ := T.exists_pair_intertwiner_of_occurs hle hstrip hd hW
  obtain ⟨F, hF⟩ := T.exists_ind_intertwiner f hf
  exact occurs_of_intertwiner_to T.t F hF

end StripTableau

end OAI.Saxl
