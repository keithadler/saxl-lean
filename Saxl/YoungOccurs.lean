import Mathlib
import Saxl.Pieri
import Saxl.Sectors
import Saxl.WordSectors
import Saxl.WordRep
import Saxl.ShapeInvariance

/-!
# Young's rule, occurrence form — the inductive step

If `S^ν` occurs in `W = ℂ[S_a] e_w` and `λ/ν` is a horizontal strip of size `b`, then `S^λ`
occurs in `ℂ[S_{a+b}] e_{w₀}` where `w₀` extends `w` by a new letter on the last `b` positions.
Proof: Pieri gives a nonzero `S_a × S_b`-map `W ⊠ 1 → Res S^λ`; the restriction map
`A₀ = ℂ[S_a × S_b] e_{w₀} ↠ W ⊠ 1` is surjective; the sector lemma extends the composite to
`ℂ[S_{a+b}] e_{w₀} → S^λ`.
-/

namespace OAI.Saxl

open Equiv Representation

section step

variable {a b k : ℕ}

/-- Extend a word on `a` positions by the letter `Fin.last k` on the last `b` positions. -/
def extendWord (w : Fin a → Fin k) : Fin (a + b) → Fin (k + 1) :=
  Fin.addCases (fun i => Fin.castSucc (w i)) (fun _ => Fin.last k)

@[simp] theorem extendWord_castAdd (w : Fin a → Fin k) (i : Fin a) :
    extendWord (b := b) w (Fin.castAdd b i) = Fin.castSucc (w i) := by simp [extendWord]

@[simp] theorem extendWord_natAdd (w : Fin a → Fin k) (j : Fin b) :
    extendWord (b := b) w (Fin.natAdd a j) = Fin.last k := by simp [extendWord]

theorem extendWord_injective : Function.Injective (extendWord (a := a) (b := b) (k := k)) := by
  intro w w' h
  funext i
  have := congrFun h (Fin.castAdd b i)
  simp only [extendWord_castAdd] at this
  exact Fin.castSucc_injective _ this

theorem extendWord_comp_embPair (w : Fin a → Fin k) (p : Perm (Fin a) × Perm (Fin b)) :
    extendWord (b := b) w ∘ embPair p = extendWord (w ∘ p.1) := by
  funext q
  refine Fin.addCases (fun i => ?_) (fun j => ?_) q <;> simp

theorem letterSet_extendWord (w : Fin a → Fin k) :
    letterSet (Fin.last k) (extendWord (b := b) w) = (lastPositions a b).1 := by
  ext q
  rw [mem_letterSet, mem_lastPositions]
  refine Fin.addCases (fun i => ?_) (fun j => ?_) q
  · simp only [extendWord_castAdd]
    constructor
    · intro h; exact absurd h (Fin.castSucc_lt_last _).ne
    · rintro ⟨j, hj⟩
      have := congrArg Fin.val hj
      simp at this
      omega
  · simp

/-- Restriction to the first `a` positions (precomposition with `extendWord`). -/
noncomputable def restrictWord : WordSpaceL (a + b) (Fin (k + 1)) →ₗ[ℂ] WordSpaceL a (Fin k) :=
  LinearMap.funLeft ℂ ℂ (extendWord (b := b))

theorem restrictWord_apply (f : WordSpaceL (a + b) (Fin (k + 1))) (w : Fin a → Fin k) :
    restrictWord (b := b) f w = f (extendWord w) := rfl

theorem restrictWord_single (w : Fin a → Fin k) :
    restrictWord (Pi.single (extendWord (b := b) w) 1) = Pi.single w 1 := by
  funext w'
  rw [restrictWord_apply]
  by_cases h : w' = w
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun h' => h (extendWord_injective h'))]

theorem restrictWord_wordRep (p : Perm (Fin a) × Perm (Fin b)) (f : WordSpaceL (a + b) (Fin (k + 1))) :
    restrictWord (wordRepL (a + b) (Fin (k + 1)) (embPair p) f) =
      wordRepL a (Fin k) p.1 (restrictWord f) := by
  funext w
  rw [restrictWord_apply, wordRepL_apply, wordRepL_apply, restrictWord_apply,
    extendWord_comp_embPair]

variable {nu lam : YoungDiagram} (T : StripTableau a b nu lam)

/-- **Young step.** -/
theorem young_step (hle : nu ≤ lam) (hstrip : HorizontalStrip nu lam)
    (hd : nu.colLen 0 ≤ lam.colLen 0) (w : Fin a → Fin k)
    (hν : Occurs (T.nuTableau hle)
      (cycG (wordRepL a (Fin k)) (Pi.single w 1)).toRepresentation) :
    Occurs T.t (cycG (wordRepL (a + b) (Fin (k + 1)))
      (Pi.single (extendWord (b := b) w) 1)).toRepresentation := by
  set ρ := wordRepL (a + b) (Fin (k + 1)) with hρ
  set z : WordSpaceL (a + b) (Fin (k + 1)) := Pi.single (extendWord (b := b) w) 1 with hz
  set W := cycG (wordRepL a (Fin k)) (Pi.single w 1) with hW
  obtain ⟨f, hf⟩ := T.exists_pair_intertwiner_of_occurs hle hstrip hd hν
  -- the restriction map `A₀ → W`
  have hR : ∀ y ∈ cycH ρ z embPair, restrictWord y ∈ W := by
    intro y hy
    rw [mem_cycH_iff] at hy
    refine Submodule.span_induction (p := fun y _ => restrictWord y ∈ W) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨p, rfl⟩
      dsimp only
      rw [resStab_apply, restrictWord_wordRep, restrictWord_single]
      exact Submodule.subset_span ⟨p.1, rfl⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx
  let R : IntertwiningMap (cycH ρ z embPair).toRepresentation
      (pairRep (b := b) W.toRepresentation) :=
    { toLinearMap := (restrictWord (b := b)).restrict fun y hy => hR y hy
      isIntertwining' := fun p => LinearMap.ext fun y => Subtype.ext (by
        show restrictWord (ρ (embPair p) (y : WordSpaceL (a + b) (Fin (k + 1)))) =
          wordRepL a (Fin k) p.1 (restrictWord (y : WordSpaceL (a + b) (Fin (k + 1))))
        exact restrictWord_wordRep p y.1) }
  -- `R` is surjective: the generators of `W` are hit
  have hRsurj : Function.Surjective R := by
    intro y
    have hy : (y : WordSpaceL a (Fin k)) ∈ (cycH ρ z embPair).toSubmodule.map (restrictWord (b := b)) := by
      have hle' : W.toSubmodule ≤ (cycH ρ z embPair).toSubmodule.map (restrictWord (b := b)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨σ, rfl⟩
        refine ⟨ρ (embPair (σ, 1)) z, Submodule.subset_span ⟨(σ, 1), rfl⟩, ?_⟩
        rw [restrictWord_wordRep, restrictWord_single]
      exact hle' y.2
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hφ : f.comp R ≠ 0 := by
    intro h0
    apply hf
    refine DFunLike.ext f 0 fun y => ?_
    obtain ⟨x, rfl⟩ := hRsurj y
    exact congrArg (fun k => k x) h0
  -- extend along the sectors
  obtain ⟨Φ, hΦ⟩ := exists_extension_of_sectors ρ (lastPositions a b) z embPair
    (sectorProj (Fin.last k) b) (sectorProj_disj _ _) (sectorProj_equiv _ _)
    (sectorProj_single _ _ _ _ (letterSet_extendWord w)) embPair_smul_lastPositions
    (fun g hg => (exists_embPair_of_smul_eq hg).imp fun p hp => hp.symm)
    (spechtRep T.t) (f.comp R)
  have hΦ0 : Φ ≠ 0 := by
    intro h0
    apply hφ
    refine DFunLike.ext _ 0 fun y => ?_
    have := hΦ y y.2
    rw [h0] at this
    exact this.symm
  exact occurs_of_intertwiner_to T.t Φ hΦ0

end step

/-! ### The chain induction -/

section chain

open YoungDiagram

variable {a b k : ℕ}

theorem content_extendWord_last (w : Fin a → Fin k) :
    content (extendWord (b := b) w) (Fin.last k) = b := by
  unfold content
  rw [Finset.card_filter, Fin.sum_univ_add]
  simp only [extendWord_castAdd, extendWord_natAdd, (Fin.castSucc_lt_last _).ne, if_false,
    Finset.sum_const_zero, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, zero_add]

theorem content_extendWord_castSucc (w : Fin a → Fin k) (i : Fin k) :
    content (extendWord (b := b) w) (Fin.castSucc i) = content w i := by
  unfold content
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  simp only [extendWord_castAdd, extendWord_natAdd, Fin.castSucc_inj, (Fin.castSucc_lt_last _).ne',
    if_false, Finset.sum_const_zero, add_zero]

/-- `μ.cells ⊕ (λ.cells \ μ.cells) ≃ λ.cells`. -/
def cellsSumDiff {mu lam : YoungDiagram} (hle : mu ≤ lam) :
    mu.cells ⊕ ↥(lam.cells \ mu.cells) ≃ lam.cells where
  toFun := Sum.elim (fun c => ⟨c.1, hle c.2⟩) (fun c => ⟨c.1, (Finset.mem_sdiff.1 c.2).1⟩)
  invFun c := if h : c.1 ∈ mu.cells then Sum.inl ⟨c.1, h⟩
    else Sum.inr ⟨c.1, Finset.mem_sdiff.2 ⟨c.2, h⟩⟩
  left_inv x := by
    rcases x with c | c
    · simp [c.2]
    · have := (Finset.mem_sdiff.1 c.2).2
      simp [this]
  right_inv c := by
    by_cases h : c.1 ∈ mu.cells
    · simp [h]
    · simp [h]

/-- A strip tableau for `μ ⊆ λ` on `Fin (a + b)` positions, from the cardinalities. -/
noncomputable def stripTableauOf {mu lam : YoungDiagram} (hle : mu ≤ lam) (ha : mu.card = a)
    (hb : mu.card + b = lam.card) : StripTableau a b mu lam :=
  let e1 : Fin a ≃ mu.cells := (Finset.equivFinOfCardEq ha).symm
  have hb' : (lam.cells \ mu.cells).card = b := by
    have := Finset.card_sdiff_add_card_eq_card (hle : mu.cells ⊆ lam.cells)
    show (lam.cells \ mu.cells).card = b
    have h2 : lam.cells.card = lam.card := rfl
    have h3 : mu.cells.card = mu.card := rfl
    omega
  let e2 : Fin b ≃ ↥(lam.cells \ mu.cells) := (Finset.equivFinOfCardEq hb').symm
  let t : Tableau (a + b) lam := (finSumFinEquiv.symm.trans (e1.sumCongr e2)).trans (cellsSumDiff hle)
  { t := t
    mem_nu := fun i => by
      show ((cellsSumDiff hle) ((e1.sumCongr e2) (finSumFinEquiv.symm (Fin.castAdd b i)))).val ∈ mu
      rw [finSumFinEquiv_symm_apply_castAdd]
      exact (e1 i).2
    not_mem_nu := fun j => by
      show ((cellsSumDiff hle) ((e1.sumCongr e2) (finSumFinEquiv.symm (Fin.natAdd a j)))).val ∉ mu
      rw [finSumFinEquiv_symm_apply_natAdd]
      exact (Finset.mem_sdiff.1 (e2 j).2).2 }

/-- The degenerate case `n = 0`: `S^⊥` occurs in the (one-dimensional) word space. -/
theorem occurs_zero (t : Tableau 0 ⊥) (w : Fin 0 → Fin 0) :
    Occurs t (cycG (wordRepL 0 (Fin 0)) (Pi.single w 1)).toRepresentation := by
  have hmem : (Pi.single w (1 : ℂ) : WordSpaceL 0 (Fin 0)) ∈ cycG (wordRepL 0 (Fin 0)) (Pi.single w 1) :=
    Submodule.subset_span ⟨1, by simp⟩
  have hg : ∀ g : Perm (Fin 0), g = 1 := fun g => by ext i; exact i.elim0
  let F : IntertwiningMap (spechtRep t)
      (cycG (wordRepL 0 (Fin 0)) (Pi.single w 1)).toRepresentation :=
    { toLinearMap := (LinearMap.proj (rowWord t) ∘ₗ (Specht t).subtype).smulRight
        (⟨Pi.single w 1, hmem⟩ : (cycG (wordRepL 0 (Fin 0)) (Pi.single w 1)).toSubmodule)
      isIntertwining' := fun g => by rw [hg g, map_one, map_one]; rfl }
  refine ⟨F, fun h0 => ?_⟩
  have := congrArg (fun k : IntertwiningMap (spechtRep t)
    (cycG (wordRepL 0 (Fin 0)) (Pi.single w 1)).toRepresentation =>
    (k ⟨polytabloid t, polytabloid_mem_specht t⟩ : WordSpaceL 0 (Fin 0)) w) h0
  have h1 : (F ⟨polytabloid t, polytabloid_mem_specht t⟩ : WordSpaceL 0 (Fin 0)) =
      polytabloid t (rowWord t) • Pi.single w 1 := rfl
  rw [h1, polytabloid_apply_rowWord, one_smul] at this
  simp at this

/-- **Young's rule, occurrence form, along a sized chain.** -/
theorem young_occurs_aux (ℓ : ℕ) (θ : ℕ → ℕ) (τ : YoungDiagram) (hc : SizedChain θ ℓ ⊥ τ) :
    ∃ (n : ℕ) (_ : n = τ.card) (w : Fin n → Fin ℓ),
      (∀ i : Fin ℓ, content w i = θ i) ∧
      ∀ t : Tableau n τ, Occurs t (cycG (wordRepL n (Fin ℓ)) (Pi.single w 1)).toRepresentation := by
  generalize hb : (⊥ : YoungDiagram) = b at hc
  induction hc with
  | zero ν =>
    subst hb
    refine ⟨0, ?_, fun i => i.elim0, fun i => i.elim0, fun t => occurs_zero t _⟩
    show 0 = (⊥ : YoungDiagram).cells.card
    rw [cells_bot, Finset.card_empty]
  | @succ ℓ ν mu lam hc hs hcard ih =>
    obtain ⟨a, ha, w, hw, hocc⟩ := ih hb
    refine ⟨a + θ ℓ, by omega, extendWord w, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · exact content_extendWord_last w
      · rw [content_extendWord_castSucc, hw]
        rfl
    · intro t
      let T : StripTableau a (θ ℓ) mu lam := stripTableauOf hs.1 ha.symm hcard
      have hd : mu.colLen 0 ≤ lam.colLen 0 := colLen_le_of_le hs.1 0
      have := young_step T hs.1 hs hd w (hocc _)
      exact occurs_of_occurs T.t t this

/-- **Young's rule (occurrence form).**  If `τ ⊵ θ` with `|τ| = |θ|`, then `S^τ` occurs in the
cyclic module generated by a word of content `θ`. -/
theorem young_occurs {τ θ : YoungDiagram} (hd : Dominates τ θ) (hc : τ.card = θ.card) :
    ∃ (n : ℕ) (_ : n = τ.card) (w : Fin n → Fin (θ.colLen 0)),
      (∀ i, content w i = θ.rowLen i) ∧
      ∀ t : Tableau n τ,
        Occurs t (cycG (wordRepL n (Fin (θ.colLen 0))) (Pi.single w 1)).toRepresentation :=
  young_occurs_aux _ _ _ (sizedChain_of_dominates hd hc)

end chain

end OAI.Saxl
