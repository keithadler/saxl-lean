import Mathlib
import Saxl.Band1Factor
import Saxl.Pieri
import Saxl.Sectors
import Saxl.WordSectors
import Saxl.Prop32

/-!
# The width-one band cut, part 3: Prop 4.2 for `s = 1`

If `S^ν` occurs in `W_{m-1}` (for the staircase tableau on the first `a` positions) and `λ/ν` is a
horizontal strip of size `b`, then `S^λ` occurs in `W_m`.
-/

namespace OAI.Saxl

open Equiv YoungDiagram Finset Representation

attribute [local instance] Fintype.ofFinite

open scoped TensorProduct

section swap

variable {m a b : ℕ} (T : StripTableau a b (staircase (m - 1)) (staircase m))

/-- The strip tableau with swapped coordinates. -/
def StripTableau.swapST : StripTableau a b (staircase (m - 1)) (staircase m) where
  t := swapTableau T.t
  mem_nu i := by
    have h : ((T.t (Fin.castAdd b i)).val.1, (T.t (Fin.castAdd b i)).val.2) ∈ staircase (m - 1) :=
      T.mem_nu i
    show ((T.t (Fin.castAdd b i)).val.2, (T.t (Fin.castAdd b i)).val.1) ∈ staircase (m - 1)
    rw [mem_staircase] at h ⊢; omega
  not_mem_nu j := by
    have h : ((T.t (Fin.natAdd a j)).val.1, (T.t (Fin.natAdd a j)).val.2) ∉ staircase (m - 1) :=
      T.not_mem_nu j
    show ((T.t (Fin.natAdd a j)).val.2, (T.t (Fin.natAdd a j)).val.1) ∉ staircase (m - 1)
    rw [mem_staircase] at h ⊢; omega

theorem swapST_t : T.swapST.t = swapTableau T.t := rfl

theorem swapST_nuTableau : T.swapST.nuTableau (staircase_mono m) =
    swapTableau (T.nuTableau (staircase_mono m)) :=
  Equiv.ext fun i => Subtype.ext rfl

end swap

section restrict

variable {m a b : ℕ} (T : StripTableau a b (staircase (m - 1)) (staircase m))

/-- The shifted pair word. -/
def extendPair (w : Fin a → Fin (dR (m - 1)) × Fin (dR (m - 1))) :
    Fin (a + b) → Fin (dR m) × Fin (dR m) :=
  fun p => (extendCol T (Prod.fst ∘ w) p, extendCol T (Prod.snd ∘ w) p)

theorem extendCol_comp_embPair (v : Fin a → Fin (dR (m - 1))) (p : Perm (Fin a) × Perm (Fin b)) :
    extendCol T v ∘ embPair p = extendCol T (v ∘ p.1) := by
  funext q
  apply Fin.ext
  refine Fin.addCases (fun i => ?_) (fun j => ?_) q
  · simp only [Function.comp_apply, embPair_castAdd, extendCol_castAdd]
  · simp only [Function.comp_apply, embPair_natAdd, extendCol_natAdd]

theorem extendPair_comp_embPair (w : Fin a → Fin (dR (m - 1)) × Fin (dR (m - 1)))
    (p : Perm (Fin a) × Perm (Fin b)) :
    extendPair T w ∘ embPair p = extendPair T (w ∘ p.1) := by
  funext q
  simp only [Function.comp_apply, extendPair]
  rw [← Function.comp_apply (f := extendCol T (Prod.fst ∘ w)), extendCol_comp_embPair,
    ← Function.comp_apply (f := extendCol T (Prod.snd ∘ w)), extendCol_comp_embPair]
  rfl

/-- The restriction map `R`. -/
noncomputable def Rpair : WordSpaceL (a + b) (Fin (dR m) × Fin (dR m)) →ₗ[ℂ]
    WordSpaceL a (Fin (dR (m - 1)) × Fin (dR (m - 1))) :=
  LinearMap.funLeft ℂ ℂ (extendPair T)

theorem Rpair_apply (f : WordSpaceL (a + b) (Fin (dR m) × Fin (dR m)))
    (w : Fin a → Fin (dR (m - 1)) × Fin (dR (m - 1))) : Rpair T f w = f (extendPair T w) := rfl

theorem Rpair_wordRep (p : Perm (Fin a) × Perm (Fin b)) (f : WordSpaceL (a + b) (Fin (dR m) × Fin (dR m))) :
    Rpair T (pairRepR m (a + b) (embPair p) f) = pairRepR (m - 1) a p.1 (Rpair T f) := by
  funext w
  rw [Rpair_apply, wordRepL_apply, wordRepL_apply, Rpair_apply, extendPair_comp_embPair]

theorem extendPair_unmixed (w : Fin a → Fin (dR (m - 1)) × Fin (dR (m - 1))) (p : Fin (a + b)) :
    Unmixed (extendPair T w p) := by
  unfold Unmixed
  refine Fin.addCases (fun i => ?_) (fun j => ?_) p
  · simp only [extendPair, extendCol_castAdd]; omega
  · simp only [extendPair, extendCol_natAdd]

/-- `R (P₁ w_m) = c • w_{m-1}` with `c = sign σ_R · sign σ_C`. -/
theorem Rpair_unmixedProj_wm :
    Rpair T (unmixedProj (wm T.t)) =
      ((((Perm.sign (colShift T.swapST)) : ℤ) : ℂ) * (((Perm.sign (colShift T)) : ℤ) : ℂ)) •
        wm (T.nuTableau (staircase_mono m)) := by
  funext w
  rw [Rpair_apply, unmixedProj_apply, if_pos (extendPair_unmixed T w), wm, pairLift_tmul,
    pairMul_apply, Pi.smul_apply, wm, pairLift_tmul, pairMul_apply, smul_eq_mul]
  have h1 : Prod.fst ∘ extendPair T w = extendCol T (Prod.fst ∘ w) := rfl
  have h2 : Prod.snd ∘ extendPair T w = extendCol T (Prod.snd ∘ w) := rfl
  rw [h1, h2]
  have hR : polytabloid (swapTableau T.t) (extendCol T (Prod.fst ∘ w)) =
      ((Perm.sign (colShift T.swapST) : ℤ) : ℂ) •
        polytabloid (swapTableau (T.nuTableau (staircase_mono m))) (Prod.fst ∘ w) := by
    have := polytabloid_extendCol T.swapST (Prod.fst ∘ w)
    rw [swapST_nuTableau] at this
    exact this
  have hC := polytabloid_extendCol T (Prod.snd ∘ w)
  rw [hR, hC, smul_eq_mul, smul_eq_mul]
  ring

end restrict

section support

variable {m a b : ℕ} (T : StripTableau a b (staircase (m - 1)) (staircase m))

/-- Expansion of `w_m` as a double sum over the two column groups. -/
theorem wm_eq_sum :
    wm T.t = ∑ g : columnGroup (swapTableau T.t), ∑ g' : columnGroup T.t,
      ((((Perm.sign (g : Perm (Fin (a + b)))) : ℤ) : ℂ) * (((Perm.sign (g' : Perm (Fin (a + b)))) : ℤ) : ℂ)) •
        (Pi.single (pairWordRC T.t (g : Perm (Fin (a + b))) (g' : Perm (Fin (a + b)))) 1 :
          WordSpaceL (a + b) (Fin (dR m) × Fin (dR m))) := by
  rw [wm, polytabloid_eq_sum, polytabloid_eq_sum, TensorProduct.sum_tmul, map_sum]
  refine sum_congr rfl fun g _ => ?_
  rw [TensorProduct.tmul_sum, map_sum]
  refine sum_congr rfl fun g' _ => ?_
  rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_smul, map_smul, smul_smul,
    pairLift_tmul, pairMul_single]
  rfl

/-- Words in the support of `w_m` are pair words of column-group elements. -/
theorem exists_of_wm_ne_zero {u : Fin (a + b) → Fin (dR m) × Fin (dR m)} (hu : wm T.t u ≠ 0) :
    ∃ g ∈ columnGroup (swapTableau T.t), ∃ g' ∈ columnGroup T.t, u = pairWordRC T.t g g' := by
  by_contra hcon
  push Not at hcon
  apply hu
  rw [wm_eq_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun g _ => ?_
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun g' _ => ?_
  rw [Pi.smul_apply, Pi.single_eq_of_ne (hcon g g.2 g' g'.2), smul_zero]

/-- The low letter `(0, 0)`. -/
def lowLetter (m : ℕ) (hm : 1 ≤ m) : Fin (dR m) × Fin (dR m) :=
  (⟨0, by have := dR_eq m; omega⟩, ⟨0, by have := dR_eq m; omega⟩)

theorem lowLetter_fst (hm : 1 ≤ m) : ((lowLetter m hm).1 : ℕ) = 0 := rfl
theorem lowLetter_snd (hm : 1 ≤ m) : ((lowLetter m hm).2 : ℕ) = 0 := rfl

/-- For an unmixed word in the support of `w_m`, the low positions are the last `b` positions. -/
theorem letterSet_eq_lastPositions (hm : 1 ≤ m) {u : Fin (a + b) → Fin (dR m) × Fin (dR m)}
    (hu : wm T.t u ≠ 0) (hum : ∀ p, Unmixed (u p)) :
    letterSet (lowLetter m hm) u = (lastPositions a b).1 := by
  obtain ⟨g, hg, g', hg', rfl⟩ := exists_of_wm_ne_zero T hu
  have hgr : ∀ p, rowOf T.t (g p) = rowOf T.t p := (mem_columnGroup_swapTableau T.t g).1 hg
  have hgc : ∀ p, colOf T.t (g' p) = colOf T.t p := (mem_columnGroup T.t).1 hg'
  ext p
  rw [mem_letterSet, mem_lastPositions]
  have hlow : pairWordRC T.t g g' p = lowLetter m hm ↔ colOf T.t (g⁻¹ p) = 0 := by
    constructor
    · intro h
      have := congrArg (fun x => (x.1 : ℕ)) h
      rw [lowLetter_fst] at this
      simpa [pairWordRC_fst] using this
    · intro h
      have hu' := hum p; unfold Unmixed at hu'
      rw [pairWordRC_fst, pairWordRC_snd] at hu'
      apply Prod.ext <;> apply Fin.ext
      · rw [lowLetter_fst]; simpa [pairWordRC_fst] using h
      · rw [lowLetter_snd]; simpa [pairWordRC_snd] using hu'.1 h
  rw [hlow, low_iff_band T.t hgr hgc hum p]
  constructor
  · intro h
    rcases StripTableau.exists_castAdd_or_natAdd p with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · have h1 : rowOf T.t (Fin.castAdd b i) + 1 + colOf T.t (Fin.castAdd b i) < m :=
        castAdd_not_band T i
      omega
    · exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    have h1 : rowOf T.t (Fin.natAdd a j) + 1 + colOf T.t (Fin.natAdd a j) = m := natAdd_band T j
    show rowOf T.t (Fin.natAdd a j) + colOf T.t (Fin.natAdd a j) = m - 1
    omega

theorem sectorProj_of_support {n : ℕ} {L : Type} [Fintype L] [DecidableEq L] (ℓ₀ : L) (b : ℕ)
    (A : Subsets n b) (f : WordSpaceL n L) (hf : ∀ u, f u ≠ 0 → letterSet ℓ₀ u = A.1) :
    sectorProj ℓ₀ b A f = f := by
  funext u
  rw [sectorProj_apply]
  by_cases h : f u = 0
  · rw [h]; split_ifs <;> rfl
  · rw [if_pos (hf u h)]

/-- `z = P₁ w_m` lies in the sector `D = lastPositions`. -/
theorem sectorProj_unmixedProj_wm (hm : 1 ≤ m) :
    sectorProj (lowLetter m hm) b (lastPositions a b) (unmixedProj (wm T.t)) =
      unmixedProj (wm T.t) := by
  apply sectorProj_of_support
  intro u hu
  rw [unmixedProj_apply] at hu
  split_ifs at hu with hum
  · exact letterSet_eq_lastPositions T hm hu hum
  · exact absurd rfl hu

end support

section step

variable {m a b : ℕ} (T : StripTableau a b (staircase (m - 1)) (staircase m))

/-- **Prop 4.2 (s = 1), step form.**  If `S^ν` occurs in `W_{m-1}` and `λ/ν` is a horizontal
strip, then `S^λ` occurs in `W_m`. -/
theorem band1_step (hm : 1 ≤ m) {ν lam : YoungDiagram} (Tl : StripTableau a b ν lam) (hle' : ν ≤ lam)
    (hstrip : HorizontalStrip ν lam) (hd : ν.colLen 0 ≤ lam.colLen 0)
    (hν : Occurs (Tl.nuTableau hle') (Wm (T.nuTableau (staircase_mono m))).toRepresentation) :
    Occurs Tl.t (Wm T.t).toRepresentation := by
  set z := unmixedProj (wm T.t) with hz
  set Wh := Wm (T.nuTableau (staircase_mono m)) with hWh
  obtain ⟨c, hc0, hRz⟩ : ∃ c : ℂ, c ≠ 0 ∧ Rpair T z = c • wm (T.nuTableau (staircase_mono m)) :=
    ⟨_, mul_ne_zero (sign_ne_zero _) (sign_ne_zero _), Rpair_unmixedProj_wm T⟩
  obtain ⟨f, hf⟩ := Tl.exists_pair_intertwiner_of_occurs hle' hstrip hd hν
  have hR : ∀ y ∈ cycH (pairRepR m (a + b)) z embPair, Rpair T y ∈ Wh := by
    intro y hy
    rw [mem_cycH_iff] at hy
    refine Submodule.span_induction (p := fun y _ => Rpair T y ∈ Wh) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨p, rfl⟩
      dsimp only
      rw [resStab_apply, Rpair_wordRep, hRz, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p.1, rfl⟩)
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx
  let R : IntertwiningMap (cycH (pairRepR m (a + b)) z embPair).toRepresentation
      (pairRep (b := b) Wh.toRepresentation) :=
    { toLinearMap := (Rpair T).restrict fun y hy => hR y hy
      isIntertwining' := fun p => LinearMap.ext fun y => Subtype.ext (by
        show Rpair T (pairRepR m (a + b) (embPair p) (y : WordSpaceL (a + b) _)) =
          pairRepR (m - 1) a p.1 (Rpair T (y : WordSpaceL (a + b) _))
        exact Rpair_wordRep T p y.1) }
  have hRsurj : Function.Surjective R := by
    intro y
    have hy : (y : WordSpaceL a _) ∈ (cycH (pairRepR m (a + b)) z embPair).toSubmodule.map (Rpair T) := by
      have hle'' : Wh.toSubmodule ≤ (cycH (pairRepR m (a + b)) z embPair).toSubmodule.map (Rpair T) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨σ, rfl⟩
        refine ⟨c⁻¹ • pairRepR m (a + b) (embPair (σ, 1)) z,
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨(σ, 1), rfl⟩), ?_⟩
        rw [map_smul, Rpair_wordRep, hRz, map_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      exact hle'' y.2
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hφ : f.comp R ≠ 0 := by
    intro h0
    apply hf
    refine DFunLike.ext f 0 fun y => ?_
    obtain ⟨x, rfl⟩ := hRsurj y
    exact congrArg (fun k => k x) h0
  obtain ⟨Φ, hΦ⟩ := exists_extension_of_sectors (pairRepR m (a + b)) (lastPositions a b) z embPair
    (sectorProj (lowLetter m hm) b) (sectorProj_disj _ _) (sectorProj_equiv _ _)
    (sectorProj_unmixedProj_wm T hm) embPair_smul_lastPositions
    (fun g hg => (exists_embPair_of_smul_eq hg).imp fun p hp => hp.symm)
    (spechtRep Tl.t) (f.comp R)
  have hΦ0 : Φ ≠ 0 := by
    intro h0
    apply hφ
    refine DFunLike.ext _ 0 fun y => ?_
    have := hΦ y y.2
    rw [h0] at this
    exact this.symm
  have hocc : Occurs Tl.t (cycG (pairRepR m (a + b)) z).toRepresentation :=
    occurs_of_intertwiner_to Tl.t Φ hΦ0
  let P : IntertwiningMap (Wm T.t).toRepresentation (pairRepR m (a + b)) :=
    { toLinearMap := unmixedProj ∘ₗ (Wm T.t).toSubmodule.subtype
      isIntertwining' := fun g => LinearMap.ext fun x => by
        show unmixedProj (pairRepR m (a + b) g (x : WordSpaceL (a + b) _)) =
          pairRepR m (a + b) g (unmixedProj (x : WordSpaceL (a + b) _))
        exact unmixedProj_wordRep g x.1 }
  have hle3 : (cycG (pairRepR m (a + b)) z).toSubmodule ≤ P.range.toSubmodule := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    exact P.range.apply_mem_toSubmodule g ⟨⟨wm T.t, Submodule.subset_span ⟨1, by simp⟩⟩, rfl⟩
  exact Occurs.of_surjective _ (corestrict P) (StripTableau.corestrict_surjective _)
    (occurs_of_le _ hle3 hocc)

end step

end OAI.Saxl
