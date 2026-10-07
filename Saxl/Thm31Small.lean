import Mathlib
import Saxl.Band1Assembly
import Saxl.Bridge
import Saxl.LetterInj
import Saxl.CastN
import Saxl.Strips

/-!
# Theorem 3.1 for `m ≤ 4`, and Saxl's conjecture for staircases of size at most `10`

Case (ii) of the paper's induction only arises for `m ≥ 5`, so for `m ≤ 4` the induction needs only
Prop 3.2 (`prop32`), the strip reduction (`strip_reduction`) and the width-one band cut
(`band1_step`).  We conclude `TensorSquareCovers m` and positivity of the challenge's
`kronecker` for `m ≤ 4`.
-/

namespace OAI.Saxl

open Equiv YoungDiagram Finset Representation

open scoped TensorProduct

section tableauIndependence

/-- The orbit span is unchanged by moving the generator along the orbit. -/
theorem cycG_apply {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) (z : V) : cycG ρ (ρ g z) = cycG ρ z := by
  apply Subrepresentation.toSubmodule_injective
  show Submodule.span ℂ _ = Submodule.span ℂ _
  congr 1
  ext f
  simp only [Set.mem_range]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h * g, by rw [map_mul, Module.End.mul_apply]⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h * g⁻¹, by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]⟩

variable {m n : ℕ}

theorem shift_swapTableau (t₁ t₂ : Tableau n (staircase m)) :
    shift (swapTableau t₁) (swapTableau t₂) = shift t₁ t₂ := by
  ext i
  simp [shift, swapTableau]

/-- `W_m` does not depend on the staircase tableau. -/
theorem Wm_eq (t₁ t₂ : Tableau n (staircase m)) : Wm t₁ = Wm t₂ := by
  have h1 : polytabloid t₁ = wordRep n (dR m) (shift t₁ t₂)⁻¹ (polytabloid t₂) :=
    polytabloid_eq_wordRep t₁ t₂
  have h2 : polytabloid (swapTableau t₁) =
      wordRep n (dR m) (shift t₁ t₂)⁻¹ (polytabloid (swapTableau t₂)) := by
    rw [polytabloid_eq_wordRep (swapTableau t₁) (swapTableau t₂), shift_swapTableau]
  have hw : wm t₁ = pairRepR m n (shift t₁ t₂)⁻¹ (wm t₂) := by
    rw [wm, wm, h1, h2, ← pairLift_tprod, Representation.tprod_apply, TensorProduct.map_tmul]
    rfl
  rw [Wm, Wm, hw, cycG_apply]

end tableauIndependence

section cast

variable {m n n' : ℕ} (e : Fin n ≃ Fin n')

theorem castTableau_swapTableau (t : Tableau n (staircase m)) :
    castTableau e (swapTableau t) = swapTableau (castTableau e t) := rfl

theorem wordCast_pairLift {L L' : Type} (x : WordSpaceL n L) (y : WordSpaceL n L') :
    wordCast e (pairLift (x ⊗ₜ[ℂ] y)) = pairLift (wordCast e x ⊗ₜ[ℂ] wordCast e y) := by
  funext u; rfl

theorem wm_castTableau (t : Tableau n (staircase m)) :
    wm (castTableau e t) = wordCast e (wm t) := by
  rw [wm, wm, wordCast_pairLift, ← polytabloid_castTableau, ← polytabloid_castTableau,
    castTableau_swapTableau]

theorem wordCast_mem_cycG' {L : Type} (z : WordSpaceL n L) {x : WordSpaceL n L}
    (hx : x ∈ cycG (wordRepL n L) z) : wordCast e x ∈ cycG (wordRepL n' L) (wordCast e z) := by
  rw [mem_cycG_iff] at hx
  refine Submodule.span_induction
    (p := fun x _ => wordCast e x ∈ cycG (wordRepL n' L) (wordCast e z)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨g, rfl⟩
    dsimp only
    rw [wordCast_wordRepL]
    exact Submodule.subset_span ⟨permHom e g, rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- Occurrence in `W_m` transports along a position bijection. -/
theorem occurs_Wm_castN {lam : YoungDiagram} (tl : Tableau n lam) (t : Tableau n (staircase m))
    (h : Occurs tl (Wm t).toRepresentation) :
    Occurs (castTableau e tl) (Wm (castTableau e t)).toRepresentation := by
  apply occurs_castN e tl
  obtain ⟨f, hf⟩ := h
  have hmem : ∀ x ∈ Wm t, wordCast e x ∈ Wm (castTableau e t) := by
    intro x hx
    rw [Wm, wm_castTableau]
    exact wordCast_mem_cycG' e _ hx
  let R : IntertwiningMap (Wm t).toRepresentation
      (pullback e (Wm (castTableau e t)).toRepresentation) :=
    { toLinearMap := (wordCast e).toLinearMap.restrict fun x hx => hmem x hx
      isIntertwining' := fun g => LinearMap.ext fun x => Subtype.ext (by
        show wordCast e (wordRepL n (Fin (dR m) × Fin (dR m)) g
            (x : WordSpaceL n (Fin (dR m) × Fin (dR m)))) =
          wordRepL n' (Fin (dR m) × Fin (dR m)) (permHom e g)
            (wordCast e (x : WordSpaceL n (Fin (dR m) × Fin (dR m))))
        exact wordCast_wordRepL e g x.1) }
  refine ⟨R.comp f, fun h0 => hf ?_⟩
  refine DFunLike.ext f 0 fun x => ?_
  have h1 : (R.comp f) x = 0 := by rw [h0]; rfl
  rw [IntertwiningMap.comp_apply] at h1
  have h2 : wordCast e (f x : WordSpaceL n (Fin (dR m) × Fin (dR m))) = 0 :=
    congrArg Subtype.val h1
  rw [LinearEquiv.map_eq_zero_iff] at h2
  exact Subtype.ext h2

end cast

section arith

theorem card_staircase_succ (m : ℕ) :
    (staircase (m + 1)).card = (staircase m).card + (m + 1) := by
  have h1 := two_mul_rowSum_staircase m le_rfl
  have h2 := two_mul_rowSum_staircase (m + 1) le_rfl
  rw [← card_staircase] at h1 h2
  rw [show 2 * m + 1 - m = m + 1 by omega] at h1
  rw [show 2 * (m + 1) + 1 - (m + 1) = m + 2 by omega] at h2
  have : (m + 1) * (m + 2) = m * (m + 1) + 2 * (m + 1) := by ring
  omega

/-- Every partition of `1` is dominated by the staircase `(1)`. -/
theorem dominates_staircase_one {lam : YoungDiagram} (h : lam.card = (staircase 1).card) :
    Dominates (staircase 1) lam := by
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [rowSum]
  · rw [rowSum_staircase_of_le 1 hk, ← h]
    exact rowSum_le_card lam k

end arith

section induction

/-- **Theorem 3.1 for `m ≤ 4`.** -/
theorem thm31_le4 (m : ℕ) (hm1 : 1 ≤ m) (hm4 : m ≤ 4) :
    ∀ (n : ℕ) (t : Tableau n (staircase m)) (lam : YoungDiagram) (tl : Tableau n lam),
      lam.card = (staircase m).card → Occurs tl (Wm t).toRepresentation := by
  induction m with
  | zero => omega
  | succ k ih =>
    intro n t lam tl hcard
    by_cases hdom : Dominates (staircase (k + 1)) lam
    · exact prop32 t tl hdom hcard
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact absurd (dominates_staircase_one hcard) hdom
    -- `m = k + 1 ≥ 2`: strip reduction; case (ii) is excluded by `m ≤ 4`
    rcases strip_reduction (show 2 ≤ k + 1 by omega) lam hcard hdom with ⟨ν, hs, hνc⟩ | ⟨h5, _⟩
    · have hN : n = (staircase (k + 1)).card := N_eq t
      have hcs := card_staircase_succ k
      have hνk : ν.card = (staircase k).card := by omega
      have hνk' : (staircase (k + 1 - 1)).card = ν.card := by
        rw [Nat.add_sub_cancel]; exact hνk.symm
      -- strip tableaux on `Fin (ν.card + (k + 1))`
      let Tl : StripTableau ν.card (k + 1) ν lam := stripTableauOf hs.1 rfl hνc
      let T : StripTableau ν.card (k + 1) (staircase (k + 1 - 1)) (staircase (k + 1)) :=
        stripTableauOf (staircase_mono (k + 1)) hνk' (by rw [hνk']; omega)
      have hih : Occurs (Tl.nuTableau hs.1)
          (Wm (T.nuTableau (staircase_mono (k + 1)))).toRepresentation :=
        ih (by omega) (by omega) ν.card (T.nuTableau (staircase_mono (k + 1))) ν
          (Tl.nuTableau hs.1) hνk
      have hstep : Occurs Tl.t (Wm T.t).toRepresentation :=
        band1_step T (by omega) Tl hs.1 hs (colLen_le_of_le hs.1 0) hih
      -- transport to `Fin n`
      have hcast : ν.card + (k + 1) = n := by omega
      let e : Fin (ν.card + (k + 1)) ≃ Fin n := finCongr hcast
      have h2 := occurs_Wm_castN e Tl.t T.t hstep
      rw [Wm_eq (castTableau e T.t) t] at h2
      exact occurs_of_occurs _ tl h2
    · omega

/-- **`TensorSquareCovers m` for `1 ≤ m ≤ 4`.** -/
theorem tensorSquareCovers_le4 (m : ℕ) (hm1 : 1 ≤ m) (hm4 : m ≤ 4) : TensorSquareCovers m :=
  tensorSquareCovers_of_Wm m fun μ hμ =>
    thm31_le4 m hm1 hm4 _ (canonicalTableau (staircase m) rfl) μ (canonicalTableau μ hμ) hμ

/-- **Saxl's conjecture for staircases of size `≤ 10`**, in the challenge's own terms. -/
theorem saxl_le4 (m : ℕ) (hm1 : 1 ≤ m) (hm4 : m ≤ 4) (μ : YoungDiagram)
    (hμ : μ.card = (staircase m).card) :
    0 < kronecker (canonicalTableau (staircase m) rfl) (canonicalTableau (staircase m) rfl)
      (canonicalTableau μ hμ) :=
  kronecker_pos_of_occurs _ _ _ (tensorSquareCovers_le4 m hm1 hm4 μ hμ)

end induction

end OAI.Saxl
