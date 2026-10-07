import Mathlib
import Saxl.Band2Margin
import Saxl.Band1

/-!
# The transversal lemma for a band of any width `s`

Pair letters `(a, b)` with both entries `< s` are *low*, with both `≥ s` are *high*; `UnmixedS s`
says the two entries are on the same side.  `unmixedProjS s` is the paper's `P_s`.  For a
row-preserving `g` and a column-preserving `g'` whose pair word is unmixed, the high positions are
exactly those whose cell lies in the smaller staircase `ρ_{m-s}` (paper eqs. (4.6)–(4.7)), by the
margin lemma.
-/

namespace OAI.Saxl

open Equiv YoungDiagram Finset

section proj

variable {m N : ℕ}

/-- Unmixed at threshold `s`: both entries `< s` or both `≥ s`. -/
def UnmixedS (s : ℕ) (ab : Fin (dR m) × Fin (dR m)) : Prop := ((ab.1 : ℕ) < s ↔ (ab.2 : ℕ) < s)

instance (s : ℕ) (ab : Fin (dR m) × Fin (dR m)) : Decidable (UnmixedS s ab) := by
  unfold UnmixedS; infer_instance

/-- The letterwise projection `P_s` killing words with a mixed position. -/
def unmixedProjS (s : ℕ) :
    WordSpaceL N (Fin (dR m) × Fin (dR m)) →ₗ[ℂ] WordSpaceL N (Fin (dR m) × Fin (dR m)) where
  toFun f u := if ∀ p, UnmixedS s (u p) then f u else 0
  map_add' f g := by funext u; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c f := by
    funext u; simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; split_ifs <;> simp

theorem unmixedProjS_apply (s : ℕ) (f : WordSpaceL N (Fin (dR m) × Fin (dR m)))
    (u : Fin N → Fin (dR m) × Fin (dR m)) :
    unmixedProjS s f u = if ∀ p, UnmixedS s (u p) then f u else 0 := rfl

theorem unmixedProjS_wordRep (s : ℕ) (g : Perm (Fin N)) (f : WordSpaceL N (Fin (dR m) × Fin (dR m))) :
    unmixedProjS s (wordRepL N _ g f) = wordRepL N _ g (unmixedProjS s f) := by
  funext u
  rw [unmixedProjS_apply, wordRepL_apply, wordRepL_apply, unmixedProjS_apply]
  have : (∀ p, UnmixedS s ((u ∘ g) p)) ↔ ∀ p, UnmixedS s (u p) :=
    ⟨fun h p => by simpa using h (g.symm p), fun h p => h _⟩
  by_cases h : ∀ p, UnmixedS s (u p)
  · rw [if_pos h, if_pos (this.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]

end proj

section counts

variable {m N : ℕ} (t : Tableau N (staircase m))

/-- Row `i` has `m - i - s` positions whose column is `≥ s`. -/
theorem card_rowFiber_filter_colOf (i s : ℕ) :
    ((rowFiber t i).filter fun q => s ≤ colOf t q).card = m - i - s := by
  rw [← Nat.card_Ico s (m - i)]
  refine card_bij (fun p _ => colOf t p) ?_ ?_ ?_
  · intro p hp
    rw [mem_filter, mem_rowFiber] at hp
    rw [mem_Ico]
    have := rowOf_add_colOf_lt t p
    exact ⟨hp.2, by omega⟩
  · intro p hp q hq hpq
    rw [mem_filter, mem_rowFiber] at hp hq
    apply t.injective; apply Subtype.ext
    exact Prod.ext (hp.1.trans hq.1.symm) hpq
  · intro j hj
    rw [mem_Ico] at hj
    have hcell : (i, j) ∈ (staircase m).cells := by rw [mem_cells, mem_staircase]; omega
    refine ⟨t.symm ⟨(i, j), hcell⟩, ?_, ?_⟩
    · rw [mem_filter, mem_rowFiber]
      refine ⟨?_, ?_⟩
      · show (t (t.symm _)).val.1 = i; simp
      · show s ≤ (t (t.symm _)).val.2; simp [hj.1]
    · show (t (t.symm _)).val.2 = j; simp

/-- Column `j` has `m - j - s` positions whose row is `≥ s`. -/
theorem card_colFiber_filter_rowOf (j s : ℕ) :
    ((colFiber t j).filter fun q => s ≤ rowOf t q).card = m - j - s := by
  rw [← Nat.card_Ico s (m - j)]
  refine card_bij (fun p _ => rowOf t p) ?_ ?_ ?_
  · intro p hp
    rw [mem_filter, mem_colFiber] at hp
    rw [mem_Ico]
    have := rowOf_add_colOf_lt t p
    exact ⟨hp.2, by omega⟩
  · intro p hp q hq hpq
    rw [mem_filter, mem_colFiber] at hp hq
    apply t.injective; apply Subtype.ext
    exact Prod.ext hpq (hp.1.trans hq.1.symm)
  · intro i hi
    rw [mem_Ico] at hi
    have hcell : (i, j) ∈ (staircase m).cells := by rw [mem_cells, mem_staircase]; omega
    refine ⟨t.symm ⟨(i, j), hcell⟩, ?_, ?_⟩
    · rw [mem_filter, mem_colFiber]
      refine ⟨?_, ?_⟩
      · show (t (t.symm _)).val.2 = j; simp
      · show s ≤ (t (t.symm _)).val.1; simp [hi.1]
    · show (t (t.symm _)).val.1 = i; simp

theorem inv_preserves_rowOf {g : Perm (Fin N)} (hg : ∀ p, rowOf t (g p) = rowOf t p) (p : Fin N) :
    rowOf t (g⁻¹ p) = rowOf t p := by
  have := hg (g⁻¹ p)
  rw [show g (g⁻¹ p) = p by rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]] at this
  exact this.symm

theorem inv_preserves_colOf {g : Perm (Fin N)} (hg : ∀ p, colOf t (g p) = colOf t p) (p : Fin N) :
    colOf t (g⁻¹ p) = colOf t p := by
  have := hg (g⁻¹ p)
  rw [show g (g⁻¹ p) = p by rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]] at this
  exact this.symm

/-- Row-preserving `g`: row `i` has `m - i - s` positions with first letter `≥ s`. -/
theorem card_rowFiber_high {g : Perm (Fin N)} (hg : ∀ p, rowOf t (g p) = rowOf t p) (i s : ℕ) :
    ((rowFiber t i).filter fun p => s ≤ colOf t (g⁻¹ p)).card = m - i - s := by
  rw [← card_rowFiber_filter_colOf t i s]
  refine card_bij (fun p _ => g⁻¹ p) ?_ ?_ ?_
  · intro p hp
    rw [mem_filter, mem_rowFiber] at hp ⊢
    rw [inv_preserves_rowOf t hg]
    exact hp
  · intro p _ q _ h
    exact g⁻¹.injective h
  · intro q hq
    refine ⟨g q, ?_, by rw [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]⟩
    rw [mem_filter, mem_rowFiber] at hq ⊢
    rw [hg, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]
    exact hq

/-- Column-preserving `g'`: column `j` has `m - j - s` positions with second letter `≥ s`. -/
theorem card_colFiber_high {g' : Perm (Fin N)} (hg' : ∀ p, colOf t (g' p) = colOf t p) (j s : ℕ) :
    ((colFiber t j).filter fun p => s ≤ rowOf t (g'⁻¹ p)).card = m - j - s := by
  rw [← card_colFiber_filter_rowOf t j s]
  refine card_bij (fun p _ => g'⁻¹ p) ?_ ?_ ?_
  · intro p hp
    rw [mem_filter, mem_colFiber] at hp ⊢
    rw [inv_preserves_colOf t hg']
    exact hp
  · intro p _ q _ h
    exact g'⁻¹.injective h
  · intro q hq
    refine ⟨g' q, ?_, by rw [← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]⟩
    rw [mem_filter, mem_colFiber] at hq ⊢
    rw [hg', ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]
    exact hq

end counts

section transversal

variable {m N : ℕ} (t : Tableau N (staircase m))

/-- **Transversal lemma (any width).**  For a row-preserving `g` and a column-preserving `g'`
with unmixed pair word, the positions with high first letter are exactly those whose cell lies in
`ρ_{m-s}`. -/
theorem high_iff_mem_small {s : ℕ} {g g' : Perm (Fin N)} (hg : ∀ p, rowOf t (g p) = rowOf t p)
    (hg' : ∀ p, colOf t (g' p) = colOf t p)
    (hu : ∀ p, UnmixedS s (pairWordRC t g g' p)) (p : Fin N) :
    s ≤ colOf t (g⁻¹ p) ↔ (t p).val ∈ (staircase (m - s)).cells := by
  classical
  set H : Finset (Fin N) := univ.filter fun q => s ≤ colOf t (g⁻¹ q) with hH
  have hH2 : ∀ q, q ∈ H ↔ s ≤ rowOf t (g'⁻¹ q) := fun q => by
    rw [hH, mem_filter]; simp only [mem_univ, true_and]
    have := hu q; unfold UnmixedS at this
    rw [pairWordRC_fst, pairWordRC_snd] at this
    rw [not_lt.symm, not_lt.symm]
    exact not_congr this
  set A : Finset (ℕ × ℕ) := H.image fun q => (t q).val with hA
  have hinj : Function.Injective fun q : Fin N => (t q).val := fun a b h =>
    t.injective (Subtype.ext h)
  have hAsub : A ⊆ (staircase m).cells := by
    intro c hc
    rw [hA, mem_image] at hc
    obtain ⟨q, _, rfl⟩ := hc
    exact (t q).2
  have hrow : ∀ i, (A.filter fun c => c.1 = i).card = m - s - i := by
    intro i
    rw [hA, filter_image, card_image_of_injective _ hinj]
    rw [Nat.sub_right_comm, ← card_rowFiber_high t hg i s]
    congr 1
    ext q
    rw [mem_filter, hH, mem_filter, mem_filter, mem_rowFiber]
    simp only [mem_univ, true_and]
    exact and_comm
  have hcol : ∀ j, (A.filter fun c => c.2 = j).card = m - s - j := by
    intro j
    rw [hA, filter_image, card_image_of_injective _ hinj]
    rw [Nat.sub_right_comm, ← card_colFiber_high t hg' j s]
    congr 1
    ext q
    rw [mem_filter, hH2, mem_filter, mem_colFiber]
    exact and_comm
  have hAeq := eq_staircase_of_margins hAsub hrow hcol
  have hp : s ≤ colOf t (g⁻¹ p) ↔ p ∈ H := by rw [hH, mem_filter]; simp
  rw [hp, ← hAeq, hA, mem_image]
  constructor
  · intro h; exact ⟨p, h, rfl⟩
  · rintro ⟨q, hq, hqp⟩
    rw [hinj hqp] at hq
    exact hq

end transversal

end OAI.Saxl
