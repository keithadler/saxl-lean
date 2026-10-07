import Mathlib
import Saxl.Dominance
import Saxl.Strips

/-!
# Young's rule, combinatorial half (paper Lemma 2.3)

`SizedChain θ ℓ ν λ` : `λ` is reached from `ν` by `ℓ` horizontal strips, the `k`-th (0-indexed,
counted from `ν`) of size `θ k`.  Main results:

* `sizedChain_of_dominates` : `τ ⊵ θ` and `|τ| = |θ|` give `SizedChain θ.rowLen (rows θ) ⊥ τ`;
* `dominates_of_sizedChain` : the converse, plus each intermediate diagram has `≤ k` rows.
-/

namespace OAI.Saxl

open YoungDiagram

theorem rowLen_le_of_le {ν τ : YoungDiagram} (h : ν ≤ τ) (i : ℕ) : ν.rowLen i ≤ τ.rowLen i := by
  by_contra hc
  push Not at hc
  have : (i, τ.rowLen i) ∈ ν := by rw [mem_iff_lt_rowLen]; exact hc
  have := h this
  rw [mem_iff_lt_rowLen] at this
  omega

theorem colLen_le_of_le {ν τ : YoungDiagram} (h : ν ≤ τ) (j : ℕ) : ν.colLen j ≤ τ.colLen j := by
  by_contra hc
  push Not at hc
  have : (τ.colLen j, j) ∈ ν := by rw [mem_iff_lt_colLen]; exact hc
  have := h this
  rw [mem_iff_lt_colLen] at this
  omega

theorem rowSum_le_of_le {ν τ : YoungDiagram} (h : ν ≤ τ) (k : ℕ) : rowSum ν k ≤ rowSum τ k :=
  Finset.sum_le_sum fun i _ => rowLen_le_of_le h i

theorem eq_bot_of_card_eq_zero {τ : YoungDiagram} (h : τ.card = 0) : τ = ⊥ := by
  ext c
  simp only [mem_cells, YoungDiagram.cells_bot, Finset.notMem_empty, iff_false]
  intro hc
  have : τ.cells.Nonempty := ⟨c, hc⟩
  have := Finset.card_pos.2 this
  have h' : τ.cells.card = 0 := h
  omega

/-! ### Shaving the `t` tallest columns -/

/-- Row lengths after removing the bottom box of each of the `t` tallest columns
(rightmost first among equal heights). -/
def shaveRow (τ : YoungDiagram) (t i : ℕ) : ℕ := (τ.rowLen i - t) + min (τ.rowLen (i + 1)) t

theorem shaveRow_anti (τ : YoungDiagram) (t : ℕ) {i i' : ℕ} (h : i ≤ i') :
    shaveRow τ t i' ≤ shaveRow τ t i := by
  unfold shaveRow
  have := τ.rowLen_anti i i' h
  have := τ.rowLen_anti (i + 1) (i' + 1) (by omega)
  omega

theorem shaveRow_le (τ : YoungDiagram) (t i : ℕ) : shaveRow τ t i ≤ τ.rowLen i := by
  unfold shaveRow
  have := τ.rowLen_anti i (i + 1) (by omega)
  omega

theorem lt_shaveRow_of_lt_rowLen_succ (τ : YoungDiagram) (t : ℕ) {i j : ℕ}
    (h : j < τ.rowLen (i + 1)) : j < shaveRow τ t i := by
  unfold shaveRow
  have := τ.rowLen_anti i (i + 1) (by omega)
  omega

/-- The shaved diagram. -/
def shave (τ : YoungDiagram) (t : ℕ) : YoungDiagram where
  cells := (Finset.range (τ.colLen 0) ×ˢ Finset.range (τ.rowLen 0)).filter
    (fun c => c.2 < shaveRow τ t c.1)
  isLowerSet := by
    intro x y hxy hx
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_ofPred_eq] at hx ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    have := shaveRow_anti τ t hxy.1
    have := hxy.1
    have := hxy.2
    exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem mem_shave {τ : YoungDiagram} {t i j : ℕ} : (i, j) ∈ shave τ t ↔ j < shaveRow τ t i := by
  rw [← mem_cells]
  simp only [shave, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨?_, ?_⟩, h⟩
    · by_contra hi
      push Not at hi
      have := rowLen_eq_zero_of_le hi
      have := rowLen_eq_zero_of_le (show τ.colLen 0 ≤ i + 1 by omega)
      unfold shaveRow at h
      omega
    · have := shaveRow_le τ t i
      have := τ.rowLen_anti 0 i (Nat.zero_le _)
      omega

theorem rowLen_shave (τ : YoungDiagram) (t i : ℕ) : (shave τ t).rowLen i = shaveRow τ t i :=
  nat_eq_of_lt_iff fun j => by rw [← mem_iff_lt_rowLen, mem_shave]

theorem shave_le (τ : YoungDiagram) (t : ℕ) : shave τ t ≤ τ := by
  intro c hc
  obtain ⟨i, j⟩ := c
  rw [mem_shave] at hc
  rw [mem_iff_lt_rowLen]
  exact lt_of_lt_of_le hc (shaveRow_le τ t i)

theorem horizontalStrip_shave (τ : YoungDiagram) (t : ℕ) : HorizontalStrip (shave τ t) τ := by
  refine ⟨shave_le τ t, fun j => ?_⟩
  by_contra h
  push Not at h
  have h1 : ((shave τ t).colLen j + 1, j) ∈ τ := by rw [mem_iff_lt_colLen]; omega
  rw [mem_iff_lt_rowLen] at h1
  have h2 : ((shave τ t).colLen j, j) ∈ shave τ t := by
    rw [mem_shave]; exact lt_shaveRow_of_lt_rowLen_succ τ t h1
  rw [mem_iff_lt_colLen] at h2
  omega

/-- Telescoping identity behind the card and row-sum formulas. -/
theorem sum_shaveRow_add (τ : YoungDiagram) {t : ℕ} (ht : t ≤ τ.rowLen 0) (k : ℕ) :
    ∑ i ∈ Finset.range k, shaveRow τ t i + t =
      ∑ i ∈ Finset.range k, τ.rowLen i + min (τ.rowLen k) t := by
  induction k with
  | zero => simp [ht]
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    unfold shaveRow at ih ⊢
    have := τ.rowLen_anti k (k + 1) (by omega)
    omega

theorem rowSum_shave_add (τ : YoungDiagram) {t : ℕ} (ht : t ≤ τ.rowLen 0) (k : ℕ) :
    rowSum (shave τ t) k + t = rowSum τ k + min (τ.rowLen k) t := by
  unfold rowSum
  simp only [rowLen_shave]
  exact sum_shaveRow_add τ ht k

theorem card_shave_add (τ : YoungDiagram) {t : ℕ} (ht : t ≤ τ.rowLen 0) :
    (shave τ t).card + t = τ.card := by
  have hN : (shave τ t).colLen 0 ≤ τ.colLen 0 := colLen_le_of_le (shave_le τ t) 0
  rw [← sum_rowLen_eq_card (shave τ t) hN, ← sum_rowLen_eq_card τ le_rfl]
  have := rowSum_shave_add τ ht (τ.colLen 0)
  unfold rowSum at this
  rw [rowLen_eq_zero_of_le le_rfl] at this
  simpa using this

/-! ### Sized chains -/

/-- `SizedChain θ ℓ ν λ` : `ℓ` horizontal strips from `ν` up to `λ`, the `k`-th of size `θ k`. -/
inductive SizedChain (θ : ℕ → ℕ) : ℕ → YoungDiagram → YoungDiagram → Prop
  | zero (ν : YoungDiagram) : SizedChain θ 0 ν ν
  | succ {ℓ : ℕ} {ν μ lam : YoungDiagram} :
      SizedChain θ ℓ ν μ → HorizontalStrip μ lam → μ.card + θ ℓ = lam.card →
        SizedChain θ (ℓ + 1) ν lam

theorem SizedChain.congr {θ θ' : ℕ → ℕ} {ℓ : ℕ} {ν lam : YoungDiagram}
    (h : SizedChain θ ℓ ν lam) (he : ∀ i < ℓ, θ i = θ' i) : SizedChain θ' ℓ ν lam := by
  induction h with
  | zero ν => exact .zero ν
  | succ hc hs hcard ih =>
    exact .succ (ih fun i hi => he i (by omega)) hs (by rw [← he _ (by omega)]; exact hcard)

/-- Sufficiency in Young's rule: dominance gives a sized strip chain from `⊥`. -/
theorem sizedChain_of_dominates_aux (ℓ : ℕ) :
    ∀ (θ : ℕ → ℕ) (τ : YoungDiagram), (∀ i i', i ≤ i' → θ i' ≤ θ i) →
      ∑ i ∈ Finset.range ℓ, θ i = τ.card →
      (∀ k ≤ ℓ, ∑ i ∈ Finset.range k, θ i ≤ rowSum τ k) →
      SizedChain θ ℓ ⊥ τ := by
  induction ℓ with
  | zero =>
    intro θ τ _ hsum _
    simp at hsum
    rw [eq_bot_of_card_eq_zero hsum.symm]
    exact .zero ⊥
  | succ ℓ ih =>
    intro θ τ hθ hsum hdom
    set t := θ ℓ with ht
    have ht0 : t ≤ τ.rowLen 0 := by
      have h1 := hdom 1 (by omega)
      have h2 := hθ 0 ℓ (Nat.zero_le _)
      simp only [rowSum, Finset.sum_range_one] at h1
      omega
    have hcard := card_shave_add τ ht0
    refine .succ (ih θ (shave τ t) hθ ?_ ?_) (horizontalStrip_shave τ t) hcard
    · rw [Finset.sum_range_succ] at hsum; omega
    · intro k hk
      have h1 := rowSum_shave_add τ ht0 k
      have h2 := hdom k (by omega)
      have h3 := hdom (k + 1) (by omega)
      rw [Finset.sum_range_succ] at h3
      have h4 : rowSum τ (k + 1) = rowSum τ k + τ.rowLen k := by
        unfold rowSum; rw [Finset.sum_range_succ]
      have h5 := hθ k ℓ (by omega)
      omega

/-- Young's rule, sufficiency, for diagrams: `τ ⊵ θ` and `|τ| = |θ|` give a chain of strips
with sizes the rows of `θ`. -/
theorem sizedChain_of_dominates {τ θ : YoungDiagram} (hd : Dominates τ θ) (hc : τ.card = θ.card) :
    SizedChain θ.rowLen (θ.colLen 0) ⊥ τ := by
  apply sizedChain_of_dominates_aux
  · exact fun i i' h => θ.rowLen_anti i i' h
  · rw [sum_rowLen_eq_card θ le_rfl]; exact hc.symm
  · exact fun k _ => hd k

/-! ### Necessity: a chain of `k` strips has at most `k` rows and forces dominance -/

theorem colLen_bot (j : ℕ) : (⊥ : YoungDiagram).colLen j = 0 :=
  nat_eq_of_lt_iff fun i => by rw [← mem_iff_lt_colLen]; simp

theorem SizedChain.colLen_zero_le {θ : ℕ → ℕ} {ℓ : ℕ} {lam : YoungDiagram}
    (h : SizedChain θ ℓ ⊥ lam) : lam.colLen 0 ≤ ℓ := by
  generalize hb : (⊥ : YoungDiagram) = b at h
  induction h with
  | zero ν => subst hb; rw [colLen_bot]
  | succ _ hs _ ih =>
    have := hs.2 0
    have := ih hb
    omega

theorem SizedChain.le {θ : ℕ → ℕ} {ℓ : ℕ} {ν lam : YoungDiagram}
    (h : SizedChain θ ℓ ν lam) : ν ≤ lam := by
  induction h with
  | zero ν => exact le_rfl
  | succ _ hs _ ih => exact ih.trans hs.1

theorem SizedChain.card {θ : ℕ → ℕ} {ℓ : ℕ} {lam : YoungDiagram}
    (h : SizedChain θ ℓ ⊥ lam) : lam.card = ∑ i ∈ Finset.range ℓ, θ i := by
  generalize hb : (⊥ : YoungDiagram) = b at h
  induction h with
  | zero ν => subst hb; simp
  | succ _ _ hcard ih => rw [Finset.sum_range_succ, ← ih hb]; omega

/-- Every prefix of a chain is a chain. -/
theorem SizedChain.prefix {θ : ℕ → ℕ} {ℓ : ℕ} {ν lam : YoungDiagram}
    (h : SizedChain θ ℓ ν lam) (k : ℕ) (hk : k ≤ ℓ) :
    ∃ μ, SizedChain θ k ν μ ∧ μ ≤ lam := by
  induction h with
  | zero ν => exact ⟨ν, by simpa [Nat.le_zero.1 hk] using SizedChain.zero ν, le_rfl⟩
  | @succ ℓ ν μ lam hc hs hcard ih =>
    rcases Nat.lt_or_ge k (ℓ + 1) with hlt | hge
    · obtain ⟨μ', h1, h2⟩ := ih (by omega)
      exact ⟨μ', h1, h2.trans hs.1⟩
    · have : k = ℓ + 1 := by omega
      subst this
      exact ⟨lam, .succ hc hs hcard, le_rfl⟩

/-- Necessity in Young's rule: a sized chain from `⊥` forces dominance. -/
theorem dominates_of_sizedChain {θ : ℕ → ℕ} {ℓ : ℕ} {τ : YoungDiagram}
    (h : SizedChain θ ℓ ⊥ τ) (k : ℕ) (hk : k ≤ ℓ) :
    ∑ i ∈ Finset.range k, θ i ≤ rowSum τ k := by
  obtain ⟨μ, hμ, hle⟩ := h.prefix k hk
  have h1 := hμ.card
  have h2 : rowSum μ k = μ.card := by
    rw [rowSum, sum_rowLen_eq_card μ hμ.colLen_zero_le]
  have h3 := rowSum_le_of_le hle k
  omega

end OAI.Saxl
