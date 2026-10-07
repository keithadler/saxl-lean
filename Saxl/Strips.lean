import Mathlib
import Saxl.Dominance
import Saxl.Staircase

/-!
# Horizontal strips (paper §6, Lemma 6.1)

`HorizontalStrip ν λ` : `ν ⊆ λ` and `λ/ν` has at most one box per column.
-/

namespace OAI.Saxl

open YoungDiagram

/-- `λ/ν` is a horizontal strip. -/
def HorizontalStrip (nu lam : YoungDiagram) : Prop :=
  nu ≤ lam ∧ ∀ j, lam.colLen j ≤ nu.colLen j + 1

/-! ### Full sweep: delete the first row -/

/-- The diagram with rows `(λ₂, λ₃, …)`. -/
def dropRow (lam : YoungDiagram) : YoungDiagram where
  cells := (lam.cells.filter (fun c => 1 ≤ c.1)).image (fun c => (c.1 - 1, c.2))
  isLowerSet := by
    intro x y hxy hx
    simp only [Finset.coe_image, Finset.coe_filter, Set.mem_image] at hx ⊢
    obtain ⟨c, ⟨hc, hc1⟩, rfl⟩ := hx
    refine ⟨(y.1 + 1, y.2), ⟨?_, by simp⟩, by simp⟩
    refine lam.isLowerSet (show (y.1 + 1, y.2) ≤ c from Prod.mk_le_mk.2 ⟨?_, ?_⟩) hc
    · have := hxy.1; simp at this ⊢; omega
    · exact hxy.2

theorem mem_dropRow {lam : YoungDiagram} {i j : ℕ} : (i, j) ∈ dropRow lam ↔ (i + 1, j) ∈ lam := by
  rw [← mem_cells, ← mem_cells (μ := lam)]
  simp only [dropRow, Finset.mem_image, Finset.mem_filter, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, ⟨h, ha⟩, rfl, rfl⟩
    have : a - 1 + 1 = a := by omega
    simpa [this] using h
  · intro h
    exact ⟨i + 1, j, ⟨h, by simp⟩, by simp, rfl⟩

theorem rowLen_dropRow (lam : YoungDiagram) (i : ℕ) : (dropRow lam).rowLen i = lam.rowLen (i + 1) :=
  nat_eq_of_lt_iff fun j => by
    rw [← mem_iff_lt_rowLen, ← mem_iff_lt_rowLen, mem_dropRow]

theorem colLen_dropRow_zero_succ (lam : YoungDiagram) :
    (dropRow lam).colLen 0 + 1 ≤ lam.colLen 0 ∨ (dropRow lam).colLen 0 = 0 := by
  rcases Nat.eq_zero_or_pos ((dropRow lam).colLen 0) with h | h
  · exact Or.inr h
  · left
    have : ((dropRow lam).colLen 0 - 1, 0) ∈ dropRow lam := by
      rw [mem_iff_lt_colLen]; omega
    rw [mem_dropRow, mem_iff_lt_colLen] at this
    omega

theorem card_dropRow (lam : YoungDiagram) : lam.card = (dropRow lam).card + lam.rowLen 0 := by
  have h1 : (dropRow lam).colLen 0 ≤ lam.colLen 0 := by
    rcases colLen_dropRow_zero_succ lam with h | h <;> omega
  rw [← sum_rowLen_eq_card lam (show lam.colLen 0 ≤ lam.colLen 0 + 1 by omega),
    ← sum_rowLen_eq_card (dropRow lam) h1, Finset.sum_range_succ']
  congr 1
  exact Finset.sum_congr rfl fun i _ => (rowLen_dropRow lam i).symm

/-- A full sweep removes a horizontal strip. -/
theorem horizontalStrip_dropRow (lam : YoungDiagram) : HorizontalStrip (dropRow lam) lam := by
  refine ⟨?_, ?_⟩
  · intro c hc
    obtain ⟨i, j⟩ := c
    rw [mem_dropRow] at hc
    exact lam.isLowerSet (Prod.mk_le_mk.2 ⟨Nat.le_succ i, le_rfl⟩) hc
  · intro j
    by_contra h
    push Not at h
    have : (lam.colLen j - 1, j) ∈ lam := by rw [mem_iff_lt_colLen]; omega
    have h2 : (lam.colLen j - 2, j) ∈ dropRow lam := by
      rw [mem_dropRow]
      have : lam.colLen j - 2 + 1 = lam.colLen j - 1 := by omega
      rwa [this]
    rw [mem_iff_lt_colLen] at h2
    omega

/-! ### Partial sweep: remove the bottom box of the rightmost `t` columns -/

/-- `card = ∑_{j<q} colLen j` once `q ≥ rowLen 0`. -/
theorem card_eq_sum_colLen (μ : YoungDiagram) {q : ℕ} (hq : μ.rowLen 0 ≤ q) :
    μ.card = ∑ j ∈ Finset.range q, μ.colLen j := by
  rw [sum_colLen_eq_sum_min μ le_rfl q, ← sum_rowLen_eq_card μ le_rfl]
  apply Finset.sum_congr rfl
  intro i _
  have := μ.rowLen_anti 0 i (Nat.zero_le _)
  omega

/-- Remove the bottom box of each of the rightmost `t` nonempty columns. -/
def removeSuffix (lam : YoungDiagram) (t : ℕ) : YoungDiagram where
  cells := lam.cells.filter (fun c => c.2 < lam.rowLen 0 - t ∨ c.1 + 1 < lam.colLen c.2)
  isLowerSet := by
    intro x y hxy hx
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx ⊢
    obtain ⟨hx, hc⟩ := hx
    refine ⟨lam.isLowerSet hxy hx, ?_⟩
    rcases hc with hc | hc
    · left; have := hxy.2; omega
    · right
      have h1 := lam.colLen_anti y.2 x.2 hxy.2
      have h2 := hxy.1
      omega

theorem mem_removeSuffix {lam : YoungDiagram} {t i j : ℕ} :
    (i, j) ∈ removeSuffix lam t ↔ (i, j) ∈ lam ∧ (j < lam.rowLen 0 - t ∨ i + 1 < lam.colLen j) := by
  rw [← mem_cells, ← mem_cells (μ := lam)]
  simp [removeSuffix]

theorem colLen_removeSuffix (lam : YoungDiagram) (t j : ℕ) :
    (removeSuffix lam t).colLen j =
      if j < lam.rowLen 0 - t then lam.colLen j else lam.colLen j - 1 := by
  apply nat_eq_of_lt_iff
  intro i
  rw [← mem_iff_lt_colLen, mem_removeSuffix, mem_iff_lt_colLen]
  split_ifs <;> omega

theorem horizontalStrip_removeSuffix (lam : YoungDiagram) (t : ℕ) :
    HorizontalStrip (removeSuffix lam t) lam := by
  refine ⟨fun c hc => (mem_removeSuffix.1 hc).1, fun j => ?_⟩
  rw [colLen_removeSuffix]
  split_ifs <;> omega

theorem card_removeSuffix (lam : YoungDiagram) {t : ℕ} (ht : t ≤ lam.rowLen 0) :
    lam.card = (removeSuffix lam t).card + t := by
  have hr : (removeSuffix lam t).rowLen 0 ≤ lam.rowLen 0 := by
    by_contra h
    push Not at h
    have : (0, lam.rowLen 0) ∈ removeSuffix lam t := by rw [mem_iff_lt_rowLen]; exact h
    have := (mem_removeSuffix.1 this).1
    rw [mem_iff_lt_rowLen] at this
    omega
  rw [card_eq_sum_colLen lam le_rfl, card_eq_sum_colLen (removeSuffix lam t) hr,
    ← Finset.sum_range_add_sum_Ico _ (show lam.rowLen 0 - t ≤ lam.rowLen 0 by omega),
    ← Finset.sum_range_add_sum_Ico _ (show lam.rowLen 0 - t ≤ lam.rowLen 0 by omega)]
  have e1 : ∑ j ∈ Finset.range (lam.rowLen 0 - t), (removeSuffix lam t).colLen j =
      ∑ j ∈ Finset.range (lam.rowLen 0 - t), lam.colLen j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj := Finset.mem_range.1 hj
    rw [colLen_removeSuffix]
    split_ifs; omega
  have e2 : ∑ j ∈ Finset.Ico (lam.rowLen 0 - t) (lam.rowLen 0), lam.colLen j =
      ∑ j ∈ Finset.Ico (lam.rowLen 0 - t) (lam.rowLen 0), ((removeSuffix lam t).colLen j + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj := Finset.mem_Ico.1 hj
    have : (0, j) ∈ lam := by rw [mem_iff_lt_rowLen]; exact hj.2
    rw [mem_iff_lt_colLen] at this
    rw [colLen_removeSuffix]
    split_ifs <;> omega
  rw [e1, e2, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one]
  omega

/-! ### Chains of horizontal strips -/

/-- `StripChain q ν λ` : `ν ⊆ λ` reached by `q` (possibly empty) horizontal strips. -/
inductive StripChain : ℕ → YoungDiagram → YoungDiagram → Prop
  | zero (ν : YoungDiagram) : StripChain 0 ν ν
  | succ {q : ℕ} {ν μ lam : YoungDiagram} :
      StripChain q ν μ → HorizontalStrip μ lam → StripChain (q + 1) ν lam

theorem HorizontalStrip.refl (ν : YoungDiagram) : HorizontalStrip ν ν :=
  ⟨le_rfl, fun _ => Nat.le_succ _⟩

theorem StripChain.refl (q : ℕ) (ν : YoungDiagram) : StripChain q ν ν := by
  induction q with
  | zero => exact .zero ν
  | succ q ih => exact .succ ih (HorizontalStrip.refl ν)

theorem rowSum_succ_dropRow (lam : YoungDiagram) (q : ℕ) :
    rowSum lam (q + 1) = lam.rowLen 0 + rowSum (dropRow lam) q := by
  unfold rowSum
  rw [Finset.sum_range_succ', add_comm]
  simp only [rowLen_dropRow]

/-- Sweeps: any `K ≤ λ₁ + ⋯ + λ_q` boxes can be removed by `q` horizontal strips. -/
theorem exists_stripChain_of_le_rowSum (q : ℕ) :
    ∀ (lam : YoungDiagram) (K : ℕ), K ≤ rowSum lam q →
      ∃ ν, StripChain q ν lam ∧ ν.card + K = lam.card := by
  induction q with
  | zero =>
    intro lam K hK
    simp [rowSum] at hK
    exact ⟨lam, .zero lam, by omega⟩
  | succ q ih =>
    intro lam K hK
    by_cases h : K ≤ lam.rowLen 0
    · refine ⟨removeSuffix lam K, .succ (StripChain.refl q _) (horizontalStrip_removeSuffix lam K), ?_⟩
      have := card_removeSuffix lam h
      omega
    · push Not at h
      rw [rowSum_succ_dropRow] at hK
      obtain ⟨ν, hc, hcard⟩ := ih (dropRow lam) (K - lam.rowLen 0) (by omega)
      refine ⟨ν, .succ hc (horizontalStrip_dropRow lam), ?_⟩
      have := card_dropRow lam
      omega

/-! ### The mean argument -/

/-- Rows decrease, so `4 · rowSum k ≤ k · rowSum 4` for `k ≥ 4`. -/
theorem four_mul_rowSum_le (lam : YoungDiagram) {k : ℕ} (hk : 4 ≤ k) :
    4 * rowSum lam k ≤ k * rowSum lam 4 := by
  have h4 : ∀ i, 4 ≤ i → lam.rowLen i ≤ lam.rowLen 3 := fun i hi =>
    lam.rowLen_anti 3 i (by omega)
  have hR4 : 4 * lam.rowLen 3 ≤ rowSum lam 4 := by
    unfold rowSum
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    have := lam.rowLen_anti 0 3 (by omega)
    have := lam.rowLen_anti 1 3 (by omega)
    have := lam.rowLen_anti 2 3 (by omega)
    omega
  have hsplit : rowSum lam k = rowSum lam 4 + ∑ i ∈ Finset.Ico 4 k, lam.rowLen i := by
    unfold rowSum
    rw [Finset.sum_range_add_sum_Ico _ hk]
  have htail : ∑ i ∈ Finset.Ico 4 k, lam.rowLen i ≤ (k - 4) * lam.rowLen 3 := by
    calc _ ≤ ∑ _i ∈ Finset.Ico 4 k, lam.rowLen 3 :=
          Finset.sum_le_sum fun i hi => h4 i (Finset.mem_Ico.1 hi).1
      _ = _ := by simp
  rw [hsplit]
  have : 4 * ((k - 4) * lam.rowLen 3) ≤ (k - 4) * rowSum lam 4 := by
    calc 4 * ((k - 4) * lam.rowLen 3) = (k - 4) * (4 * lam.rowLen 3) := by ring
      _ ≤ (k - 4) * rowSum lam 4 := Nat.mul_le_mul_left _ hR4
  have e : k * rowSum lam 4 = 4 * rowSum lam 4 + (k - 4) * rowSum lam 4 := by
    rw [← add_mul]; congr 1; omega
  omega

/-! ### Lemma 6.1 -/

/-- Horizontal-strip reduction (paper Lemma 6.1). -/
theorem strip_reduction {m : ℕ} (hm : 2 ≤ m) (lam : YoungDiagram)
    (hcard : lam.card = (staircase m).card) (hnd : ¬ Dominates (staircase m) lam) :
    (∃ ν, HorizontalStrip ν lam ∧ ν.card + m = lam.card) ∨
    (5 ≤ m ∧ ∃ ν, StripChain 4 ν lam ∧ ν.card + (2 * m - 1) = lam.card) := by
  by_cases h1 : m ≤ lam.rowLen 0
  · left
    exact ⟨removeSuffix lam m, horizontalStrip_removeSuffix lam m, (card_removeSuffix lam h1).symm⟩
  push Not at h1
  right
  -- failure of dominance at some index `k`
  unfold Dominates at hnd
  push Not at hnd
  obtain ⟨k, hk⟩ := hnd
  have hkm : k < m := by
    by_contra hge
    push Not at hge
    have := rowSum_staircase_of_le m hge
    have := rowSum_le_card lam k
    omega
  have hle : ∀ i, lam.rowLen i ≤ m - 1 := fun i => by
    have := lam.rowLen_anti 0 i (Nat.zero_le _); omega
  -- `k ≤ 3` is impossible
  have hk4 : 4 ≤ k := by
    by_contra hlt
    push Not at hlt
    have hs := two_mul_rowSum_staircase m hkm.le
    have hbound : rowSum lam k ≤ k * (m - 1) := by
      unfold rowSum
      calc _ ≤ ∑ _i ∈ Finset.range k, (m - 1) := Finset.sum_le_sum fun i _ => hle i
        _ = _ := by simp
    interval_cases k <;> omega
  have hm5 : 5 ≤ m := by omega
  -- mean argument gives `rowSum lam 4 ≥ 2m + 5`
  have hR4 : 2 * m - 1 ≤ rowSum lam 4 := by
    have hs := two_mul_rowSum_staircase m hkm.le
    have hmean := four_mul_rowSum_le lam hk4
    have hkpos : 0 < k := by omega
    by_contra hcon
    push Not at hcon
    -- `k * rowSum lam 4 ≥ 4 * rowSum lam k ≥ 4 * (rowSum ρ k + 1) = 2k(2m+1-k) + 4`
    have hA : 2 * k * (2 * m + 1 - k) + 4 ≤ k * rowSum lam 4 := by
      have : 4 * (rowSum (staircase m) k + 1) ≤ 4 * rowSum lam k := by omega
      have e : 4 * (rowSum (staircase m) k + 1) = 2 * (2 * rowSum (staircase m) k) + 4 := by ring
      rw [e, hs] at this
      have : 2 * (k * (2 * m + 1 - k)) = 2 * k * (2 * m + 1 - k) := by ring
      omega
    have hB : k * rowSum lam 4 ≤ k * (2 * m - 2) := Nat.mul_le_mul_left _ (by omega)
    have hC : 2 * k * (2 * m + 1 - k) = k * (2 * (2 * m + 1 - k)) := by ring
    have hD : 2 * m - 2 < 2 * (2 * m + 1 - k) := by omega
    have := Nat.mul_lt_mul_of_pos_left hD hkpos
    omega
  obtain ⟨ν, hc, hν⟩ := exists_stripChain_of_le_rowSum 4 lam (2 * m - 1) hR4
  exact ⟨hm5, ν, hc, hν⟩

end OAI.Saxl
