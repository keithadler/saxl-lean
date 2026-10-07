import Mathlib
import Saxl.Statement
import Saxl.Polytabloid
import Saxl.Content

/-!
# The column lemma

A word of content `λ = rowLens μ` whose letters are distinct inside every column of the tableau
`t` is `rowWord t ∘ π⁻¹` for a column permutation `π ∈ C_t` (James, Lemma 4.6's combinatorial
core).  The proof is a counting induction on the letter: letter `j` occurs `rowLen j` times, at most
once per column, hence exactly once in each of the `rowLen j` columns of length `> j`.
-/

namespace OAI.Saxl

open Equiv YoungDiagram

variable {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)

/-- `w` has distinct letters within every column of `t`. -/
def ColumnDistinct (w : Fin n → Fin (μ.colLen 0)) : Prop :=
  ∀ i j, (t i).val.2 = (t j).val.2 → w i = w j → i = j

/-- Positions lying in column `c` of `t`. -/
def colPositions (c : ℕ) : Finset (Fin n) := Finset.univ.filter fun k => (t k).val.2 = c

theorem mem_colPositions {c : ℕ} {k : Fin n} : k ∈ colPositions t c ↔ (t k).val.2 = c := by
  simp [colPositions]

theorem card_colPositions (c : ℕ) : (colPositions t c).card = μ.colLen c := by
  rw [colLen_eq_card]
  refine Finset.card_bij (fun k _ => (t k).val) ?_ ?_ ?_
  · intro k hk
    rw [mem_colPositions] at hk
    rw [mem_col_iff]
    exact ⟨(t k).2, hk⟩
  · intro a _ b _ h
    exact t.injective (Subtype.ext h)
  · intro c' hc'
    rw [mem_col_iff] at hc'
    exact ⟨t.symm ⟨c', hc'.1⟩, by rw [mem_colPositions]; simp [hc'.2], by simp⟩

variable {t}

/-- Letter `j` meets every column of length `> j`, once we know it never sits in a shorter column. -/
theorem exists_pos_of_lt_rowLen {w : Fin n → Fin (μ.colLen 0)}
    (hc : content w = content (rowWord t)) (hd : ColumnDistinct t w)
    (j : Fin (μ.colLen 0)) (hj : ∀ k, w k = j → (j : ℕ) < μ.colLen (t k).val.2)
    {c : ℕ} (hcj : c < μ.rowLen j) : ∃ k, w k = j ∧ (t k).val.2 = c := by
  set L : Finset (Fin n) := Finset.univ.filter fun k => w k = j with hL
  have hLcard : L.card = μ.rowLen j := by
    have h := congrFun hc j
    rw [content_rowWord] at h
    exact h
  have himg : L.image (fun k => (t k).val.2) ⊆ Finset.range (μ.rowLen j) := by
    intro c' hc'
    rw [Finset.mem_image] at hc'
    obtain ⟨k, hk, rfl⟩ := hc'
    rw [hL, Finset.mem_filter] at hk
    have := hj k hk.2
    rw [Finset.mem_range, ← mem_iff_lt_rowLen, mem_iff_lt_colLen]
    exact this
  have hinj : Set.InjOn (fun k => (t k).val.2) L := by
    intro a ha b hb hab
    rw [hL, Finset.coe_filter] at ha hb
    exact hd a b hab (ha.2.trans hb.2.symm)
  have heq : L.image (fun k => (t k).val.2) = Finset.range (μ.rowLen j) := by
    apply Finset.eq_of_subset_of_card_le himg
    rw [Finset.card_image_of_injOn hinj, hLcard, Finset.card_range]
  have : c ∈ L.image (fun k => (t k).val.2) := by rw [heq]; exact Finset.mem_range.2 hcj
  rw [Finset.mem_image] at this
  obtain ⟨k, hk, hkc⟩ := this
  rw [hL, Finset.mem_filter] at hk
  exact ⟨k, hk.2, hkc⟩

/-- No letter sits in a column shorter than it (counting induction on the letter). -/
theorem lt_colLen_of_columnDistinct {w : Fin n → Fin (μ.colLen 0)}
    (hc : content w = content (rowWord t)) (hd : ColumnDistinct t w) :
    ∀ (m : ℕ) (i : Fin (μ.colLen 0)) (k : Fin n), (i : ℕ) = m → w k = i →
      m < μ.colLen (t k).val.2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i k him hwk
    by_contra hcon
    push Not at hcon
    set c := (t k).val.2 with hcdef
    have hcd : μ.colLen c ≤ μ.colLen 0 := μ.colLen_anti 0 c (Nat.zero_le _)
    -- the letters `0, …, colLen c - 1` all occur in column `c`
    set T : Finset (Fin (μ.colLen 0)) :=
      (Finset.range (μ.colLen c)).attachFin (fun x hx => lt_of_lt_of_le (Finset.mem_range.1 hx) hcd)
      with hT
    set S : Finset (Fin (μ.colLen 0)) := (colPositions t c).image w with hS
    have hTS : T ⊆ S := by
      intro j hj
      rw [hT, Finset.mem_attachFin, Finset.mem_range] at hj
      have hjm : (j : ℕ) < m := lt_of_lt_of_le hj hcon
      have hcj : c < μ.rowLen j := by
        rw [← mem_iff_lt_rowLen, mem_iff_lt_colLen]; exact hj
      obtain ⟨k', hk'1, hk'2⟩ :=
        exists_pos_of_lt_rowLen hc hd j (fun k'' hk'' => ih _ hjm j k'' rfl hk'') hcj
      rw [hS, Finset.mem_image]
      exact ⟨k', (mem_colPositions t).2 hk'2, hk'1⟩
    have hiS : i ∈ S := by
      rw [hS, Finset.mem_image]
      exact ⟨k, (mem_colPositions t).2 rfl, hwk⟩
    have hiT : i ∉ T := by
      rw [hT, Finset.mem_attachFin, Finset.mem_range, him]
      exact not_lt.2 hcon
    have h1 : (insert i T).card ≤ S.card := Finset.card_le_card (Finset.insert_subset hiS hTS)
    rw [Finset.card_insert_of_notMem hiT, hT, Finset.card_attachFin, Finset.card_range] at h1
    have h2 : S.card ≤ μ.colLen c := by
      rw [hS, ← card_colPositions t c]; exact Finset.card_image_le
    omega

/-- The column lemma: such a word is `rowWord t ∘ π⁻¹` for some `π ∈ C_t`. -/
theorem exists_columnPerm {w : Fin n → Fin (μ.colLen 0)}
    (hc : content w = content (rowWord t)) (hd : ColumnDistinct t w) :
    ∃ π ∈ columnGroup t, w = rowWord t ∘ ⇑(π⁻¹ : Perm (Fin n)) := by
  have hlt : ∀ k, ((w k : ℕ), (t k).val.2) ∈ μ := fun k => by
    rw [mem_iff_lt_colLen]
    exact lt_colLen_of_columnDistinct hc hd _ (w k) k rfl rfl
  let σ : Fin n → Fin n := fun k => t.symm ⟨((w k : ℕ), (t k).val.2), hlt k⟩
  have hσt : ∀ k, (t (σ k)).val = ((w k : ℕ), (t k).val.2) := fun k => by simp [σ]
  have hinj : Function.Injective σ := by
    intro a b hab
    have h := congrArg (fun k => (t k).val) hab
    simp only [hσt] at h
    rw [Prod.mk.injEq] at h
    exact hd a b h.2 (Fin.ext h.1)
  let π : Perm (Fin n) := (Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hinj))⁻¹
  refine ⟨π, ?_, ?_⟩
  · intro k
    show (t ((Equiv.ofBijective σ _).symm k)).val.2 = (t k).val.2
    set k' := (Equiv.ofBijective σ _).symm k with hk'
    have : σ k' = k := by rw [hk']; exact Equiv.ofBijective_apply_symm_apply _ _ _
    rw [← this, hσt]
  · funext k
    show w k = rowWord t (σ k)
    apply Fin.ext
    rw [rowWord_apply, hσt]

end OAI.Saxl
