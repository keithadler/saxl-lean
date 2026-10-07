import Mathlib
import Saxl.Statement
import Saxl.Polytabloid
import Saxl.Content
import Saxl.Main
import Saxl.Antisymmetrizer
import Saxl.SubmoduleTheorem
import Saxl.Branching

/-!
# The sign twist `S^λ ⊗ ε ≅ S^{λᵗ}` (paper eq. (2.3)), part A

We build a nonzero sign-twisted intertwiner `Θ : S^λ ⊗ ε → S^{λᵗ}`.  On the orbit of the row
word, `Θ(e_{rw ∘ g⁻¹}) := sign g • g • e_{tᵗ}`; this is well defined since the row group `R_t`
(= the column group of the transposed tableau) acts on `e_{tᵗ}` by signs.  Then
`Θ(e_t) = ∑_{h ∈ C_t} h • e_{tᵗ}`, whose coefficient at the column word is `|C_t| ≠ 0`.
-/

namespace OAI.Saxl

open Equiv YoungDiagram

attribute [local instance] Fintype.ofFinite

theorem perm_inv_apply {α : Type*} (g : Perm α) (x : α) : g⁻¹ (g x) = x := by
  rw [Perm.inv_def]; exact Equiv.symm_apply_apply _ _

/-- The sign twist `V ⊗ ε` of a representation of `S_n`. -/
def signTwist {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Perm (Fin n)) V) : Representation ℂ (Perm (Fin n)) V where
  toFun g := ((Perm.sign g : ℤ) : ℂ) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp only [Perm.sign_mul, Units.val_mul, Int.cast_mul, map_mul, Module.End.mul_apply,
      LinearMap.smul_apply, map_smul, smul_smul]
    rw [mul_comm]

theorem signTwist_apply {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Perm (Fin n)) V) (g : Perm (Fin n)) (v : V) :
    signTwist ρ g v = ((Perm.sign g : ℤ) : ℂ) • ρ g v := rfl

variable {n : ℕ} {μ : YoungDiagram}

/-- Cells of `μ` and of `μᵗ` correspond by swapping coordinates. -/
def cellsTranspose (μ : YoungDiagram) : μ.cells ≃ μ.transpose.cells where
  toFun c := ⟨c.val.swap, by rw [mem_cells, mem_transpose, Prod.swap_swap]; exact c.2⟩
  invFun c := ⟨c.val.swap, by have := c.2; rwa [mem_cells, mem_transpose] at this⟩
  left_inv c := by ext1; simp
  right_inv c := by ext1; simp

/-- The transposed tableau, of shape `μᵗ`. -/
def transposeTableau (t : Tableau n μ) : Tableau n μ.transpose := t.trans (cellsTranspose μ)

theorem transposeTableau_apply (t : Tableau n μ) (i : Fin n) :
    (transposeTableau t i).val = (t i).val.swap := rfl

theorem rowWord_transposeTableau (t : Tableau n μ) (i : Fin n) :
    (rowWord (transposeTableau t) i : ℕ) = (t i).val.2 := rfl

/-- The row group of `t` is the column group of `tᵗ`. -/
theorem mem_columnGroup_transposeTableau (t : Tableau n μ) (g : Perm (Fin n)) :
    g ∈ columnGroup (transposeTableau t) ↔ ∀ i, (t (g i)).val.1 = (t i).val.1 := by
  simp only [mem_columnGroup, transposeTableau_apply, Prod.snd_swap]

/-- The stabiliser of the row word is the row group. -/
theorem rowWord_comp_eq_iff (t : Tableau n μ) (g : Perm (Fin n)) :
    rowWord t ∘ g = rowWord t ↔ g ∈ columnGroup (transposeTableau t) := by
  rw [mem_columnGroup_transposeTableau]
  constructor
  · intro h i
    have := congrFun h i
    simp only [Function.comp_apply] at this
    exact congrArg Fin.val this
  · intro h
    funext i
    exact Fin.ext (h i)

variable (t : Tableau n μ)

local notation "d" => μ.colLen 0
local notation "d'" => μ.transpose.colLen 0

/-- Well-definedness of `Θ` on the orbit of the row word. -/
theorem sign_wordRep_polytabloid_eq {g g' : Perm (Fin n)}
    (h : rowWord t ∘ ⇑g⁻¹ = rowWord t ∘ ⇑g'⁻¹) :
    ((Perm.sign g : ℤ) : ℂ) • wordRep n d' g (polytabloid (transposeTableau t)) =
      ((Perm.sign g' : ℤ) : ℂ) • wordRep n d' g' (polytabloid (transposeTableau t)) := by
  have hk : g⁻¹ * g' ∈ columnGroup (transposeTableau t) := by
    rw [← rowWord_comp_eq_iff]
    funext i
    have := congrFun h (g' i)
    simp only [Function.comp_apply, perm_inv_apply] at this
    simp only [Function.comp_apply, Perm.mul_apply]
    exact this
  have hg' : g' = g * (g⁻¹ * g') := by group
  rw [hg', Perm.sign_mul, map_mul (wordRep n d'), Module.End.mul_apply, wordRep_polytabloid _ hk,
    map_smul, smul_smul, Units.val_mul, Int.cast_mul, mul_assoc, sign_sq, mul_one]

open Classical in
/-- `Θ` on basis words: `Θ₀ (rw ∘ g⁻¹) = sign g • g • e_{tᵗ}`, and `0` off the orbit. -/
noncomputable def Θ₀ (w : Fin n → Fin d) : WordSpace n d' :=
  if h : ∃ g : Perm (Fin n), w = rowWord t ∘ ⇑g⁻¹ then
    ((Perm.sign h.choose : ℤ) : ℂ) • wordRep n d' h.choose (polytabloid (transposeTableau t))
  else 0

theorem Θ₀_orbit (g : Perm (Fin n)) :
    Θ₀ t (rowWord t ∘ ⇑g⁻¹) =
      ((Perm.sign g : ℤ) : ℂ) • wordRep n d' g (polytabloid (transposeTableau t)) := by
  unfold Θ₀
  have h : ∃ g' : Perm (Fin n), rowWord t ∘ ⇑g⁻¹ = rowWord t ∘ ⇑g'⁻¹ := ⟨g, rfl⟩
  rw [dif_pos h]
  exact (sign_wordRep_polytabloid_eq t h.choose_spec).symm

theorem Θ₀_of_not {w : Fin n → Fin d} (hw : ¬ ∃ g : Perm (Fin n), w = rowWord t ∘ ⇑g⁻¹) :
    Θ₀ t w = 0 := by
  unfold Θ₀; rw [dif_neg hw]

/-- The sign-twisted intertwiner `Θ : M^λ ⊗ ε → M^{λᵗ}`. -/
noncomputable def Θ : WordSpace n d →ₗ[ℂ] WordSpace n d' where
  toFun f := ∑ w, f w • Θ₀ t w
  map_add' f g := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.smul_sum, smul_smul]

theorem Θ_single (w : Fin n → Fin d) : Θ t (Pi.single w 1) = Θ₀ t w := by
  show ∑ w', (Pi.single w (1 : ℂ) : WordSpace n d) w' • Θ₀ t w' = Θ₀ t w
  rw [Finset.sum_eq_single w]
  · simp
  · intro w' _ hw'; simp [Pi.single_eq_of_ne hw']
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Twisted equivariance on basis words. -/
theorem Θ_wordRep_single (g : Perm (Fin n)) (w : Fin n → Fin d) :
    Θ t (wordRep n d g (Pi.single w 1)) =
      ((Perm.sign g : ℤ) : ℂ) • wordRep n d' g (Θ t (Pi.single w 1)) := by
  rw [wordRep_single, Θ_single, Θ_single]
  by_cases hw : ∃ h : Perm (Fin n), w = rowWord t ∘ ⇑h⁻¹
  · obtain ⟨h, rfl⟩ := hw
    have : rowWord t ∘ ⇑h⁻¹ ∘ ⇑g⁻¹ = rowWord t ∘ ⇑(g * h)⁻¹ := by
      funext i; simp [Perm.mul_apply]
    rw [Function.comp_assoc, this, Θ₀_orbit, Θ₀_orbit, map_smul, smul_smul,
      map_mul (wordRep n d'), Module.End.mul_apply, Perm.sign_mul, Units.val_mul, Int.cast_mul]
  · have hw' : ¬ ∃ h : Perm (Fin n), w ∘ ⇑g⁻¹ = rowWord t ∘ ⇑h⁻¹ := by
      rintro ⟨h, hh⟩
      apply hw
      refine ⟨g⁻¹ * h, ?_⟩
      funext i
      have := congrFun hh (g i)
      simp only [Function.comp_apply, perm_inv_apply] at this
      simp only [Function.comp_apply, mul_inv_rev, inv_inv, Perm.mul_apply]
      exact this
    rw [Θ₀_of_not t hw, Θ₀_of_not t hw', map_zero, smul_zero]

/-- Twisted equivariance: `Θ ∘ g = sign g • (g ∘ Θ)`. -/
theorem Θ_wordRep (g : Perm (Fin n)) (f : WordSpace n d) :
    Θ t (wordRep n d g f) = ((Perm.sign g : ℤ) : ℂ) • wordRep n d' g (Θ t f) := by
  have hf := eq_sum_single f
  conv_lhs => rw [hf]
  conv_rhs => rw [hf]
  simp only [map_sum, map_smul, Finset.smul_sum, Θ_wordRep_single]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [smul_comm]

/-- `Θ(e_t) = ∑_{h ∈ C_t} h • e_{tᵗ}`. -/
theorem Θ_polytabloid :
    Θ t (polytabloid t) = ∑ h : columnGroup t,
      wordRep n d' (h : Perm (Fin n)) (polytabloid (transposeTableau t)) := by
  rw [polytabloid_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, Θ_single, Θ₀_orbit, smul_smul, sign_sq, one_smul]

/-- The coefficient of `Θ(e_t)` at the column word is `|C_t|`. -/
theorem Θ_polytabloid_apply_rowWord :
    Θ t (polytabloid t) (rowWord (transposeTableau t)) = (Fintype.card (columnGroup t) : ℂ) := by
  rw [Θ_polytabloid, Finset.sum_apply]
  simp only [wordRep_apply]
  rw [Finset.card_univ.symm, Finset.cast_card]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [StripTableau.polytabloid_coeff, Finset.sum_eq_single (1 : columnGroup (transposeTableau t))]
  · have : rowWord (transposeTableau t) ∘ ⇑(h : Perm (Fin n)) = rowWord (transposeTableau t) := by
      funext i; apply Fin.ext; exact (mem_columnGroup t).1 h.2 i
    simp [this]
  · intro k _ hk
    have hne : rowWord (transposeTableau t) ∘ ⇑(h : Perm (Fin n)) ≠
        rowWord (transposeTableau t) ∘ ⇑((k : Perm (Fin n))⁻¹ : Perm (Fin n)) := by
      intro heq
      apply hk
      -- `h k ∈ C_{tᵗ}`-stabiliser of its row word, i.e. `h k ∈ C_t`; with `k ∈ R_t` forces `k = 1`
      have h1 : rowWord (transposeTableau t) ∘ ⇑((h : Perm (Fin n)) * k) =
          rowWord (transposeTableau t) := by
        funext i
        have := congrFun heq ((k : Perm (Fin n)) i)
        simp only [Function.comp_apply, perm_inv_apply] at this
        simpa [Perm.mul_apply] using this
      rw [rowWord_comp_eq_iff, mem_columnGroup_transposeTableau] at h1
      -- `h * k` preserves rows of `tᵗ`, i.e. columns of `t`
      have hmem : (h : Perm (Fin n)) * k ∈ columnGroup t := by
        rw [mem_columnGroup]
        intro i
        have := h1 i
        simpa [transposeTableau_apply] using this
      have hk' : (k : Perm (Fin n)) ∈ columnGroup t := by
        have := (columnGroup t).mul_mem ((columnGroup t).inv_mem h.2) hmem
        simpa using this
      -- `k ∈ C_t ∩ R_t = 1`
      have hrow : rowWord t ∘ ⇑(k : Perm (Fin n)) = rowWord t := by
        rw [rowWord_comp_eq_iff]; exact k.2
      ext1
      exact eq_one_of_mem_columnGroup_of_rowWord t hk' hrow
    rw [if_neg hne, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem Θ_polytabloid_ne_zero : Θ t (polytabloid t) ≠ 0 := fun h0 => by
  have := Θ_polytabloid_apply_rowWord t
  rw [h0] at this
  simp at this
  exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 this.symm)

/-- `Θ` maps `S^λ` into `S^{λᵗ}`. -/
theorem Θ_mem_specht {x : WordSpace n d} (hx : x ∈ Specht t) :
    Θ t x ∈ Specht (transposeTableau t) := by
  refine Submodule.span_induction (p := fun x _ => Θ t x ∈ Specht (transposeTableau t))
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨g, rfl⟩
    dsimp only
    rw [Θ_wordRep, Θ_polytabloid, map_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ ?_
    rw [← Module.End.mul_apply, ← map_mul]
    exact Submodule.subset_span ⟨_, rfl⟩
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- The sign-twisted intertwiner `S^λ ⊗ ε → S^{λᵗ}`. -/
noncomputable def ΘS : Representation.IntertwiningMap (signTwist (spechtRep t))
    (spechtRep (transposeTableau t)) where
  toLinearMap := (Θ t).restrict fun x hx => Θ_mem_specht t hx
  isIntertwining' g := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show Θ t (((Perm.sign g : ℤ) : ℂ) • wordRep n d g x) = wordRep n d' g (Θ t x)
    rw [map_smul, Θ_wordRep, smul_smul, sign_sq, one_smul]

theorem ΘS_apply (x : Specht t) : (ΘS t x : WordSpace n d') = Θ t x := rfl

theorem ΘS_ne_zero : ΘS t ≠ 0 := fun h0 => by
  have := congrArg (fun k : Representation.IntertwiningMap (signTwist (spechtRep t))
    (spechtRep (transposeTableau t)) => (k ⟨polytabloid t, polytabloid_mem_specht' t⟩ : WordSpace n d'))
    h0
  exact Θ_polytabloid_ne_zero t this
where
  polytabloid_mem_specht' : ∀ (t : Tableau n μ), polytabloid t ∈ Specht t := fun t =>
    Submodule.subset_span ⟨1, by simp⟩

end OAI.Saxl
