import Mathlib
import Saxl.Statement
import Saxl.MaschkeBridge

/-!
# Induction from coordinate sectors (paper Lemma 4.1, in "extension" form)

Let a finite group `G` act transitively on a finite set `Ω`, and let `ρ` be a `G`-representation on
`V` with equivariant sector projections `π A : V →ₗ V` (`A ∈ Ω`): `∑ π A = id`,
`π A ∘ π B = 0` for `A ≠ B`, and `ρ g ∘ π A = π (g • A) ∘ ρ g`.  Fix `D ∈ Ω` with stabiliser `H`
and `z` with `π D z = z`.  Put `A₀ = ℂ[H] z`.  Then every `H`-intertwiner `φ : A₀ → Res_H S`
extends to a `G`-intertwiner `ℂ[G] z → S`, namely `y ↦ ∑_A g_A • φ (g_A⁻¹ • π A y)` for coset
representatives `g_A • D = A`.  (This is the universal property of `Ind_H^G A₀ ≅ ℂ[G] z`, which is
all the induction in §6 needs.)
-/

namespace OAI.Saxl

open Representation

section

variable (G : Type) [Group G] {Ω : Type} [Fintype Ω] [MulAction G Ω]

/-- The stabiliser of the base sector. -/
abbrev stab (D : Ω) : Subgroup G := MulAction.stabilizer G D

variable {G}

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (D : Ω) (z : V)

/-- `ρ` restricted to the stabiliser. -/
noncomputable def resStab : Representation ℂ (stab G D) V := ρ.comp (stab G D).subtype

theorem resStab_apply (h : stab G D) (v : V) : resStab ρ D h v = ρ (h : G) v := rfl

/-- `A₀ = ℂ[H] z`. -/
noncomputable def cycH : Subrepresentation (resStab ρ D) := cyclic (resStab ρ D) z

/-- `ℂ[G] z`. -/
noncomputable def cycG : Subrepresentation ρ := cyclic ρ z

theorem mem_cycH_iff {y : V} :
    y ∈ cycH ρ D z ↔ y ∈ Submodule.span ℂ (Set.range fun h : stab G D => resStab ρ D h z) :=
  Iff.rfl

theorem mem_cycG_iff {y : V} : y ∈ cycG ρ z ↔ y ∈ Submodule.span ℂ (Set.range fun g : G => ρ g z) :=
  Iff.rfl

theorem cycH_le_cycG : (cycH ρ D z).toSubmodule ≤ (cycG ρ z).toSubmodule := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, rfl⟩
  exact Submodule.subset_span ⟨h, rfl⟩

theorem z_mem_cycH : z ∈ cycH ρ D z :=
  Submodule.subset_span ⟨1, by simp [resStab_apply]⟩

variable [MulAction.IsPretransitive G Ω] (π : Ω → V →ₗ[ℂ] V)
  (hsum : ∑ A, π A = LinearMap.id)
  (hdisj : ∀ A B, A ≠ B → π A ∘ₗ π B = 0)
  (hequiv : ∀ (g : G) (A : Ω), ρ g ∘ₗ π A = π (g • A) ∘ₗ ρ g)
  (hz : π D z = z)

include hequiv in
theorem π_ρ (g : G) (A : Ω) (v : V) : π A (ρ g v) = ρ g (π (g⁻¹ • A) v) := by
  have := congrArg (fun f => f v) (hequiv g (g⁻¹ • A))
  simp only [LinearMap.comp_apply, smul_inv_smul] at this
  exact this.symm

include hdisj hz in
theorem π_z_of_ne {A : Ω} (hA : A ≠ D) : π A z = 0 := by
  rw [← hz, ← LinearMap.comp_apply, hdisj A D hA, LinearMap.zero_apply]

include hdisj hequiv hz in
/-- `A₀ ⊆ T_D`: the other projections kill `A₀`. -/
theorem π_eq_zero_of_mem_cycH {y : V} (hy : y ∈ cycH ρ D z) {A : Ω} (hA : A ≠ D) : π A y = 0 := by
  rw [mem_cycH_iff] at hy
  refine Submodule.span_induction (p := fun y _ => π A y = 0) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨h, rfl⟩
    dsimp only
    rw [resStab_apply, π_ρ ρ π hequiv]
    have hne : (h : G)⁻¹ • A ≠ D := by
      intro heq
      apply hA
      calc A = (h : G) • ((h : G)⁻¹ • A) := (smul_inv_smul _ _).symm
        _ = (h : G) • D := by rw [heq]
        _ = D := h.2
    rw [π_z_of_ne D z π hdisj hz hne, map_zero]
  · simp
  · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
  · intro c x _ hx; rw [map_smul, hx, smul_zero]

include hsum hdisj hequiv hz in
theorem π_D_of_mem_cycH {y : V} (hy : y ∈ cycH ρ D z) : π D y = y := by
  classical
  have := congrArg (fun f => f y) hsum
  simp only [LinearMap.sum_apply, LinearMap.id_apply] at this
  rw [Finset.sum_eq_single D] at this
  · exact this
  · intro A _ hA; exact π_eq_zero_of_mem_cycH ρ D z π hdisj hequiv hz hy hA
  · intro h; exact absurd (Finset.mem_univ _) h

include hdisj hequiv hz in
/-- `g_A⁻¹ • π_A y ∈ A₀` for `y ∈ ℂ[G] z` and `g_A • D = A`. -/
theorem inv_smul_π_mem {y : V} (hy : y ∈ cycG ρ z) {A : Ω} {gA : G} (hgA : gA • D = A) :
    ρ gA⁻¹ (π A y) ∈ cycH ρ D z := by
  rw [mem_cycG_iff] at hy
  refine Submodule.span_induction (p := fun y _ => ρ gA⁻¹ (π A y) ∈ cycH ρ D z) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨g, rfl⟩
    dsimp only
    rw [π_ρ ρ π hequiv]
    by_cases hg : g⁻¹ • A = D
    · rw [hg, hz, ← Module.End.mul_apply, ← map_mul]
      have hgD : g • D = A := by rw [← hg, smul_inv_smul]
      have hmem : gA⁻¹ * g ∈ stab G D := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, hgD, ← hgA, inv_smul_smul]
      exact Submodule.subset_span ⟨⟨_, hmem⟩, rfl⟩
    · rw [π_z_of_ne D z π hdisj hz hg, map_zero, map_zero]
      exact Submodule.zero_mem _
  · rw [map_zero, map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [map_smul, map_smul]; exact Submodule.smul_mem _ _ hx

/-! ### The extension -/

variable {W : Type} [AddCommGroup W] [Module ℂ W] (S : Representation ℂ G W)
  (φ : IntertwiningMap (cycH ρ D z).toRepresentation (S.comp (stab G D).subtype))

open Classical in
/-- `φ` extended by zero to all of `V`. -/
noncomputable def φext (v : V) : W := if h : v ∈ cycH ρ D z then φ ⟨v, h⟩ else 0

theorem φext_of_mem {v : V} (hv : v ∈ cycH ρ D z) : φext ρ D z S φ v = φ ⟨v, hv⟩ := by
  unfold φext; rw [dif_pos hv]

theorem φext_zero : φext ρ D z S φ 0 = 0 := by
  rw [φext_of_mem ρ D z S φ (Submodule.zero_mem _)]
  exact map_zero φ

theorem φext_add {v w : V} (hv : v ∈ cycH ρ D z) (hw : w ∈ cycH ρ D z) :
    φext ρ D z S φ (v + w) = φext ρ D z S φ v + φext ρ D z S φ w := by
  rw [φext_of_mem ρ D z S φ (Submodule.add_mem _ hv hw), φext_of_mem ρ D z S φ hv,
    φext_of_mem ρ D z S φ hw]
  exact map_add φ ⟨v, hv⟩ ⟨w, hw⟩

theorem φext_smul (c : ℂ) {v : V} (hv : v ∈ cycH ρ D z) :
    φext ρ D z S φ (c • v) = c • φext ρ D z S φ v := by
  rw [φext_of_mem ρ D z S φ (Submodule.smul_mem _ c hv), φext_of_mem ρ D z S φ hv]
  exact map_smul φ c ⟨v, hv⟩

/-- `H`-equivariance of `φext` on `A₀`. -/
theorem φext_ρ (h : G) (hh : h ∈ stab G D) {v : V} (hv : v ∈ cycH ρ D z) :
    φext ρ D z S φ (ρ h v) = S h (φext ρ D z S φ v) := by
  have hmem : ρ h v ∈ cycH ρ D z := (cycH ρ D z).apply_mem_toSubmodule ⟨h, hh⟩ hv
  rw [φext_of_mem ρ D z S φ hmem, φext_of_mem ρ D z S φ hv]
  exact IntertwiningMap.isIntertwining _ _ φ ⟨h, hh⟩ ⟨v, hv⟩

include hsum hdisj hequiv hz in
/-- **Lemma 4.1 (extension form)**: an `H`-intertwiner `A₀ → Res_H S` extends to a `G`-intertwiner
`ℂ[G] z → S`. -/
theorem exists_extension_of_sectors :
    ∃ Φ : IntertwiningMap (cycG ρ z).toRepresentation S,
      ∀ (y : V) (hy : y ∈ cycH ρ D z), Φ ⟨y, cycH_le_cycG ρ D z hy⟩ = φ ⟨y, hy⟩ := by
  classical
  have hrep : ∀ A : Ω, ∃ g : G, g • D = A := fun A => MulAction.exists_smul_eq G D A
  choose gA hgA using hrep
  set F : V → W := fun v => ∑ A, S (gA A) (φext ρ D z S φ (ρ (gA A)⁻¹ (π A v))) with hF
  have hmemA : ∀ (y : V), y ∈ cycG ρ z → ∀ A, ρ (gA A)⁻¹ (π A y) ∈ cycH ρ D z :=
    fun y hy A => inv_smul_π_mem ρ D z π hdisj hequiv hz hy (hgA A)
  have hFadd : ∀ y y', y ∈ cycG ρ z → y' ∈ cycG ρ z → F (y + y') = F y + F y' := by
    intro y y' hy hy'
    simp only [hF]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [map_add, map_add, φext_add ρ D z S φ (hmemA y hy A) (hmemA y' hy' A), map_add]
  have hFsmul : ∀ (c : ℂ) y, y ∈ cycG ρ z → F (c • y) = c • F y := by
    intro c y hy
    simp only [hF]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [map_smul, map_smul, φext_smul ρ D z S φ c (hmemA y hy A), map_smul]
  -- equivariance
  have hFequiv : ∀ (g : G) y, y ∈ cycG ρ z → F (ρ g y) = S g (F y) := by
    intro g y hy
    simp only [hF]
    rw [map_sum]
    -- reindex the right-hand side by `A ↦ g • A`
    rw [← Equiv.sum_comp (MulAction.toPerm g)]
    refine Finset.sum_congr rfl fun B _ => ?_
    simp only [MulAction.toPerm_apply]
    rw [π_ρ ρ π hequiv, ← Module.End.mul_apply, ← map_mul, inv_smul_smul]
    -- `(gA (g • B))⁻¹ * g = h * (gA B)⁻¹` with `h ∈ H`
    have hmem : (gA (g • B))⁻¹ * g * gA B ∈ stab G D := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hgA B, inv_smul_eq_iff]
      exact (hgA (g • B)).symm
    have hfac : (gA (g • B))⁻¹ * g = ((gA (g • B))⁻¹ * g * gA B) * (gA B)⁻¹ := by group
    rw [hfac, map_mul, Module.End.mul_apply,
      φext_ρ ρ D z S φ _ hmem (hmemA y hy B), ← Module.End.mul_apply, ← map_mul,
      show gA (g • B) * ((gA (g • B))⁻¹ * g * gA B) = g * gA B by group, map_mul,
      Module.End.mul_apply]
  -- restriction to `A₀`
  have hFres : ∀ y, y ∈ cycH ρ D z → F y = φext ρ D z S φ y := by
    intro y hy
    simp only [hF]
    rw [Finset.sum_eq_single D]
    · have hD : gA D ∈ stab G D := by rw [MulAction.mem_stabilizer_iff]; exact hgA D
      rw [π_D_of_mem_cycH ρ D z π hsum hdisj hequiv hz hy,
        φext_ρ ρ D z S φ _ ((stab G D).inv_mem hD) hy, ← Module.End.mul_apply, ← map_mul]
      simp
    · intro A _ hA
      rw [π_eq_zero_of_mem_cycH ρ D z π hdisj hequiv hz hy hA, map_zero, φext_zero, map_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨{ toLinearMap := { toFun := fun y => F y,
                             map_add' := fun y y' => hFadd y y' y.2 y'.2,
                             map_smul' := fun c y => hFsmul c y y.2 },
            isIntertwining' := fun g => LinearMap.ext fun y => hFequiv g y y.2 },
    fun y hy => ?_⟩
  show F y = φ ⟨y, hy⟩
  rw [hFres y hy, φext_of_mem]

end

end OAI.Saxl
