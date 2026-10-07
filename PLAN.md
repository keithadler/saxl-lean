# Formalising Saxl's conjecture

Target: `OAI.Saxl.SaxlConjecture` (statement in `Saxl/Statement.lean`, copied from
openai/math `lean/ComparatorChallenges/Saxl.lean`). Source paper: OpenAI, "A Cyclic Polytabloid
Proof of Saxl's Conjecture", 24 Sep 2026 (`paper.pdf`, not committed).

Paper's strategy: for the staircase `ρ_m`, let `W_m = ℂ[G_m](v_R ⊗ v_C)` inside `S^ρ ⊗ S^ρ`
(triangle position set `B_m`, `G_m = S_{B_m}`). Show `W_m` contains every irreducible `S^λ`.

## Milestones (each is one Lean file under `Saxl/`)

1. **Specht.lean** — `Specht t` irreducible; the S^λ for λ ⊢ n are all irreps; `S^λ ≅ (S^λ)*`.
   Check what Mathlib 2026 already has before building anything.
2. **Pieri.lean** — Lemma 2.2: `Ind (S^ν ⊠ 1) ≅ ⊕ S^λ` over horizontal strips (multiplicity one).
3. **Young.lean** — Lemma 2.3: `S^τ ⊆ M^θ ↔ τ ⊵ θ`, `S^θ` occurs once.
4. **Dominance.lean** — Prop 3.2: `W_m` contains `S^λ` for every `λ ⊴ ρ_m` (sign twist + quotient).
5. **Induced.lean** — Lemma 4.1 / Prop 4.2: sector separation gives the full induced quotient
   `Ind (W_{m-s} ⊠ U_{m,s})`.
6. **Band.lean** — Prop 5.3: every shape with ≤ 4 rows occurs in `U_{m,2}` (2×2 matrix argument).
7. **Strips.lean** — Lemma 6.1: horizontal-strip reduction (first row ≥ m, else 4 sweeps).
8. **Main.lean** — Theorems 3.1 and 1.1, then bridge to `SaxlConjecture` (`kronecker > 0`).

Milestones 2–3 are classical but heavy; 5–7 are the paper's novel content.

## Status

Toolchain builds. Dominance.lean DONE, no sorry, standard axioms only: dominance order, card-by-rows, column-sum = sum of min (rowLen, q), and `Dominates.transpose` (conjugation reverses dominance, paper eq. 2.1). Everything else not started; `saxl_conjecture` is still `sorry`.

## Mathlib audit (pinned commit d13f23b)

No Specht modules, Pieri rule, Young's rule or Kronecker coefficients. Available: `YoungDiagram`,
`SemistandardTableau`, `Representation` (Induced, Irreducible, Maschke, Semisimple, Character,
Intertwining, Subrepresentation). So milestones 1–3 are built from scratch, and "S^λ irreducible /
exhaust irreps of S_n" is the biggest classical gap.

## Staircase.lean + Strips.lean — DONE (paper Lemma 6.1), no sorry, standard axioms only

`Staircase.lean`: `rowLen`/`colLen` of `staircase m`, `2·rowSum ρ_m k = k(2m+1-k)`, `rowSum ≤ card`.
`Strips.lean`: `HorizontalStrip`, full sweep `dropRow`, partial sweep `removeSuffix` (both are strips,
with exact card drops), `StripChain q ν λ`, `exists_stripChain_of_le_rowSum` (K ≤ λ₁+…+λ_q boxes
removable in q strips), the mean argument `4·rowSum k ≤ k·rowSum 4`, and **`strip_reduction`**:
for m ≥ 2, λ ⊢ N_m not dominated by ρ_m, either (i) a strip of size m leaves ν ⊢ N_{m-1}, or
(ii) m ≥ 5 and four strips of total size 2m-1 leave ν ⊢ N_{m-2}.  (Strips may be empty; the
paper's "nonempty" is cosmetic.)

## Young.lean — DONE (combinatorial half of paper Lemma 2.3), no sorry, standard axioms only

`shave τ t` removes the bottom box of the `t` tallest columns (rightmost first among ties),
defined by rows: `shaveRow τ t i = (τ_i - t) + min τ_{i+1} t`.  It is a horizontal strip of size `t`
(`t ≤ τ_0`) and `rowSum (shave τ t) k + t = rowSum τ k + min τ_k t` (paper eq. 2.7).
`SizedChain θ ℓ ν λ` : `ℓ` strips from `ν` to `λ`, the `k`-th of size `θ k`.
**`sizedChain_of_dominates`** : `τ ⊵ θ`, `|τ| = |θ|` ⇒ `SizedChain θ.rowLen (rows θ) ⊥ τ`.
**`dominates_of_sizedChain`** : converse; `SizedChain.colLen_zero_le` : after `k` strips ≤ `k` rows.
Note: the existence direction never needs the "last row disappears" step — the `⊥` base case
absorbs it.  Multiplicity-one of `S^θ` in `M^θ` (the chain is unique when `τ = θ`) is NOT done.

## Main.lean — top-level reduction DONE, no sorry, standard axioms only

`Occurs t σ` := ∃ nonzero intertwiner `S^μ → σ`.  `Occurs.mono` (subrep → ambient),
`kronecker_pos_of_occurs` (bridge to the challenge's `finrank` definition), and
**`saxlConjecture_of_covers`**: `SaxlConjecture` follows from `TensorSquareCovers m` for all `m ≥ 1`,
where `TensorSquareCovers m` := every `S^μ`, `μ ⊢ N_m`, occurs in `S^ρ_m ⊗ S^ρ_m`.
Gotcha recorded: typeclass search cannot find `AddCommGroup`/`Module.Finite` on
`IntertwiningMap _ (tprod _ _)` (instance-path mismatch inside `tprod`'s `TensorProduct`); the fix
is a generic lemma with explicit `(V := …) (W := …)` and letting `exact` check defeq.

## Polytabloid.lean — started (milestone 1 groundwork), no sorry

`wordRep_single` (`g • e_w = e_{w ∘ g⁻¹}`), `polytabloid_eq_sum`, `polytabloid_apply_rowWord`
(coefficient 1 at the row word), `polytabloid_ne_zero`, `wordRep_polytabloid` (column group acts by
sign).  Uses `attribute [local instance] Fintype.ofFinite` to match the challenge's `Fintype` choice.
Note: `openai/math` contains NO symmetric-group representation theory to reuse (checked 7 Oct 2026).

## MaschkeBridge.lean — DONE, no sorry

`occurs_of_intertwiner_to` : if `S^μ` is irreducible (hypothesis `[IsIrreducible (spechtRep t)]`)
and there is a nonzero intertwiner `σ → S^μ`, then `Occurs t σ`.  Proof at the `Subrepresentation`
level: complement of the kernel (Maschke, `exists_isCompl`), Schur (`surjective_or_eq_zero`),
`IntertwiningMap.ofBijective`.  Also `polytabloid_mem_specht` and `⊥/⊤/⊓` membership helpers.
Gotcha: `Module.Projective` over `ℂ[G]` on `asModule` hits the same instance-path wall; the
subrepresentation lattice avoids it.

## Plan for Specht irreducibility (milestone 1 core) — James's submodule theorem in the word model
1. `Content.lean` — DONE: content of a word, `G`-invariance, `contentSub c` subrep, `spechtSub_le_contentSub`, `content_rowWord`.
2. `Antisymmetrizer.lean` — DONE: `kappa`, `kappa_single_rowWord`, `kappa_wordRep` (sign on the right), `kappa_single_eq_zero` (repeated letter in a column), Hermitian `form` with unitarity, `form_kappa` (self-adjoint), `eq_zero_of_form_self_eq_zero`.
3. `ColumnLemma.lean` — DONE: `ColumnDistinct`, `colPositions`, `exists_pos_of_lt_rowLen`, `lt_colLen_of_columnDistinct` (strong induction on the letter), **`exists_columnPerm`**.
4. `SubmoduleTheorem.lean` — DONE: `kappa_single_mem_span`, `kappa_mem_span_of_mem_contentSub`, **`submodule_theorem`** (James), **`spechtRep_isIrreducible`** as an instance.  Specht modules are irreducible — the Maschke bridge now applies unconditionally.

## Mathlib API available for induction (checked 7 Oct 2026)
`Rep.ind`/`Rep.coind` with adjunctions `indResAdjunction`, `resCoindAdjunction`; for a finite-index
subgroup `indCoindIso` and `resIndAdjunction` (so Ind is also right adjoint to Res).  Also
`Representation.coind φ σ` as `G`-equivariant functions.  Frobenius reciprocity need not be rebuilt.

## Shape of Theorem 3.1 in `Occurs` language
`Occurs.of_surjective` (DONE): a surjection `W ↠ I` splits, so occurrence in `I` gives occurrence
in `W` — this is how Prop 4.2's band quotient feeds the induction.

## Next milestones (in order)

**N0. Shape invariance — DONE** (`ShapeInvariance.lean`): `occurs_of_occurs : Occurs t V → Occurs t' V`
for tableaux of the same shape (`shift`, conjugate column groups, `polytabloid_eq_wordRep`,
`transport`).  Lets us pick convenient position labellings (row/column tableaux, strips at the end).

**N1. Pieri-occurrence — DONE** (`Branching.lean`, `BranchingHom.lean`, `Pieri.lean`).
`Pieri.lean`: `exists_extension` (Maschke extension of intertwiners out of a subrepresentation, any
finite group), `pairRep` (`W ⊠ 1`), `resPair`, `exists_pair_intertwiner(_of_occurs)`, Frobenius via
`Rep.indResHomEquiv` (`exists_ind_intertwiner`), and **`occurs_ind_of_occurs`**:
`Occurs ν W → Occurs λ (Rep.ind embPair (Rep.of (pairRep W))).ρ` for `λ/ν` a horizontal strip.
This is the occurrence direction of the paper's Lemma 2.2, proved without Littlewood–Richardson.
PROGRESS LOG: `Branching.lean` DONE —
`embPair`, `StripTableau`, `nuTableau`, `extend`, `Φ` (`S_a`-equivariant), `symmPolytabloid` (`S_b`-fixed, in `S^λ`),
and **`Φ_symmPolytabloid : Φ u = stripCount • e_{t_ν}`** with `stripCount_pos`.  This is sub-step (iii)'s core.
`BranchingHom.lean` DONE: **`exists_branching_intertwiner`** — a nonzero `S_a`-intertwiner
`S^ν → Res_{S_a} S^λ` with `S_b`-fixed image (sub-step (iii) complete).  Gotcha: apply
`Occurs.of_surjective` only to one-level subtypes of the word space (a doubly nested subtype makes
the `AddCommGroup`/`AddCommMonoid` diamond check time out); so `A = ℂ[S_a]u` lives in the ambient
word space and is included into `S^λ` at the end.
Original plan:  For `λ/ν` a horizontal strip with `|ν| = a`, `|λ| = a + b`:
`Occurs ν W` (as `S_a`-rep) ⇒ `Occurs λ (Ind_{S_a × S_b}^{S_{a+b}} (W ⊠ 1))`.
Sub-steps: (i) model `S_a × S_b ↪ S_{a+b}` and `Ind` via `Rep.ind`; (ii) Frobenius:
`Hom_{S_n}(Ind(S^ν ⊠ 1), S^λ) ≅ Hom_{S_a×S_b}(S^ν ⊠ 1, Res S^λ)` (`Rep.indResAdjunction`);
(iii) **branching**: a nonzero `S_a × S_b`-map `S^ν ⊠ 1 → Res S^λ` — construct it in the word model
from a `λ`-tableau whose last `b` positions fill the strip, symmetrising over `S_b`;
(iv) `occurs_of_intertwiner_to` + functoriality of `Ind` in `W`.

**N2. Lemma 4.1 — DONE** (`Sectors.lean`): **`exists_extension_of_sectors`** — for a finite group acting
transitively on `Ω` with equivariant sector projections, every `H`-intertwiner `ℂ[H]z → Res_H S`
extends to a `G`-intertwiner `ℂ[G]z → S` (the universal property of `Ind_H^G ℂ[H]z ≅ ℂ[G]z`, which is
all §6 needs; no explicit `Ind` construction).  Original statement: transitive `G`-set `Ω`, `T = ⊕_{A∈Ω} T_A`, `g T_A = T_{gA}`,
`z ∈ T_D`, `A₀ = ℂ[H] z` ⇒ `Ind_H^G A₀ ≅ ℂ[G] z`.  State with `Representation.coind` or `Rep.ind`.

**N3. Sign twist** (`SignTwist.lean`) — part A DONE: `signTwist` (`V ⊗ ε`), `transposeTableau`,
the twisted intertwiner `Θ : M^λ ⊗ ε → M^{λᵗ}` defined on the orbit of the row word by
`Θ(e_{rw∘g⁻¹}) = sign g • g • e_{tᵗ}` (well defined since `R_t = C_{tᵗ}` acts on `e_{tᵗ}` by signs),
`Θ(e_t) = Σ_{h∈C_t} h • e_{tᵗ}` with coefficient `|C_t|` at the column word, and **`ΘS ≠ 0`**:
a nonzero twisted intertwiner `S^λ ⊗ ε → S^{λᵗ}`.  No Young-symmetrizer theory needed.
Part B DONE (`SignTwistOccurs.lean`): `isIrreducible_signTwist`, `ΘS_bijective`, `untwist`/`twist`,
**`occurs_of_occurs_transpose`** and **`occurs_transpose_of_occurs`**: `Occurs tᵗ (V ⊗ ε) ↔ Occurs t V`.
N3 is closed.

**N3b. Word model foundations — DONE** (`WordRep.lean`): `WordSpaceL n L`/`wordRepL` over any letter type
(`WordSpace n d` is the case `L = Fin d`, definitionally), `letterPush` (equivariant pushforward along a
letter map), `pairLift : WordSpace ⊗ WordSpace → pair-letter space` (`e_w ⊗ e_{w'} ↦ e_{(w,w')}`,
equivariant for `tprod`).  Enables the paper's `(E ⊗ E)^{⊗B}` computations (`Q`, `P_s`) letterwise.

**Design note for Prop 3.2 (no multiplicity-one needed):** `ϕ : V_C ⊗ ε → V_R` is our `ΘS`; `ΘS(u) =
κ_{t₁}(Σ_{H_C} h e_{t₁}) ∈ ℂ e_{t₁}` by `kappa_mem_span_of_mem_contentSub`, nonzero since `ΘS` is injective and
`u ≠ 0` (coefficient `|H_R|` at the row word).  So eq. (3.5) is bypassed; Young's rule is only needed in
occurrence form (`τ ⊵ θ ⇒ Occurs τ M^θ`), obtainable from `occurs_ind_of_occurs` + `exists_extension_of_sectors`.

**N5-prep — DONE** (`WordSectors.lean`): `Subsets n b` with the transitive `S_n`-action, `lastPositions`,
`embPair` presents its stabiliser (`exists_embPair_of_smul_eq`), sector projections `sectorProj` by the
positions of a distinguished letter (disjoint, equivariant).  `Sectors.lean` no longer needs `Σ π_A = id`.
**N5 (occurrence form) — DONE** (`YoungOccurs.lean`): `young_step` and **`young_occurs`**:
`τ ⊵ θ`, `|τ| = |θ|` ⇒ for some `n = |τ|` and a word `w : Fin n → Fin (rows θ)` of content `θ`, `S^τ`
occurs in `ℂ[S_n] e_w` for every `τ`-tableau on `n` positions.  (Position count is existential to
avoid `Fin`-casts; a cast lemma is needed at the consumer.)
Original note: induct along `sizedChain_of_dominates`; per step combine
`exists_pair_intertwiner_of_occurs` (Pieri), the restriction map `A₀ ↠ W ⊠ 1` (take `W` = the cyclic
orbit-span of the previous word so surjectivity is free), and `exists_extension_of_sectors`; conclude
`Dominates τ θ → Occurs tτ (ℂ[S_n] e_{w_θ})`.

**Prop 3.2 progress:** `RowSquares.lean` (sum-of-squares uniqueness, eq. 3.9) and `StaircasePairs.lean`
(`swapTableau`, row fibers, `pair_eq_of_content_eq`: a retained pair word equals the target word) are DONE.
Also DONE: `Orbit.lean` (equal content ⇒ conjugate ⇒ same cyclic module; letter relabelling), `CastN.lean`
(transport of `Occurs` along `Fin n ≃ Fin n'`), `transpose_staircase`.
`QMap.lean` DONE: `contentProj` (equivariant), row reversal `revPerm`, `qmap`, `pairWord_eq_target_iff`,
and **`Q_pair`** (paper eq. 3.10): `Q(e_{t'} ⊗ e_{tᵀ}) = (|C|·sign ω) • e_{c₀}`, scalar nonzero.
**Prop 3.2 — DONE** (`Prop32.lean`): `prop32 : Dominates (staircase m) λ → |λ| = N_m → Occurs tλ W_m`,
with `W_m = ℂ[G](v_R ⊗ v_C)` in the pair-letter word space (`TwistPair.lean`, `LetterInj.lean`).
No multiplicity-one Young's rule used.
Formerly remaining for Prop 3.2: the twisted map `id ⊗ Θ` with `Z_m ⊆ (id⊗Θ)(W_m)`, and the
`Occurs` chain (`of_surjective` ×2, mono, `occurs_of_occurs_transpose`, `young_occurs` + cast + orbit).

**Bridge — DONE** (`Bridge.lean`): `spechtEquiv` (same shape ⇒ isomorphic), `tmulSub : S^{t'} ⊗ S^t → pair space`,
`occurs_tprod_of_occurs_Wm`, and **`tensorSquareCovers_of_Wm`**: `TensorSquareCovers m` follows once every
`S^λ` (`λ ⊢ N_m`) occurs in `W_m` for the canonical tableau — no casts.  So the whole conjecture now
reduces to Theorem 3.1 in the form `∀ λ ⊢ N_m, Occurs (canonicalTableau λ) W_m`.

## Important finding (7 Oct 2026): case (ii) of Theorem 3.1 needs the classification of irreducibles
The paper writes `A = Ind 1 ≅ ⊕ (S^η)^{a_η}` and picks an `η` with `≤ 4` rows: this uses that every
irreducible `S_K`-representation is a Specht module (classification) and Young's rule's necessity
direction.  Neither is formalised (Mathlib has Wedderburn–Artin over `ℂ` but no irreducible counting and
no `S_n` classification).  Case (i) needs nothing new.  Since case (ii) only arises for `m ≥ 5`, the
plan is: Prop 4.2 with `s = 1` ⇒ Theorem 3.1 for `m ≤ 4` ⇒ **Saxl for staircases up to size 10, fully
formal**; the classification is a separate sub-project (route: Wedderburn–Artin + `dim Z(ℂ[G]) = #conj
classes` + `#conj classes of S_n = p(n)` + Specht modules pairwise non-isomorphic via `κ_t`/dominance).

**Prop 4.2 (s = 1) — DONE** (`Band1.lean`, `Band1Factor.lean`, `Band1Assembly.lean`): `unmixedProj` (`P₁`),
the transversal lemma `low_iff_band` (eqs. 4.6–4.7), the column shift and factorisation lemma
`polytabloid_extendCol` (eq. 4.8), `Rpair_unmixedProj_wm` (`R(P₁ w_m) = c·w_{m-1}`), and **`band1_step`**:
`Occurs ν W_{m-1} → HorizontalStrip ν λ → Occurs λ W_m` (via Pieri, the sector lemma and the projection).
**Theorem 3.1 for `m ≤ 4` — DONE** (`Thm31Small.lean`, 7 Oct 2026): `Wm_eq` (`W_m` is independent of
the staircase tableau), `occurs_Wm_castN` (transport of occurrence in `W_m` along a position bijection),
`card_staircase_succ`, and `thm31_le4` by induction on `m` (`prop32` for the dominated case,
`strip_reduction` + `band1_step` otherwise; case (ii) is excluded by `m ≤ 4`).  Hence
**`tensorSquareCovers_le4`** and **`saxl_le4`**: `0 < kronecker ρ_m ρ_m μ` for every `μ ⊢ N_m`,
`1 ≤ m ≤ 4` — Saxl's conjecture for staircases of size `≤ 10`, machine-checked against the challenge's
own definitions with only the three permitted axioms.

**Classification — DONE** (7 Oct 2026, `ClassDiagram.lean`, `SpechtDistinct.lean`,
`Classification.lean`).  No Wedderburn–Artin: `dominates_of_colDistinct` (James's combinatorial
lemma) ⇒ `dominates_of_occurs_contentSub` (`S^η ⊂ M^θ ⇒ η ⊵ θ`) ⇒ `eq_of_specht_equiv` (Specht
modules of different shapes are non-isomorphic); `classDiagram_injective` (conjugacy classes of `S_n`
inject into Young diagrams of size `n` via the cycle type); then Mathlib's `char_orthonormal` makes
the characters of `ρ` and of all `S^η` linearly independent class functions, one too many unless `ρ`
is isomorphic to some `S^η`.  Result: **`exists_specht_occurs`**: every irreducible finite-dimensional
representation of `S_n` contains (is) a Specht module.

**Constituent extraction — DONE** (7 Oct 2026, `Constituent.lean`): `exists_irreducible_subrep`,
`exists_specht_occurs_of_nontrivial`, the external tensor product `boxTensor ρ A` of representations of
`S_a` and `S_b`, and `exists_specht_boxTensor_contentSub`: a nonzero `S_a × S_b`-intertwiner
`ρ ⊠ M^θ → τ` stays nonzero on `ρ ⊠ S^η` for some `η ⊵ θ` (the paper's "Equation (6.3) provides some
`η` with `a_η > 0` and `c^λ_{ν,η} > 0`"; with `θ` of `≤ 4` parts, `η` has `≤ 4` rows).

**Mathlib upstreaming** (`contrib/`): `CharacterCount.lean` (characters of pairwise non-isomorphic
irreducibles are linearly independent class functions; `card_le_card_conjClasses`) and
`ConjClassesPartition.lean` (`ConjClasses (Perm α) ≃ (Fintype.card α).Partition`), both general, both
absent from Mathlib.  Fork `keithadler/mathlib4`, clone at `~/mathlib4-contrib`.

**Prop 4.2 for general width `s` — parts 1–2 DONE** (7 Oct 2026): `Band2Margin.lean`
(`eq_staircase_of_margins`: the equality case of the row/column margin inequalities, eqs. 4.6–4.7,
proved once for any `s`), `Band2Transversal.lean` (`UnmixedS s`, `unmixedProjS s` = `P_s`,
`high_iff_mem_small`: high positions of an unmixed term are exactly the cells of `ρ_{m-s}`),
`Band2Shift.lean` (`colShiftS` column rotation, `bandShape m s` = `{(r,c) : r < s, r + c < m}` — for
`s = 2` the shape `(m, m-1)` — and `T.bandTableau : Tableau b (bandShape m s)` whose columns are the
column blocks of the band; `embPair_mem_columnGroup_iff`, `sign_embPair`, `extendS`),
`Band2Factor.lean` (`polytabloid_extendS`: `e_t (extendS v y) = sign σ • e_ν v • e_β y`, eq. 4.8).
Key simplification: the band module `U_{m,2}` is `WPair`-shaped — generated by
`pairLift (e_{β'} ⊗ e_β)` for the two band tableaux (row blocks / column blocks) of shape
`(m, m-1)`, exactly like `W_m = ⟨pairLift (e_{swap t} ⊗ e_t)⟩`.

NEXT: `Band2Assembly.lean`: `Rpair2 := (funLeft hi ⊗ funLeft lo) ∘ splitEquiv` into
`WordSpaceL a (hi²) ⊗ WordSpaceL b (lo²)`, `Rpair2 (P₂ w_m) = c • (w_{m-2} ⊗ u_{m,2})`, the sector
lemma with `H = S_a × S_b`, extension of a nonzero `S^ν ⊠ S^η → Res S^λ` along `S^ν ↪ W_{m-2}`,
`S^η ↪ U_{m,2}` (tensor of injections is injective: `Module.Flat.rTensor/lTensor_preserves_injective`),
giving `band2_step`.  Then Prop 5.3 (`S^η ⊂ U_{m,2}` for `η ⊢ 2m-1` with `≤ 4` rows) and the case
(ii) assembly: iterated Pieri gives a nonzero `S^ν ⊠ M^θ → Res S^λ` (`θ` = strip sizes),
`exists_specht_boxTensor_contentSub` picks `η`, Frobenius + `Occurs.of_surjective` finish.

**N4. Self-duality / Lemma 2.1 transport** (`Duality.lean`): `(S^λ)* ≅ S^λ`; alternating block
tensors for any ordered basis of a dual space span a copy of `S^θ`.

**N5. Young's rule, multiplicity one** (`YoungMult.lean`): `dim Hom(S^θ, M^θ) = 1`
(`Hom(M^θ, S^θ) ≅ (S^θ)^{S_θ}` via Frobenius, plus uniqueness of the chain from `Young.lean`).

**N6. Prop 3.2** (dominance base case), **Prop 4.2** (band quotient, uses N2), **Prop 5.3** (uses
N4), then **Theorem 3.1** by induction on `m` using `strip_reduction`, N1, `Occurs.of_surjective`,
and finally `saxlConjecture_of_covers`.

Remaining: milestones 1–6.  Milestone 8 is reduced to Theorem 3.1 (`TensorSquareCovers`).
