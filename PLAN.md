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

**N1. Pieri-occurrence** (`Branching.lean` + `Pieri.lean`).  PROGRESS: `Branching.lean` DONE —
`embPair`, `StripTableau`, `nuTableau`, `extend`, `Φ` (`S_a`-equivariant), `symmPolytabloid` (`S_b`-fixed, in `S^λ`),
and **`Φ_symmPolytabloid : Φ u = stripCount • e_{t_ν}`** with `stripCount_pos`.  This is sub-step (iii)'s core.
Original plan:  For `λ/ν` a horizontal strip with `|ν| = a`, `|λ| = a + b`:
`Occurs ν W` (as `S_a`-rep) ⇒ `Occurs λ (Ind_{S_a × S_b}^{S_{a+b}} (W ⊠ 1))`.
Sub-steps: (i) model `S_a × S_b ↪ S_{a+b}` and `Ind` via `Rep.ind`; (ii) Frobenius:
`Hom_{S_n}(Ind(S^ν ⊠ 1), S^λ) ≅ Hom_{S_a×S_b}(S^ν ⊠ 1, Res S^λ)` (`Rep.indResAdjunction`);
(iii) **branching**: a nonzero `S_a × S_b`-map `S^ν ⊠ 1 → Res S^λ` — construct it in the word model
from a `λ`-tableau whose last `b` positions fill the strip, symmetrising over `S_b`;
(iv) `occurs_of_intertwiner_to` + functoriality of `Ind` in `W`.

**N2. Lemma 4.1** (`Sectors.lean`): transitive `G`-set `Ω`, `T = ⊕_{A∈Ω} T_A`, `g T_A = T_{gA}`,
`z ∈ T_D`, `A₀ = ℂ[H] z` ⇒ `Ind_H^G A₀ ≅ ℂ[G] z`.  State with `Representation.coind` or `Rep.ind`.

**N3. Sign twist** (`SignTwist.lean`): `S^λ ⊗ ε ≅ S^{λᵗ}` in the word model (paper eq. 2.3).

**N4. Self-duality / Lemma 2.1 transport** (`Duality.lean`): `(S^λ)* ≅ S^λ`; alternating block
tensors for any ordered basis of a dual space span a copy of `S^θ`.

**N5. Young's rule, multiplicity one** (`YoungMult.lean`): `dim Hom(S^θ, M^θ) = 1`
(`Hom(M^θ, S^θ) ≅ (S^θ)^{S_θ}` via Frobenius, plus uniqueness of the chain from `Young.lean`).

**N6. Prop 3.2** (dominance base case), **Prop 4.2** (band quotient, uses N2), **Prop 5.3** (uses
N4), then **Theorem 3.1** by induction on `m` using `strip_reduction`, N1, `Occurs.of_surjective`,
and finally `saxlConjecture_of_covers`.

Remaining: milestones 1–6.  Milestone 8 is reduced to Theorem 3.1 (`TensorSquareCovers`).
