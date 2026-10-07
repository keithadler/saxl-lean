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

Remaining: milestones 1–6 and 8.  Milestone 7 is now closed.
