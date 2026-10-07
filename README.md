# saxl-lean

A Lean 4 / Mathlib formalisation project for **Saxl's conjecture**, following the proof in
OpenAI, *A Cyclic Polytabloid Proof of Saxl's Conjecture* (24 Sep 2026, `openai/math` preprint).

## The statement

For `m ≥ 1` let `ρ_m = (m, m-1, …, 1)` be the staircase partition of `N_m = m(m+1)/2`.
**Saxl's conjecture** says that every irreducible complex representation `S^λ` of the symmetric
group `S_{N_m}` occurs in the tensor square `S^{ρ_m} ⊗ S^{ρ_m}`, i.e. every Kronecker coefficient
`g(ρ_m, ρ_m, λ)` is positive.

The formal target is `OAI.Saxl.saxl_conjecture` in [`Saxl/Statement.lean`](Saxl/Statement.lean).
That file is a **verbatim copy** of `lean/ComparatorChallenges/Saxl.lean` from `openai/math`
(their challenge statement), so it is kept byte-identical and undocumented; it defines Specht
modules concretely inside a word space (`WordSpace n d = (Fin n → Fin d) → ℂ`) as the cyclic span
of a polytabloid, and `kronecker a b t` as the dimension of the intertwiner space
`Hom_{S_n}(S^μ, S^α ⊗ S^β)`.  The challenge permits only the axioms `propext`, `Quot.sound`,
`Classical.choice`; every theorem here is checked against that with `#print axioms`.

## Toolchain

* Lean `v4.34.1` (`lean-toolchain`), the version pinned by `openai/math`.
* Mathlib at commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, the same pin as `openai/math`.

## Building

```bash
lake exe cache get   # fetch Mathlib oleans (several GB)
lake build
```

`lake build` compiles everything; the only `sorry` is the top-level `saxl_conjecture` itself.

## Layout

| File | Contents |
|---|---|
| `Saxl/Statement.lean` | the challenge statement (verbatim, do not edit) |
| `Saxl/Dominance.lean` | dominance order; conjugation reverses it |
| `Saxl/Staircase.lean` | rows, columns, size of `ρ_m` |
| `Saxl/Strips.lean` | horizontal strips, sweeps, Lemma 6.1 (strip reduction) |
| `Saxl/Young.lean` | combinatorial Young's rule: dominance ⇔ sized strip chain |
| `Saxl/Main.lean` | `Occurs`, reduction of `SaxlConjecture` to `TensorSquareCovers` |
| `Saxl/Polytabloid.lean` | basic facts about polytabloids in the word space |
| `Saxl/Content.lean` | content of words, the permutation module `M^λ` as a subrepresentation |
| `Saxl/Antisymmetrizer.lean` | `κ_t`, the Hermitian form, self-adjointness |
| `Saxl/ColumnLemma.lean` | content-`λ` column-distinct words are column permutations of the row word |
| `Saxl/SubmoduleTheorem.lean` | James's submodule theorem; **Specht modules are irreducible** |
| `Saxl/MaschkeBridge.lean` | occurrence passes across quotients onto irreducibles and along surjections |
| `Saxl/Branching.lean`, `Saxl/Pieri*.lean`, `Saxl/Sectors.lean` | Pieri occurrence via strip tableaux, Frobenius reciprocity, the sector lemma (Lemma 4.1) |
| `Saxl/ShapeInvariance.lean`, `Saxl/CastN.lean`, `Saxl/LetterInj.lean` | occurrence is independent of the tableau, the position set and the letter alphabet |
| `Saxl/SignTwist.lean`, `Saxl/Young.lean`, `Saxl/YoungOccurs.lean` | sign twist / transpose, dominance chains, Young's rule (occurrence form) |
| `Saxl/Prop32.lean` | Prop 3.2: `S^λ` occurs in `W_m` for every `λ ⊴ ρ_m` |
| `Saxl/Bridge.lean` | `W_m ↪ S^{ρ_m} ⊗ S^{ρ_m}`; occurrence in `W_m` gives `TensorSquareCovers m` |
| `Saxl/Strips.lean` | the horizontal-strip reduction (Lemma 6.1) |
| `Saxl/Band1*.lean` | Prop 4.2 with `s = 1`: the width-one band cut `band1_step` |
| `Saxl/Thm31Small.lean` | **Theorem 3.1 for `m ≤ 4`** and `saxl_le4`: Saxl's conjecture for staircases of size `≤ 10` |

## Status

Fully machine-checked, with only `propext`, `Classical.choice`, `Quot.sound`:

* `saxl_le4 : ∀ m, 1 ≤ m → m ≤ 4 → ∀ μ (hμ : μ.card = (staircase m).card), 0 < kronecker ρ_m ρ_m μ`
  — Saxl's conjecture, in the challenge's own `kronecker`, for the staircases `(1)`, `(2,1)`,
  `(3,2,1)`, `(4,3,2,1)` (all partitions of `1, 3, 6, 10`).

Case (ii) of the paper's induction (only needed for `m ≥ 5`) uses the classification of irreducible
`S_n`-representations, which is not yet formalised; see `PLAN.md` for the route.
