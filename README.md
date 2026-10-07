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

`PLAN.md` tracks what is done and the next milestones.
