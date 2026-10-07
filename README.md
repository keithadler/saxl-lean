# saxl-lean

An independent Lean 4 / Mathlib formalisation of OpenAI's preprint
*A Cyclic Polytabloid Proof of Saxl's Conjecture* (24 Sep 2026, [`openai/math`](https://github.com/openai/math)),
checked against the challenge statement that ships with that repository.

**Read this first.** OpenAI's repository contains its *own* complete Lean proof of the paper
(`lean/OAI/RepresentationTheory/Saxl/`, 38 files, no `sorry`, pushed 6 Oct 2026). This project
started a few hours later without noticing it, and re-derived roughly the first half of the proof
independently. Since 7 Oct 2026 OpenAI's files are vendored here under `Saxl/OAI/` (Apache-2.0,
namespace renamed to `OAI.SaxlOAI`) and used to close the full statement. **The "Provenance"
section below says exactly which theorems were written for this repository and which are OpenAI's.**
Nothing in `Saxl/OAI/` was written here.

**Proved in this repository (independently of OpenAI's files):** Saxl's conjecture for the
staircases `(1)`, `(2,1)`, `(3,2,1)` and `(4,3,2,1)` — every irreducible representation of `S_1`,
`S_3`, `S_6` and `S_10` occurs in the tensor square of the staircase Specht module.

```lean
theorem saxl_le4 (m : ℕ) (hm1 : 1 ≤ m) (hm4 : m ≤ 4) (μ : YoungDiagram)
    (hμ : μ.card = (staircase m).card) :
    0 < kronecker (canonicalTableau (staircase m) rfl) (canonicalTableau (staircase m) rfl)
      (canonicalTableau μ hμ)
```

**Proved by composing with the vendored OpenAI proof:** the full statement,
`saxl_conjecture_vendored : SaxlConjecture` in `Saxl/Complete.lean` (OpenAI's `Model.lean` is
byte-identical to the challenge definitions, so their theorem is definitionally a proof of ours).

`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for all of the above.

## The statement

For `m ≥ 1` let `ρ_m = (m, m-1, …, 1)` be the staircase partition of `N_m = m(m+1)/2`.
**Saxl's conjecture** (2012) says that every irreducible complex representation `S^λ` of `S_{N_m}`
is a constituent of `S^{ρ_m} ⊗ S^{ρ_m}`, i.e. every Kronecker coefficient `g(ρ_m, ρ_m, λ)` is
positive.

The formal target is `OAI.Saxl.saxl_conjecture` in [`Saxl/Statement.lean`](Saxl/Statement.lean), a
**byte-identical copy** of `lean/ComparatorChallenges/Saxl.lean` from `openai/math`.  It is never
edited.  It builds Specht modules concretely inside a word space `WordSpace n d = (Fin n → Fin d) → ℂ`
as the cyclic span of a polytabloid, and defines `kronecker a b t` as the dimension of
`Hom_{S_n}(S^μ, S^α ⊗ S^β)`.  Everything else in this repository is built on top of that file.

## What is formalised

The proof follows the paper's structure.  Ticks are fully proved; the rest is open.

| Paper | Status | Where |
|---|---|---|
| Specht modules, James's submodule theorem, irreducibility of `S^λ` | ✅ | `Polytabloid`, `Content`, `Antisymmetrizer`, `ColumnLemma`, `SubmoduleTheorem` |
| Occurrence calculus (Maschke/Schur: quotients, surjections, extensions) | ✅ | `Main`, `MaschkeBridge` |
| Occurrence is independent of tableau, position set and alphabet | ✅ | `ShapeInvariance`, `CastN`, `LetterInj`, `Orbit` |
| Sign twist and conjugate shapes | ✅ | `SignTwist`, `SignTwistOccurs`, `TwistPair` |
| Pieri rule (occurrence form), without Littlewood–Richardson | ✅ | `Branching`, `BranchingHom`, `Pieri` |
| Lemma 4.1, the "sector" extension lemma | ✅ | `Sectors`, `WordSectors` |
| Young's rule (occurrence form), dominance chains | ✅ | `Dominance`, `Young`, `YoungOccurs` |
| Prop 3.2: `S^λ ⊂ W_m` for all `λ ⊴ ρ_m` | ✅ | `StaircasePairs`, `RowSquares`, `QMap`, `Prop32` |
| `W_m ↪ S^{ρ_m} ⊗ S^{ρ_m}`, reduction of the conjecture to Theorem 3.1 | ✅ | `Bridge` |
| Lemma 6.1, horizontal-strip reduction | ✅ | `Strips` |
| Prop 4.2 with `s = 1` (width-one band cut) | ✅ | `Band1`, `Band1Factor`, `Band1Assembly` |
| **Theorem 3.1 for `m ≤ 4`; Saxl for `N_m ≤ 10`** | ✅ | `Thm31Small` |
| Prop 4.2 for any width `s`: margin lemma, transversal, column rotation, band tableau, factorisation (eq. 4.8) | ✅ | `Band2Margin`, `Band2Transversal`, `Band2Shift`, `Band2Factor` |
| Prop 4.2 with `s = 2`: extension-by-zero along the band split, injectivity, equivariance | ✅ | `Band2Ext`, `WordSectorsP` |
| Prop 4.2 with `s = 2`: assembly (`band2_step`) | ❌ here; ✅ in vendored `Saxl/OAI/BandGlue`, `HighProjection`, `CoordinateSector` | — |
| Prop 5.3 and Lemma 2.1 transport / self-duality | ❌ here; ✅ in vendored `Saxl/OAI/Path*`, `BandMatrices`, `SpechtDuality` | — |
| `S^η ⊂ M^θ ⇒ η ⊵ θ`; Specht modules of different shapes are non-isomorphic | ✅ | `SpechtDistinct` |
| Conjugacy classes of `S_n` embed into Young diagrams of size `n` | ✅ | `ClassDiagram` |
| **Classification: every irreducible of `S_n` contains a Specht module** | ✅ | `Classification` |
| Constituent extraction: a nonzero `ρ ⊠ M^θ → τ` stays nonzero on some `ρ ⊠ S^η`, `η ⊵ θ` | ✅ | `Constituent` |
| Theorem 3.1 for all `m`; `saxl_conjecture` | ❌ here; ✅ via vendored `Saxl/OAI/Main` | `Complete` (bridge only) |

The ❌ items are the parts of case (ii) of the paper's induction (`m ≥ 5`) that this repository has
not re-derived; they are supplied by the vendored OpenAI files.  The classification
(`exists_specht_occurs`) is proved here by counting class functions; OpenAI's
`SpechtClassification.lean` proves the same statement by the same method for `S_n`.

Roughly 6,900 lines of Lean and 430 theorems.

## Provenance

| Where | Who wrote it | What |
|---|---|---|
| `Saxl/Statement.lean` | OpenAI (challenge file, verbatim) | the definitions and the `sorry`ed target |
| `Saxl/*.lean` except `OAI/`, `Complete` | this repository (Keith Adler with Claude) | everything in the ✅ rows above marked with a file name: Specht modules, James's theorem, Pieri, sectors, Young's rule, Prop 3.2, strip reduction, Prop 4.2 parts 1–3, Theorem 3.1 for `m ≤ 4`, the classification of irreducibles, constituent extraction |
| `Saxl/OAI/*.lean` | **OpenAI** (vendored from `openai/math` commit `adc7f12`, Apache-2.0, namespace renamed) | OpenAI's complete proof; used only to close the full statement |
| `Saxl/Complete.lean` | this repository | a one-line bridge: OpenAI's theorem is definitionally the challenge statement |
| `contrib/*.lean` | this repository | generalised versions submitted to Mathlib |

To check what this repository proves on its own, delete `Saxl/OAI/` and `Saxl/Complete.lean`;
everything else still builds.

## Upstreaming to Mathlib

The two counting inputs to the classification are general and were missing from Mathlib; they are
submitted as pull requests (opened 7 Oct 2026, sources in `contrib/`):

* [mathlib4#44613](https://github.com/leanprover-community/mathlib4/pull/44613) —
  `Representation.card_le_card_conjClasses`: over an algebraically closed field with `|G|`
  invertible, pairwise non-isomorphic irreducible representations number at most
  `Nat.card (ConjClasses G)` (their characters are linearly independent class functions).
* [mathlib4#44612](https://github.com/leanprover-community/mathlib4/pull/44612) —
  `Equiv.Perm.conjClassesEquivPartition : ConjClasses (Perm α) ≃ (Fintype.card α).Partition`.

Specht modules themselves are not in Mathlib; `contrib/MATHLIB-PR.md` tracks the PRs.

## Two things learned along the way

* Eq. (3.5) in the paper's proof of Prop 3.2 is not needed; the formal proof of `prop32` goes
  through without it (see `exists_Θ_uvec` in `Prop32.lean`).  A simplification, not an error.
* The paper's case (ii) silently uses "every irreducible `S_K`-representation is a Specht module"
  together with the necessity direction of Young's rule.  Neither was in Mathlib; both are now
  proved here (`Classification.lean`, `SpechtDistinct.lean`) and the general parts are in the
  Mathlib PRs above.

## Toolchain and building

* Lean `v4.34.1` and Mathlib at commit `d13f23b723b8a846827a245b89c10fc7d3f11612` — the exact pins
  used by `openai/math`.

```bash
lake exe cache get   # fetch Mathlib oleans (several GB)
lake build
```

To verify the headline result and its axioms:

```bash
printf 'import Saxl\n#print axioms OAI.Saxl.saxl_le4\n' > check.lean && lake env lean check.lean
```

## Layout

`Saxl.lean` imports every module.  `Saxl/Statement.lean` is the untouched challenge; `Saxl/Main.lean`
defines `Occurs` and reduces `SaxlConjecture` to `TensorSquareCovers`; the remaining modules are
listed in the table above.  `PLAN.md` tracks progress and the next milestones.

## Credits

Mathematics: the OpenAI preprint.  Formalisation outside `Saxl/OAI/`: Keith Adler with Claude (Anthropic).  `Saxl/OAI/`: OpenAI's formalisation, vendored under Apache-2.0.
