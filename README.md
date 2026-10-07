# saxl-lean

A Lean 4 / Mathlib formalisation of OpenAI's preprint
*A Cyclic Polytabloid Proof of Saxl's Conjecture* (24 Sep 2026, [`openai/math`](https://github.com/openai/math)),
checked against the challenge statement that ships with that repository.

**Current result (v0.1.0, 7 Oct 2026):** Saxl's conjecture is machine-checked for the staircases
`(1)`, `(2,1)`, `(3,2,1)` and `(4,3,2,1)` — every irreducible representation of `S_1`, `S_3`, `S_6`
and `S_10` occurs in the tensor square of the staircase Specht module.

```lean
theorem saxl_le4 (m : ℕ) (hm1 : 1 ≤ m) (hm4 : m ≤ 4) (μ : YoungDiagram)
    (hμ : μ.card = (staircase m).card) :
    0 < kronecker (canonicalTableau (staircase m) rfl) (canonicalTableau (staircase m) rfl)
      (canonicalTableau μ hμ)
```

`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` — the three axioms the
challenge permits.  There is no `sorry` anywhere except the full conjecture itself.

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
| Prop 4.2 with `s = 2` | ❌ | — |
| Prop 5.3 and Lemma 2.1 transport / self-duality | ❌ | — |
| `S^η ⊂ M^θ ⇒ η ⊵ θ`; Specht modules of different shapes are non-isomorphic | ✅ | `SpechtDistinct` |
| Conjugacy classes of `S_n` embed into Young diagrams of size `n` | ✅ | `ClassDiagram` |
| **Classification: every irreducible of `S_n` contains a Specht module** | ✅ | `Classification` |
| Theorem 3.1 for all `m`; `saxl_conjecture` | ❌ | — |

The three ❌ items are all needed for case (ii) of the paper's induction, which first arises at
`m = 5`.  The classification (`exists_specht_occurs`) was the main missing input: Mathlib has
character orthogonality but no classification of irreducible `S_n`-representations; it is proved
here by counting, with no Wedderburn–Artin.  `PLAN.md` records the route for the rest.

Roughly 6,200 lines of Lean and 400 theorems.

## Two things learned along the way

* Eq. (3.5) in the paper's proof of Prop 3.2 is not needed; the formal proof of `prop32` goes
  through without it (see `exists_Θ_uvec` in `Prop32.lean`).  A simplification, not an error.
* The paper's case (ii) silently uses "every irreducible `S_K`-representation is a Specht module"
  together with the necessity direction of Young's rule.  Neither is in Mathlib yet.

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

Mathematics: the OpenAI preprint.  Formalisation: Keith Adler with Claude (Anthropic).
