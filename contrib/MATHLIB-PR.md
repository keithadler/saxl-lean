# Mathlib upstreaming of the counting inputs to the classification

**Opened 7 Oct 2026 as two PRs** (split by reviewer area):

* https://github.com/leanprover-community/mathlib4/pull/44612 — `feat(GroupTheory/Perm): conjugacy classes of Perm α are partitions of Fintype.card α` (branch `perm-conjclasses-partition`)
* https://github.com/leanprover-community/mathlib4/pull/44613 — `feat(RepresentationTheory): irreducible representations are bounded by conjugacy classes` (branch `character-count-conjclasses`)

Fork: https://github.com/keithadler/mathlib4, local clone `~/mathlib4-contrib` (master cache fetched).
Watch: plp127's #43899 refactors `FiniteDimensional` hypotheses in `Character.lean`; if it merges
first, `CharacterCount.lean` needs its hypotheses adjusted.

## Zulip post — paste into `#mathlib4`

Topic: `number of irreducibles ≤ conjugacy classes; Perm conjugacy classes ≃ partitions`

Hi all, I've opened two small PRs in finite-group representation theory. I searched master, open PRs and this stream first and didn't find either statement; the archive lists the first one as a known gap (the "character table is square" discussions from 2020–21), so apologies if I missed something.

* #44613 `Representation.card_le_card_conjClasses`: for a finite group `G` over an algebraically closed field `k` with `|G|` invertible, a family of pairwise non-isomorphic irreducible representations has at most `Nat.card (ConjClasses G)` members. The proof is just that their characters are linearly independent class functions, using the existing `char_orthonormal`. It also adds `Representation.classFunction ρ : ConjClasses G → k`. This is only the upper-bound half of "number of irreducibles = number of conjugacy classes"; the span statement is still open.

* #44612 `Equiv.Perm.conjClassesEquivPartition : ConjClasses (Perm α) ≃ (Fintype.card α).Partition`, packaging `Perm.partition`, `partition_eq_of_isConj` and `exists_with_cycleType_iff`, plus `card_conjClasses_eq_card_partition`.

Context: with these two, "every irreducible representation of `S_n` is a Specht module" follows as soon as Specht modules are shown pairwise non-isomorphic. I have that downstream in a formalisation of Saxl's conjecture (https://github.com/keithadler/saxl-lean, `Saxl/Classification.lean`) and wanted to upstream the Mathlib-independent parts first. Disclosure: both PRs and the downstream repo were written with Claude (Anthropic) assisting; I reviewed and built everything locally against master. Happy to adjust names or placement — reviews welcome.

Note: #43899 (plp127) changes the `FiniteDimensional` hypotheses in `Character.lean`; if that lands first I'll rebase #44613 onto it.

---

Original single-branch draft below (superseded).

Two new files:

* `Mathlib/RepresentationTheory/CharacterCount.lean`
* `Mathlib/GroupTheory/Perm/ConjClassesPartition.lean`

## PR title

feat(RepresentationTheory, GroupTheory/Perm): irreducibles are bounded by conjugacy classes; conjugacy classes of `Perm α` are partitions

## PR description (draft)

Two small, independent pieces of finite-group representation theory that Mathlib currently stops
just short of.

**`Mathlib/RepresentationTheory/CharacterCount.lean`.** For a finite group `G` and an algebraically
closed field `k` with `|G|` invertible, `Representation.char_orthonormal` already gives orthogonality
of irreducible characters. This file adds the consequence that is actually used in practice:

* `Representation.classFunction ρ : ConjClasses G → k`, the character as a class function;
* `Representation.linearIndependent_classFunction`: the class functions of a family of pairwise
  non-isomorphic irreducible representations are linearly independent;
* `Representation.card_le_card_conjClasses`: such a family has at most `Nat.card (ConjClasses G)`
  members.

This is the upper-bound half of "number of irreducibles = number of conjugacy classes", and it is
exactly what is needed to prove that an explicit list of `Nat.card (ConjClasses G)` pairwise
non-isomorphic irreducibles is complete — e.g. that the Specht modules exhaust the irreducible
representations of `S_n`, which is how it is used downstream (see "Motivation").

**`Mathlib/GroupTheory/Perm/ConjClassesPartition.lean`.** Mathlib has `Equiv.Perm.partition`,
`Equiv.Perm.partition_eq_of_isConj` and `Equiv.Perm.exists_with_cycleType_iff`, but never packages
them into the classical bijection. This file adds

* `Equiv.Perm.conjClassesPartition : ConjClasses (Perm α) → (Fintype.card α).Partition`,
  with `_injective`, `_surjective` (via `exists_partition_eq`);
* `Equiv.Perm.conjClassesEquivPartition : ConjClasses (Perm α) ≃ (Fintype.card α).Partition`;
* `Equiv.Perm.card_conjClasses_eq_card_partition`.

**Motivation.** These are the two counting inputs in a formalisation of the classification of
irreducible representations of `S_n` by Specht modules
(https://github.com/keithadler/saxl-lean, `Saxl/Classification.lean`), part of a formalisation of
OpenAI's *A Cyclic Polytabloid Proof of Saxl's Conjecture*. Specht modules themselves are not yet in
Mathlib; these two files are the parts that are independent of them.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

## Zulip post (draft, `#mathlib4` or `#new members`)

I've opened #NNNNN adding two small things to finite-group representation theory:

1. `Representation.card_le_card_conjClasses`: over an algebraically closed field with `|G|`
   invertible, a family of pairwise non-isomorphic irreducible representations has at most
   `Nat.card (ConjClasses G)` members (characters are linearly independent class functions, via the
   existing `char_orthonormal`).
2. `Equiv.Perm.conjClassesEquivPartition : ConjClasses (Perm α) ≃ (Fintype.card α).Partition`,
   packaging `Perm.partition`, `partition_eq_of_isConj` and `exists_with_cycleType_iff`.

Context: with these, "every irreducible representation of `S_n` is a Specht module" follows once
Specht modules exist and are shown pairwise non-isomorphic; I have that downstream in a Saxl
conjecture formalisation (github.com/keithadler/saxl-lean) and would like to upstream the
Mathlib-independent parts first. Happy to split the PR in two if preferred.
