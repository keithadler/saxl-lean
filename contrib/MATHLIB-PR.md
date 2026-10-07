# Mathlib upstreaming of the counting inputs to the classification

**Opened 7 Oct 2026 as two PRs** (split by reviewer area):

* https://github.com/leanprover-community/mathlib4/pull/44612 — `feat(GroupTheory/Perm): conjugacy classes of Perm α are partitions of Fintype.card α` (branch `perm-conjclasses-partition`)
* https://github.com/leanprover-community/mathlib4/pull/44613 — `feat(RepresentationTheory): irreducible representations are bounded by conjugacy classes` (branch `character-count-conjclasses`)

Fork: https://github.com/keithadler/mathlib4, local clone `~/mathlib4-contrib` (master cache fetched).
Watch: plp127's #43899 refactors `FiniteDimensional` hypotheses in `Character.lean`; if it merges
first, `CharacterCount.lean` needs its hypotheses adjusted.

## Zulip post — paste into `#mathlib4`

Topic: `number of irreducibles ≤ conjugacy classes; Perm conjugacy classes ≃ partitions`

Hi all, I've opened two small PRs in finite-group representation theory:
https://github.com/leanprover-community/mathlib4/pull/44613 and
https://github.com/leanprover-community/mathlib4/pull/44612. I searched master, open PRs and this stream first and didn't find either statement; the archive lists the first one as a known gap (the "character table is square" discussions from 2020–21), so apologies if I missed something.

* PR #44613 (https://github.com/leanprover-community/mathlib4/pull/44613) — `Representation.card_le_card_conjClasses`: for a finite group `G` over an algebraically closed field `k` with `|G|` invertible, a family of pairwise non-isomorphic irreducible representations has at most `Nat.card (ConjClasses G)` members. The proof is just that their characters are linearly independent class functions, using the existing `char_orthonormal`. It also adds `Representation.classFunction ρ : ConjClasses G → k`. This is only the upper-bound half of "number of irreducibles = number of conjugacy classes"; the span statement is still open.

* PR #44612 (https://github.com/leanprover-community/mathlib4/pull/44612) — `Equiv.Perm.conjClassesEquivPartition : ConjClasses (Perm α) ≃ (Fintype.card α).Partition`, packaging `Perm.partition`, `partition_eq_of_isConj` and `exists_with_cycleType_iff`, plus `card_conjClasses_eq_card_partition`.

Context: with these two, "every irreducible representation of `S_n` is a Specht module" follows as soon as Specht modules are shown pairwise non-isomorphic. I have that downstream in a formalisation of Saxl's conjecture (https://github.com/keithadler/saxl-lean, `Saxl/Classification.lean`) and wanted to upstream the Mathlib-independent parts first. Disclosure: both PRs and the downstream repo were written with Claude (Anthropic) assisting; I reviewed and built everything locally against master. Happy to adjust names or placement — reviews welcome.

Note: PR #43899 (https://github.com/leanprover-community/mathlib4/pull/43899, plp127) changes the `FiniteDimensional` hypotheses in `Character.lean`; if that lands first I'll rebase #44613 onto it.
