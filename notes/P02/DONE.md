# P02 — DONE

Paper: arXiv 2609.23291, Jonathan A. Noel, "The Partial List Colouring Conjecture is False".

Status: `main_status: proved` (eval at 2026-11-05T12:55:30Z; `frozen_ok: true`,
`build_ok: true`, `static_hits: 0`).

## What is proved

Both frozen targets compile as `example : <lean_type> := <name>` with axiom set
`{propext, Classical.choice, Quot.sound}` (no `sorry`, no extra axioms):

1. `DsBatch.P02.counterexample : DsBatch.P02.counterexample_statement` — for the paper's
   explicit 14-vertex graph `G` and its explicit 2-list assignment `L`:
   * `Fintype.card V = 14`;
   * `ListChromaticNumberEq G 3` (3-choosable, and not `j`-choosable for `j = 0, 1, 2`);
   * `IsListAssignment L 2`;
   * every partial proper `L`-colouring colours at most 9 vertices
     (`∀ S c, IsPartialListColoring G L S c → S.card ≤ 9`).
2. `DsBatch.P02.plcc_false : DsBatch.P02.plcc_false_statement` — the Albertson–Grossman–Haas
   Partial List Colouring Conjecture is false: `¬ PartialListColouringConjecture`.

The refutation instantiates the conjecture with `n = 14`, `k = 3`, `ℓ = 2`: the conjecture
would give `S.card ≥ 14·2/3 > 9`, contradicting the bound `S.card ≤ 9`.

## Proof contents (DsBatch/P02/Main.lean)

* Elementary `Finset` bounds on removing one or two colours from a 3-list:
  `card_sdiff_singleton_ge`, `card_sdiff_pair_ge`, `card_sdiff_pair_ge'`.
* `mul_le_two_of_add_le_three` and `exists_pairwise_distinct`.
* Structural lemmas about `G` (triangle adjacency, terminal adjacency, the partition
  `univ = terminals ∪ allTriangles`, disjointness, `inter_allTriangles_eq`).
* `triangle_card_le_two` (at most 2 coloured vertices per triangle), `special_triangle_bound`
  (if both terminals are coloured then the triangle matching their colour pair contributes at
  most 1), and `nine_bound : S.card ≤ 9`.
* `choosable_three`: the paper's case split on `L(s₁) ∩ L(s₂) = ∅`; in the disjoint case the
  product bound `|L(v) ∩ L(s₁)| · |L(v) ∩ L(s₂)| ≤ 2` gives at most 8 pairs, so one of the
  9 colour pairs of `L(s₁) × L(s₂)` is unused, and the corresponding triangle avoids both
  terminal colours.
* `not_choosable_two` (via `L` itself and `nine_bound`), `not_choosable_one` (constant list
  `{0}`; `G` has an edge), `not_choosable_zero` (empty lists).
* `counterexample` and `plcc_false`.

## Size

* `DsBatch/P02/Main.lean`: 543 lines
* `DsBatch/P02/Defs.lean`: 186 lines (frozen)
* `DsBatch/P02/Statement.lean`: 107 lines (frozen)
* Total Lean: 836 lines

## Spend and wall time

* Spend: 1.165884 CNY (budget 3 CNY), 1 chunk.
* Wall time: 2026-11-05T12:36:28Z → 2026-11-05T12:55:33Z (about 19 minutes).

## Deviations, paper gaps and errors

* The paper's Theorem 1 is stated as an existence statement ("there exists a graph …"); it is
  proved for the paper's explicit construction. The formalization states and proves the
  theorem for that explicit graph and list assignment, which is the content of the paper's
  proof (and the audit accepted this as the queue scope).
* Colours `1,2,3,4` of the paper are encoded as `0,1,2,3`; a pure relabelling.
* No mathematical gaps or errors were found in the paper. Both cases of the 3-choosability
  proof and the ≤ 9 argument (triangle pigeonhole plus terminal-pair argument) are formalized
  as stated.
