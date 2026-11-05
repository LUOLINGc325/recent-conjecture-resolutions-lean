# DONE: P08

Project: P08 — *There are no nontrivial chordal square-complementary graphs*
(arXiv 2609.28702, Aboulker–Milanič–Muršič–Pizaña). Finished 2026-11-05.

## Result

`bash infra/eval.sh P08` reports `main_status: proved` (`frozen_ok=true`,
`build_ok=true`, `static_hits=0`).  Both targets are proved with axioms exactly
`{propext, Classical.choice, Quot.sound}`:

- `DsBatch.P08.no_comparable_closed_neighborhoods : no_comparable_closed_neighborhoods_statement`
- `DsBatch.P08.no_simplicial_vertex : no_simplicial_vertex_statement`

What is proved (the queue's required scope, exactly):

- `DsBatch/P08/Defs.lean` formalises the paper's notions with real Mathlib
  `SimpleGraph`: the square `G²` (`square G`: distinct vertices at distance at
  most 2, i.e. adjacent or with a common neighbour), its complement
  `sq G = (G²)ᶜ`, the closed neighbourhood `N[x] = {x} ∪ N(x)` (`closedNhd`),
  domination `N[x] ⊆ N[y]` (`DominatedBy`), the closed ball of radius two
  `B₂(x)` (`ball2`), simplicial vertex (`IsSimplicial`: `N[x]` is a clique),
  square-complementary (`IsSquareComplementary G`: `Nonempty (G² ≃g Ḡ)`) and
  nontrivial (`IsNontrivialGraph G`: `2 ≤ Fintype.card V`).
- `DsBatch/P08/Statement.lean` (frozen, SHA-256 recorded in `project.json`)
  states the two targets:
  1. `no_comparable_closed_neighborhoods_statement`: in a nontrivial squco
     graph, no two distinct vertices have comparable closed neighbourhoods
     (neither `N[x] ⊆ N[y]` nor `N[y] ⊆ N[x]`);
  2. `no_simplicial_vertex_statement`: in a nontrivial squco graph no vertex
     is simplicial.
  Non-vacuity checks are compiled in the same frozen file: the 7-cycle `C₇`
  is a nontrivial squco graph via the explicit isomorphism `x ↦ 2x (mod 7)`
  from `C₇²` to `C̄₇`; `K₂` has comparable closed neighbourhoods and simplicial
  vertices (so the conclusion is not true of all graphs); `K₁` is squco but
  not nontrivial (so nontriviality is not redundant); and `C₇` has an
  incomparable pair (`N[0] ∌ 6 ∈ N[1]`).
- `DsBatch/P08/Main.lean` proves both targets.  The paper's argument is
  followed but its unpublished input is replaced: connectivity of nontrivial
  squco graphs is proved directly (walks in `G²` project to walks in `G`,
  while the complement of a disconnected graph is connected).  Then
  `B₂(x) ⊆ B₂(y) ⟺ N_{sq G}(y) ⊆ N_{sq G}(x)`; a counting argument on ordered
  pairs (`domPairs` vs `falsePairs`) shows that every closed neighbourhood
  containment is actually an open one, because `sq G ≃ G`; and true and false
  dominating pairs are mutually exclusive (adjacent vs non-adjacent), giving
  the first target.  The second follows since the closed neighbourhood of a
  simplicial vertex is a clique, so any neighbour of it is dominated by it.

## Size

| file | lines |
|---|---|
| `DsBatch/P08/Defs.lean` | 74 |
| `DsBatch/P08/Statement.lean` | 114 |
| `DsBatch/P08/Main.lean` | 396 |
| total | 584 |

## Spend and wall time

- Spend: **≈1.31 CNY** of the 4 CNY cap (ledger at finish; the eval snapshot
  taken a few seconds earlier recorded 1.2905 CNY).
- Wall time: **≈22 minutes** (start 2026-11-05T14:32:52Z; eval at
  2026-11-05T14:54:23Z).
- Chunks: 1 (chunk limit 100 minutes).

## Paper gaps / errors

No mathematical error found.  Two proof points are compressed or depend on
unproved cited work; both were repaired in the formalisation:

1. **Connectivity is cited, not proved.**  The paper's Lemma 3.1
   (`lem:notruedompairs`) invokes Theorem 2.1, stated as a consequence of
   [BST94]: a nontrivial squco graph is connected with radius 3 and diameter
   3 or 4.  [BST94] is not in the paper, and connectivity is genuinely used
   (in particular to know that `N_{sq G}(x)` is the complement of `B₂(x)` in
   the relevant sense, and that every vertex has a neighbour).  The formal
   proof instead derives connectivity from `G² ≅ Ḡ` directly.  The radius and
   diameter claims, and the "free of pendant vertices" remark, are not needed
   and are not formalised.
2. **The counting step is one sentence.**  "If `G` contained true dominating
   pairs, then `sq G` would contain more false dominating pairs than `G` does"
   omits the details: one needs `false(G) ⊆ dom(G)`, the swap injection
   `dom(G) → false(sq G)`, iso invariance `#false(sq G) = #false(G)`, and the
   mutual exclusivity of true and false dominating pairs (a true pair is
   adjacent, a false one is non-adjacent).  All are made explicit in
   `Main.lean`.

Scope note: the optional queue items (not chordal, not distance-hereditary)
are outside the required scope and were not stated or formalised.
