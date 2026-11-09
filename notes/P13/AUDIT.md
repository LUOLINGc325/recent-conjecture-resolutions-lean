PASS

# Fidelity audit: P13 (arXiv 2609.05259)

Verdict: the frozen-to-be statements in `DsBatch/P13/{Defs,Statement}.lean` and the
targets in `projects/P13/project.json` faithfully formalise the required scope
(`L_12 = C_6 □ K_2` is a 12-vertex cubic graph with a non-equitable 4-total
colouring of configuration (8,8,8,6), hence Stemock's conjecture is false), no
more and no less. Optional parts (orders 6/8/10/14, order-12/16/18 configuration
theorems, splicing) are correctly not stated.

## Checklist

- (a) **L12 is the prism C_6 □ K_2** — PASS. `V12 := Fin 6 × Fin 2` and
  `L12 := SimpleGraph.cycleGraph 6 □ SimpleGraph.completeGraph (Fin 2)`, i.e.
  Mathlib's box product (Cartesian product), which is exactly the paper's
  `L_n = C_{n/2} □ K_2` (Section 2). The local `DecidableRel L12.Adj` instance is
  proved via `SimpleGraph.boxProd_adj`, so it is definitionally consistent with the
  real adjacency. `Fintype.card V12 = 12`, `Fintype.card L12.edgeSet = 18`,
  `Cubic L12` are all discharged by `decide` (6 rim edges per copy = 12, 6 rungs,
  18 edges total = 3·12/2; 3-regular).
- (b) **El and Conflicts encode exactly the three constraints** — PASS.
  `El G = V ⊕ G.edgeSet` is vertices plus the actual edges (`edgeSet` is the
  `Sym2` set of edges, so no non-edges are coloured). `Conflicts` has exactly
  three cases: `inl u, inl v => G.Adj u v` (adjacent vertices; `Adj` is
  irreflexive so no self/loop constraint), `inl u, inr e => u ∈ e` and the
  symmetric case (vertex–edge incidence; `Sym2.Mem x z = ∃ y, z = s(x,y)`, the
  correct endpoint relation), and `inr e, inr f => e ≠ f ∧ ∃ u, u ∈ e ∧ u ∈ f`
  (distinct edges sharing a vertex = adjacent edges; the `e ≠ f` guard prevents
  the spurious diagonal self-conflict). No accidental extra constraints (no
  diagonal Sym2 pairs, no parallel edges — `edgeSet` is a `Set`).
- (c) **ProperTotalColouring** — PASS. `∀ x y, Conflicts G x y → c x ≠ c y` with
  colours `Fin 4` (four colours), matching "adjacent or incident elements receive
  distinct colours".
- (d) **colourClassSize / ColourConfig / Equitable** — PASS.
  `colourClassSize` filters `Finset.univ` of `El G` by `c x = i`, so it counts
  exactly the vertices and real edges of colour `i`. `ColourConfig` is the
  `Multiset` of the four sizes. `Equitable := ∀ i j, size i ≤ size j + 1`; because
  both orderings are quantified, this is equivalent to `|size i − size j| ≤ 1` for
  all `i,j` (for naturals, `a ≤ b+1 ∧ b ≤ a+1 ⟺ |a−b| ≤ 1`), matching the paper's
  "differ by at most one".
- (e) **StemockConjecture** — PASS. Quantified over all finite simple graphs
  (`Fintype V`, `SimpleGraph V`) of order `< 20` (`Fintype.card V < 20`) that are
  cubic (`IsRegularOfDegree 3`, i.e. 3-regular), and over all proper 4-total
  colourings. This matches paper Conjecture 1.2. The `[DecidableRel G.Adj]`
  instance binder is technical only — a decidable instance always exists
  (`Classical.decRel`) and the degree/equitability values are instance-independent,
  so no graphs are excluded.
- (f) **Targets state exactly the required scope** — PASS. Three targets:
  `l12_structure` (12 vertices ∧ 18 edges ∧ cubic), `l12_nonequitable_colouring`
  (∃ proper 4-total colouring with `ColourConfig = {8,8,8,6}` ∧ non-equitable),
  `stemock_conjecture_false` (`¬ StemockConjecture`). Names and types match
  `project.json` entries exactly; `Main.lean` theorems carry the target names with
  the corresponding `*_statement` types. Optional parts are absent.
- (g) **Non-vacuity** — PASS. All `example`s compile (`lake build DsBatch`
  succeeds): L12 has 12 vertices / 18 edges / is cubic; adjacency spot-checks;
  `colour12` is proper, has configuration exactly `{8,8,8,6}` (sum 30 = 12+18;
  6 rungs of colour 3, and colours 0,1,2 each on 4 vertices + 4 edges) and is
  non-equitable (8 vs 6 differ by 2). Non-triviality: the constant colouring is
  not proper, and `Equitable` is satisfiable (K_2 with vertices 0,1 and edge 2).
  The Stemock hypothesis class is non-empty (`L12` cubic, order 12 < 20).
- (h) **Static compliance** — PASS. `python3 -I infra/scan.py DsBatch/P13` returns
  `[]`; `lake build DsBatch` completes successfully. No `sorry`, `admit`, `axiom`,
  `native_decide`, `unsafe`, `implemented_by`, `extern`, `debug.skipKernelTC` in
  `DsBatch/P13/*.lean` (all targets are discharged by kernel `decide`).
- (i) **Real Mathlib objects** — PASS. `SimpleGraph`, `Finset`, `Sym2`,
  `Multiset`, `SimpleGraph.IsRegularOfDegree`, `Sym2.lift` are all genuine Mathlib
  definitions, not Prop-field placeholders or opaque stubs.

## Residual notes

- The paper's figures (e.g. `figures/ladders_nonequitable.pdf`) are not present in
  `papers/2609.05259/`; the explicit witness `colour12` is a closed-form colouring
  with the required configuration, not a transcription of Figure 2.
- Notation differs from the paper: colours are `0..3` instead of `1..4`, and the
  configuration is stated as the unordered `Multiset {8,8,8,6}` rather than a
  non-increasing sequence. Both are semantically faithful.
- No MUST-FIX issues.
