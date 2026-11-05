# recent-conjecture-resolutions-lean

Lean 4 / Mathlib formalizations of the main results of ten short arXiv papers (July–November 2026) that settle
named open problems or conjectures, mostly by explicit counterexamples. Each statement is stated in
`DsBatch/<slug>/Statement.lean` (definitions in `Defs.lean`) and proved in `Main.lean`.

| slug | arXiv | paper | problem settled | endpoint theorems |
| --- | --- | --- | --- | --- |
| P01 | [2608.15281](https://arxiv.org/abs/2608.15281) | A Ten-Vertex Counterexample to a Conjecture on Unstable Graphs | Mizzi's conjecture on unstable graphs | `DsBatch.P01.counterexample`, `DsBatch.P01.mizzi_conjecture_false` |
| P02 | [2609.23291](https://arxiv.org/abs/2609.23291) | The Partial List Colouring Conjecture is False (Noel) | Partial List Colouring Conjecture (Albertson–Grossman–Haas 2000) | `DsBatch.P02.counterexample`, `DsBatch.P02.plcc_false` |
| P03 | [2611.05323](https://arxiv.org/abs/2611.05323) | Associahedra are 12-colourable | Fabila-Monroy et al. 2009 conjecture (chromatic number of flip graphs of convex polygons unbounded) | `DsBatch.P03.kappa_proper`, `DsBatch.P03.chromaticNumber_le_twelve` |
| P04 | [2608.22635](https://arxiv.org/abs/2608.22635) | Counterexamples to Dujella's conjecture on integral points ... Diophantine triple | Dujella's conjecture and Problem 4.8 in Dujella's open-problem list | `DsBatch.P04.counterexample` |
| P05 | [2609.17006](https://arxiv.org/abs/2609.17006) | Unipotence of a double commutator with transvections | Kourovka Notebook Problem 10.46 | `DsBatch.P05.main` |
| P06 | [2607.23462](https://arxiv.org/abs/2607.23462) | A diamond-free claw-free cubic graph with strong chromatic index 7 | Kardoš, Problem 4.1, 33rd Workshop on Cycles and Colourings | `DsBatch.P06.main` |
| P07 | [2609.08137](https://arxiv.org/abs/2609.08137) | Fibonacci numbers are not an additive uniqueness set (Spiro 1992) | Spiro's 1992 question whether the Fibonacci numbers form an additive uniqueness set for multiplicative functions | `DsBatch.P07.key31`, `DsBatch.P07.counterexample` |
| P08 | [2609.28702](https://arxiv.org/abs/2609.28702) | There are no nontrivial chordal square-complementary graphs | two open problems from Discrete Math. 327 (2014) 62–75 | `DsBatch.P08.no_comparable_closed_neighborhoods`, `DsBatch.P08.no_simplicial_vertex` |
| P09 | [2609.04257](https://arxiv.org/abs/2609.04257) | A Counterexample to Teschner's Bondage-Number Conjecture | Teschner's conjecture b(G) ≤ (3/2)Δ(G) | `DsBatch.P09.graph_structure`, `DsBatch.P09.gamma_eq_six`, `DsBatch.P09.four_edge`, `DsBatch.P09.bondage_ge_five`, `DsBatch.P09.teschner_false` |
| P10 | [2609.38417](https://arxiv.org/abs/2609.38417) | The List Total Colouring Conjecture is False | List Total Colouring Conjecture (Borodin–Kostochka–Woodall; Juvan–Mohar–Škrekovski; Hilton–Johnson) | `DsBatch.P10.graph_structure`, `DsBatch.P10.total_colouring`, `DsBatch.P10.list_assignment`, `DsBatch.P10.counterexample` |

Every endpoint theorem depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`
(no `sorry`, no `native_decide`); the CI workflow builds the library and checks this
(`scripts/CheckAxioms.lean`, `scripts/ENDPOINTS.txt`).

## What this is, and what it is not

- These are formal verifications of results proved in the cited papers; they do not claim new mathematics.
  Where the paper refutes a conjecture, the Lean statement proves the stated counterexample's properties and the
  negation of the conjecture as stated in the paper.
- For each paper the statement was fixed and audited before proving (`notes/<slug>/AUDIT.md`) and later
  checked again against the paper for faithfulness. That review was not done by a domain expert; reports of a
  mismatch between a Lean statement and the paper are welcome as issues.
- `notes/<slug>/DONE.md` describes what is proved and how the paper's notation maps to the Lean definitions.
  P10 states the counterexample's properties directly; the list total chromatic number is not defined as a Lean
  object, so the final step "hence the conjecture is false" is explained in the docstring.

## Provenance

The proofs and statements were written by DeepSeek models (`deepseek-flash`, with `deepseek-v4-pro` for a
minority of requests) running as an agent in Claude Code, one session per paper, inside a harness with frozen
statements, a forbidden-token scan, axiom checks and a budget cap. The harness and the workflow were designed
and orchestrated by LUOLINGc325. Total model cost for the ten papers was about 12.4 CNY.

The paper sources are not included; see the arXiv links.

## Build

```
lake exe cache get
lake build
lake env lean scripts/CheckAxioms.lean
```

Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (see `lake-manifest.json`).

## License

Apache-2.0 (see `LICENSE`).
