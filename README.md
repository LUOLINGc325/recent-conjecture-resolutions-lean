# recent-conjecture-resolutions-lean

Lean 4 / Mathlib formalizations of the main results of fourteen short arXiv papers (July–November 2026) that settle
named open problems or conjectures, mostly by explicit counterexamples, plus a port of one of them to the
`facebookresearch/atlas-lean` statement (P11). Each statement is stated in
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
| P11 | [2609.23291](https://arxiv.org/abs/2609.23291) (port of P02) | `facebookresearch/atlas-lean` statement of P02's result | Iradmusa's partial list colouring ratio conjecture (Open Problem Garden `OPG-788`) | `DsBatch.P11.conjecture_refuted` |
| P12 | [2610.34808](https://arxiv.org/abs/2610.34808) | The Family X_{qp^s} for Distinct Primes q, p and Carmichael's Totient Conjecture | Shannon–Shiue–Saito–He conjecture that X_{2p^s} = ∅ when 2p^s+1 is not prime, for odd primes p ≠ 3 | `DsBatch.P12.master_formula`, `DsBatch.P12.even_case`, `DsBatch.P12.odd_case` |
| P13 | [2609.05259](https://arxiv.org/abs/2609.05259) | Order 14 is the largest order for which every 4-total coloring of every cubic graph is equitable | Stemock's conjecture on equitable 4-total colourings of cubic graphs of order less than 20 | `DsBatch.P13.l12_structure`, `DsBatch.P13.l12_nonequitable_colouring`, `DsBatch.P13.stemock_conjecture_false` |
| P14 | [2610.03151](https://arxiv.org/abs/2610.03151) | Arithmetic properties of solubilizers | Conjecture 3 of Mousavi–Poozesh–Zamani (2022): \|N_G(x)\| divides \|Sol_G(x)\| | `DsBatch.P14.main` |
| P15 | [2610.22783](https://arxiv.org/abs/2610.22783) | Counterexamples to the local antimagic leaf conjecture | Leaf conjecture χ_la(T) ≤ ℓ(T) + 2 (counterexample T₃ only) | `DsBatch.P15.t3_caterpillar`, `DsBatch.P15.t3_weight_separation`, `DsBatch.P15.t3_chiLa`, `DsBatch.P15.leaf_conjecture_false` |

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
- P11 copies its definitions from `facebookresearch/atlas-lean` (Apache-2.0, Meta copyright header kept) and its proof
  reuses P02.
- P15 formalizes only the counterexample T₃ = Cat(8,7,25); the paper's further counterexample and infinite family are
  not formalized. `t3_weight_separation` concerns local antimagic bijective labelings only: an arbitrary bijection can
  give equal weights (`notes/P15/DONE.md` has an explicit example).
- P12, P13 and P14 cover the main result only, not every result of the paper.

## Provenance

The proofs and statements were written by DeepSeek models (`deepseek-flash`, with `deepseek-v4-pro` for a
minority of requests) running as an agent in Claude Code, one session per paper, inside a harness with frozen
statements, a forbidden-token scan, axiom checks and a budget cap. The harness and the workflow were designed
and orchestrated by LUOLINGc325. Total model cost for the fifteen entries was about 26.5 CNY.

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
