# P09 — DONE

Paper: arXiv:2609.04257, Yousof Yavari, *A Counterexample to Teschner's
Bondage-Number Conjecture*.

Status: `bash infra/eval.sh P09` reports `main_status: proved` with all five
targets `proved` and axiom sets `{propext, Classical.choice, Quot.sound}`
(`frozen_ok: true`, `build_ok: true`, `static_hits: []`; final eval at
2026-11-05T17:18:24Z).

## What is proved

All five frozen targets compile `sorry`-free against `DsBatch/P09/Main.lean`:

1. `DsBatch.P09.graph_structure : graph_structure_statement` — the paper's
   graph `G` on `V = Fin 18` (the paper's vertices `0..17` themselves, the 27
   paper edges of Eq. (3.2) in order) has `Fintype.card V = 18`, is connected
   (`G.Connected`), is cubic (`G.IsRegularOfDegree 3`, equivalently
   `maxDegree G = 3`), and is bipartite (`G.IsBipartite`, with the explicit
   colouring `bip`).
2. `DsBatch.P09.gamma_eq_six : gamma_eq_six_statement` — `γ(G) = 6`
   (`dominationNumber G = 6`): the six vertices `{0,1,2,3,14,15}` dominate
   `G` (`Nat.sInf_le`), and no five vertices dominate `G` (kernel check over
   all 8568 five-sets; see below).
3. `DsBatch.P09.four_edge : four_edge_statement` — for every finite set `F` of
   edges of `G` with `|F| ≤ 4`,
   `dominationNumber (G.deleteEdges F) = 6`. This is exactly the paper's
   Proposition "Exact four-edge certificate".
4. `DsBatch.P09.bondage_ge_five : bondage_ge_five_statement` — `5 ≤ b(G)`.
   (The optional refinement `b(G) = 5` — the paper's Proposition / upper
   bound `b(G) ≤ 5` — is *not* a target and is not formalized; only the
   required lower bound is proved, which is what refutes the conjecture.)
5. `DsBatch.P09.teschner_false : teschner_false_statement` —
   `¬ TeschnerConjecture`: a finite simple graph with at least one edge has
   `b(G) = 5 > (3/2)·Δ(G) = 9/2`, so the conjectured inequality
   `b(G) ≤ (3/2)·Δ(G)` fails.

## Proof route

* `DsBatch/P09/Defs.lean` (frozen): `V`, the paper's edge list, `G`, and the
  real Mathlib notions `Dominates`, `dominationNumber` (as `sInf` over
  dominating-set sizes), `maxDegree`, `bondageNumber` (as `sInf` over the
  sizes of edge sets whose deletion increases `γ`), `TeschnerConjecture`.
* `DsBatch/P09/Statement.lean` (frozen): the five statements plus
  non-vacuity examples (`G.Adj 0 6`, a dominating six-set, a non-dominating
  singleton, `(4.5 : ℚ) < 5`, …).
* `DsBatch/P09/CertData.lean`: an explicit indexing `eOf : Fin 27 → Sym2 V`
  of the 27 edges (proved injective and onto `G.edgeSet` in the kernel), the
  family of 55 dominating six-sets with, for every vertex outside each set,
  the complete list of indices of its edges into the set (the paper's
  "bundles"), the subset enumeration `go`, and the bitmask test `chk`.
* `DsBatch/P09/Cert4.lean`, `Cert5.lean`, `CertOk.lean`: three independent
  kernel computations (`decide`, **no** `native_decide`), kept in separate
  modules so each kernel reduction has its own memory budget:
  - `check4`: every 4-element set of the 27 edge indices is avoided by one of
    the 55 six-sets (a cover of all `C(27,4) = 17550` four-edge sets);
  - `check5`: no 5-element set of vertices dominates `G` (all `C(18,5) = 8568`);
  - `certs_ok`: each of the 55 sets has cardinality 6, dominates `G`, and its
    recorded bundles are exactly the edges from each outside vertex into the
    set.
* `DsBatch/P09/Proof.lean`: correctness of the enumeration (`go_spec`, by
  induction on the fuel), extraction of the certificate data from the two
  checks, the bitmask lemmas connecting `chk` to the bundle criterion, the
  transfer from a surviving six-set to domination of `G − F` (paper
  Lemma "bundle"), monotonicity of `γ` under edge deletion, `γ` of the
  edgeless graph (`= 18`, giving non-emptiness of the bondage set), and the
  degree/bipartition facts.
* `DsBatch/P09/Main.lean`: the five targets, assembled from the above.

## Metrics

- Lean line count: **838** total — `Defs.lean` 72, `Statement.lean` 75,
  `CertData.lean` 195, `Cert4.lean` 17, `Cert5.lean` 16, `CertOk.lean` 18,
  `Cert.lean` 8, `Proof.lean` 336, `Main.lean` 101.
- Spend: **2.6058 CNY** of the 5.0 CNY cap (`projects/P09/state/eval.json`);
  4 chunks.
- Wall time: **about 2h22m** (2026-11-05T14:56:45Z → final eval
  2026-11-05T17:18:24Z).
- Build: `lake build DsBatch` succeeds; `python3 -I infra/scan.py` finds no
  forbidden token; the frozen SHA-256 hashes are recorded in
  `projects/P09/project.json`.

## Deviations, paper gaps and errors

- **The paper's exhaustive computation is not certified.** Proposition
  "Exact four-edge certificate" (`∀ F ∈ C(E(G),4), γ(G−F) = 6`) is proved by
  a Python verifier in Appendix A whose output is quoted
  (`min_F s(F) = 1`, `|D| = 297`), not by a machine-checkable proof. The
  formalization replaces that search by an explicit certificate checked in
  the Lean kernel: 55 of the 297 minimum dominating sets, with their bundles,
  cover all 17550 four-edge sets. No human (non-computational) proof of the
  four-edge statement is given in the paper, and none is supplied here either;
  the kernel check is the proof.
- **`γ(G) = 6`.** The paper proves this by hand (bipartite counting argument
  for a five-set, Proposition "prop:gamma"). The formalization instead checks
  all 8568 five-sets in the kernel and derives the lower bound
  `γ(G) ≥ 6`; the upper bound is the explicit six-set. This is a different
  route to the same statement, not a weaker one.
- **Not formalized (not a target):** the paper's upper bound `b(G) ≤ 5`
  (Proposition "prop:upper", which decomposes `G − F₅` into a 10-vertex graph
  plus two isolated vertices and quotes `γ = 5` for it). Only `5 ≤ b(G)` is
  claimed above; combined with the paper's bound this gives `b(G) = 5`.
- The paper's structural facts (`Δ(G) = 3`, connectivity, the bipartition
  `X = {0,1,4,5,7,9,13,15,17}`, `Y` its complement, Eq. (3.1)) were checked
  against the formal graph by kernel computation; no discrepancy was found.
- No mathematical error was found in the paper's arguments. The only
  "gap" is methodological: the four-edge certificate relies on an unverified
  script.
