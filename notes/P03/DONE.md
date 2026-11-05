# P03 — DONE

Paper: arXiv 2611.05323, Jane Tan, "Associahedra are 12-colourable".

Status: `main_status: proved` (eval at 2026-11-05T13:16:40Z; `frozen_ok: true`,
`build_ok: true`, `static_hits: 0`).

## What is proved

Both frozen targets compile with axiom set `{propext, Classical.choice, Quot.sound}`
(no `sorry`, no extra axioms):

1. `DsBatch.P03.kappa_proper : DsBatch.P03.kappa_proper_statement` — for every `n ≥ 3`,
   the explicit colouring `κ(T) = (lab T, f T, d T) : ZMod 3 × ZMod 2 × ZMod 2` is proper
   on the associahedron `A_n` (the flip graph of triangulations of a convex `n`-gon, in
   the paper's ordered-full-binary-tree model): adjacent vertices have different colours.
   The colour set has exactly twelve elements.
2. `DsBatch.P03.chromaticNumber_le_twelve :
   DsBatch.P03.chromaticNumber_le_twelve_statement` — for every `n ≥ 3`,
   `(associahedron n).chromaticNumber ≤ 12`.

This proves the paper's Theorem 1 exactly as scoped by the queue, and refutes the
conjecture that the chromatic number of associahedra grows with `n`.

## Proof contents (DsBatch/P03/Main.lean)

* `zmod2_add_self`, `zmod2_key`, `zmod2_parity_key`: elementary `ZMod 2`/`ZMod 3` facts.
* `lab_fill_eq`, `lab_fill_eq_iff`: root labels of context fills are determined by the
  label at the hole (the paper's label propagation along the root path).
* `f_fill_add`: `f` is additive over an arbitrary one-hole context when the hole labels
  agree; consequently only local edges can change `f`.
* `dAux_false`, `d_fill_exists`: over a context, the change in `d` reduces to the local
  change at a common path-depth state `(k', e')`.
* `lab_rot_sub`, `local_lab_WU`, `local_lab_root`: a label-preserving rotation forces
  `lab W = lab U` and common root label `lab V`.
* `local_f`: `f` changes by 1 unless `lab (node U V) = lab V` (paper cases `p = a`,
  `a = b`).
* `local_d`: in the remaining case `p = b`, `d` changes by 1 for every incoming state.
* `rotFwd_kappa_ne`: a forward rotation changes `κ`; `kappa_proper` handles both
  directions of rotation.
* `chromaticNumber_le_twelve`: `κ` transported along
  `Fintype.equivFinOfCardEq (by decide : card (ZMod 3 × ZMod 2 × ZMod 2) = 12)` is a
  `SimpleGraph.Coloring (Fin 12)`; `SimpleGraph.Colorable.chromaticNumber_le` concludes.

## Size

* `DsBatch/P03/Main.lean`: 289 lines
* `DsBatch/P03/Defs.lean`: 156 lines (frozen)
* `DsBatch/P03/Statement.lean`: 79 lines (frozen)
* Total Lean: 524 lines

## Spend and wall time

* Spend: 0.99 CNY (eval reported `spent_cny: 0.98503`; budget 3 CNY), 1 chunk.
* Wall time: 2026-11-05T12:57:16Z → 2026-11-05T13:16:48Z (about 20 minutes).

## Deviations, paper gaps and errors

* The paper proves the result for ordered full binary trees and states that this graph is
  the flip graph of triangulations of the `n`-gon (a standard identification, stated in
  the paper). The formalization uses the tree model, exactly as the paper's proof does.
* No mathematical errors were found. Two steps are terse in the paper and were supplied
  explicitly in Lean:
  1. label propagation from the root to the rotated configuration (the paper's one-sentence
     argument) — formalized as `lab_fill_eq` / `lab_fill_eq_iff`;
  2. the assertion that only local edges affect `f` and that all other highlighted left
     edges keep their path depth — formalized as the context additivity lemmas
     `f_fill_add` and `d_fill_exists`.
  Both assertions are correct; the formalization makes the implicit context argument
  explicit.
* Observation 1 ("exactly two of three labels agree") is used only through three-residue
  case checks (`zmod2_key`), proved by kernel `decide` over `ZMod 3`; no gap.
