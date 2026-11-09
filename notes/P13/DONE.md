# DONE — P13

Project: P13, arXiv 2609.05259, "Order 14 is the largest order for which every
4-total coloring of every cubic graph is equitable" (Adauto, de Figueiredo,
Sasaki, Schneider).

Status: `bash infra/eval.sh P13` reports `main_status: proved`
(`frozen_ok=true`, `build_ok=true`, `static_hits=0`).

## What is proved

All three frozen targets (in `DsBatch/P13/Main.lean`):

* `l12_structure` — the circular ladder `L_12 = C_6 □ K_2`
  (`L12 := SimpleGraph.cycleGraph 6 □ SimpleGraph.completeGraph (Fin 2)` on
  `Fin 6 × Fin 2`) has 12 vertices, 18 edges, and is cubic
  (`IsRegularOfDegree 3`).
* `l12_nonequitable_colouring` — `L_12` has a proper 4-total colouring
  (`colour12`, colours on its 12 vertices and 18 edges; adjacent vertices,
  adjacent edges and incident vertex–edge pairs get distinct colours) with
  colour class configuration `(8,8,8,6)` (the multiset `{8,8,8,6}`, total
  30 = 12 + 18), and it is non-equitable.
* `stemock_conjecture_false` — `¬ StemockConjecture`: the paper's Conjecture
  1.2 ("every 4-total coloring of a cubic graph of order less than 20 is
  equitable") is false, refuted by the above colouring of `L_12` (order
  `12 < 20`).

The explicit colouring is in closed form (`vertexColour`, `pairColour`,
`edgeColour`, `colour12` in `Defs.lean`): colour 3 is used on the six rungs
(a perfect matching), colours 0,1,2 are each used on four vertices and four
rim edges.  Properness and the configuration are checked in the Lean kernel
with `decide` (no `native_decide`).

The optional parts of the paper (equitability at orders 6, 8, 10, 14; the
order-12, order-16 and order-18 configuration theorems; the splice theorem
and all larger orders) were not in the required scope and are not formalised.

## Numbers

* Lean line count: `DsBatch/P13/Defs.lean` 176 + `Statement.lean` 109 +
  `Main.lean` 40 = 325 lines (project docs: `AUDIT.md` 78, `NOTES.md` 35).
* Spend: 0.9048 CNY of the 4 CNY cap (final `eval.sh` ledger reading).
* Wall time: about 24 minutes (session start 2026-11-05T22:32:39Z, final
  evaluation 2026-11-05T22:56Z).
* Axioms of every target: `propext`, `Classical.choice`, `Quot.sound`.

## Audit

`projects/P13/AUDIT.md` verdict `PASS` (independent opus subagent, before
freeze): definitions and the three targets faithfully formalise the required
scope, no `MUST-FIX` issues.

## Paper gaps / errors found

* No mathematical error found in the part of the paper in scope.
* The paper's figures are not present in `papers/2609.05259/` (only
  `main.tex`; `\graphicspath{{figures/}}` and Figure 2's
  `ladders_nonequitable.pdf` are missing).  Therefore `colour12` is not a
  transcription of Figure 2 but an independently constructed closed-form
  witness with the required configuration `(8,8,8,6)`; the existence claim
  is verified in Lean, so the missing figure does not affect the result.
