# DONE: P06

Project: P06 — *A diamond-free claw-free cubic graph with strong chromatic index 7*
(arXiv 2607.23462). Finished 2026-11-05.

## Result

`bash infra/eval.sh P06` reports `main_status: proved` (frozen hashes match,
`build_ok=true`, `static_hits=0`). The single target

`DsBatch.P06.main : DsBatch.P06.main_statement`

is proved with axioms exactly `{propext, Classical.choice, Quot.sound}`.

What is proved, i.e. the queue scope "the explicit graph is cubic, claw-free,
diamond-free, has a strong 7-edge-colouring and no strong 6-edge-colouring":

- `DsBatch/P06/Defs.lean` defines the paper's explicit 18-vertex graph `H`
  (Constructions 3–4: two copies of the nine-vertex gadget `Q`, each three triangles
  `A,B,C` plus the connecting edges `a₀b₀, a₁c₀, b₁c₁, b₂c₂`, joined by the single bridge
  `a₂⁽¹⁾a₂⁽²⁾`), together with `Cubic`, `ClawFree`, `DiamondFree`, `EdgeConflict`
  (adjacency in `L(G)²`) and `StrongEdgeColoring` (strong `k`-edge-colouring).
- `DsBatch/P06/Statement.lean` (frozen) states
  `Cubic H ∧ ClawFree H ∧ DiamondFree H ∧ StrongEdgeColoring H 7 ∧ ¬ StrongEdgeColoring H 6`
  and contains non-vacuity checks (18 vertices; present/absent edges; bridge; degree;
  non-claw-free and non-diamond-free examples; empty graph examples; `¬ StrongEdgeColoring H 2`).
- `DsBatch/P06/Main.lean` proves it:
  - `Cubic`, `ClawFree`, `DiamondFree` by kernel `decide`;
  - `StrongEdgeColoring H 7` from the explicit colour table of Appendix A (`col`),
    with symmetry and the strong condition checked on all vertex quadruples;
  - `¬ StrongEdgeColoring H 6` by formalising the paper's forcing argument
    (Lemma 3.2 and Proposition 3.4): `K = {x,u,v,w,y,z}` is a `K₆` in `L(Q)²`, so a
    6-colouring uses all six colours on it; then `r` is forced to the colour of `x`,
    `s` to `v`, `t` to `u`, `q` to `w`; `m,n` split the remaining colours `y,z`; and `p`
    conflicts with all of `x,s,t,q,m,n`, hence has no available colour. The needed
    conflict facts are each discharged by `decide`.

## Size

| file | lines |
|---|---|
| `DsBatch/P06/Defs.lean` | 110 |
| `DsBatch/P06/Statement.lean` | 110 |
| `DsBatch/P06/Main.lean` | 269 |
| total | 489 |

## Spend and wall time

- Spend: **0.955 CNY** of the 4 CNY cap.
- Wall time: **≈24 minutes** (start 2026-11-05T13:49:48Z, finish ≈14:14Z).
- Chunks: 1 (chunk limit 100 minutes).

## Paper gaps / errors

None found. The paper's Lemma 3.2, availability table, forcing chain and Appendix A
colouring all check out; the formalisation follows the paper's own argument rather than
the computational search. The paper's `verify.py` was not needed.

One scope note (not an error): the queue scope asks only for cubic + claw-free +
diamond-free + strong 7-colouring + no strong 6-colouring, so the frozen statement does
not include the paper's additional Theorem 1.1 claims of connectedness, 18 vertices, and
not being the triangular prism (all true of the explicit `H`, but outside the required
scope).
