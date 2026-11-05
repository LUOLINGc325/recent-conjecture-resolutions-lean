PASS

# P03 fidelity audit — Associahedra are 12-colourable (arXiv 2611.05323)

Audited `DsBatch/P03/Defs.lean` and `DsBatch/P03/Statement.lean` against
`papers/2611.05323/main.tex`. `lake build DsBatch` succeeds (only the two
expected `sorry` warnings in `Main.lean`).

## 1. Vertex model and adjacency (Defs.lean)

The paper's proof model (the model used in §2–§3) is the ordered-full-binary-tree
model: vertices are ordered full binary trees with `n-1` leaves (equivalently
`n-2` internal vertices), adjacency by one tree rotation. `OBT` is exactly the free
ordered-full-binary-tree type (`leaf | node l r`), i.e. the set of such trees up to
the root/left-right isomorphism the paper specifies. `numLeaves` counts leaves.
The vertex set `{T : OBT // numLeaves T = n - 1}` matches the paper exactly.

Adjacency is `Rot := RotFwd ∨ RotFwd swapped`, where `RotFwd` replaces a subtree
`((U,V),W)` by `(U,(V,W))` at an arbitrary context position. This is precisely the
paper's tree rotation ("replacing a subtree ((U,V),W) by (U,(V,W)), or conversely").
`associahedron n` is a valid `SimpleGraph` (symmetry and looplessness are proved,
the latter from `node_node_ne` + `Ctx.fill_inj`, which correctly assert a rotation is
never a no-op). The paper explicitly identifies this graph with `A_n` ("It is
well-documented that the resulting graph is equivalent to other standard definitions
of the associahedra"), so the tree model is acceptable per the audit rules.

## 2. `kappa_proper_statement`

```
∀ n, 3 ≤ n → ∀ T T', (associahedron n).Adj T T' → kappa T.1 ≠ kappa T'.1
```
This is exactly the paper's §3 claim: "the colouring κ proposed in the previous
section is proper ... for any T,T' related by a tree rotation, κ(T)≠κ(T')", for every
`n ≥ 3`. Note the paper's formally-numbered Theorem 1 is the `χ ≤ 12` statement; the
properness of κ is the paper's main proof content (start of §3). The pair of targets
(properness + `χ ≤ 12`) together is exactly the paper's content, no more and no less.

## 3. `chromaticNumber_le_twelve_statement`

```
∀ n, 3 ≤ n → (associahedron n).chromaticNumber ≤ 12
```
This is exactly the paper's Theorem 1: "χ(A_n) ≤ 12 for all n ≥ 3". No extra
hypotheses, correct direction.

## 4. `lab`, `f`, `dAux`/`d`, `kappa`

- `lab`: leaf `0`, node `1 - a - b` over `ZMod 3`. Matches the paper's `ℓ` verbatim.
- `f`: recursively sums `f l + f r` plus `1` when `lab l = lab (node l r)`; a left
  edge is highlighted iff the parent and left child have equal labels. Matches
  "total number (mod 2) of highlighted left edges".
- `dAux T k e`: `k` is the parity of the parent's path depth, `e` whether the edge
  parent→root is highlighted. At a node, `k' := if e then k+1 else 0` (new-path
  topmost vertex gets depth 0; continued path increments depth), `eL := lab l = p`,
  and the added term `if eL ∧ k' = 0 then 1 else 0` counts the highlighted left edge
  whose upper endpoint (the current node) has even path depth. Recursion passes
  `k'` and the child-edge highlight flag. This correctly implements "parity of
  highlighted left edges whose upper vertex has even path depth", with path depth
  measured from the topmost vertex of the maximal highlighted path (a path that is
  continued downward only across highlighted edges, and reset otherwise, matching the
  paper's observation that each vertex has at most one highlighted child edge).
  `d T = dAux T 0 false` correctly starts at the root with no parent (depth 0, not on
  a parent path). Verified by hand on a concrete 2-edge highlighted path
  (root–left–left): the root→child edge contributes (upper depth 0) and the
  child→grandchild edge does not (upper depth 1), giving `d = 1`, as the paper
  defines.
- `kappa T = (lab T, f T, d T) : ZMod 3 × ZMod 2 × ZMod 2`. Matches
  `κ(T) = (ℓ(T), f(T), d(T))` into `Z/3 × Z/2 × Z/2` (twelve colours).

## 5. project.json targets

```
{"name": "DsBatch.P03.kappa_proper",            "lean_type": "DsBatch.P03.kappa_proper_statement"}
{"name": "DsBatch.P03.chromaticNumber_le_twelve", "lean_type": "DsBatch.P03.chromaticNumber_le_twelve_statement"}
```
Both names match the theorems in `Main.lean` and the `*_statement` defs in
`Statement.lean`. Correct format.

## 6. Non-vacuity checks

All are genuine and compile:
- `Fintype.card (ZMod 3 × ZMod 2 × ZMod 2) = 12` (twelve-colour set).
- `n = 3` vertex exists (`node leaf leaf`, 2 leaves = 3-1).
- `quadTreeA`/`quadTreeB` are the two 3-leaf trees (vertices of `A_4`), adjacent via
  a root rotation (`Ctx.hole`), with `kappa quadTreeA ≠ kappa quadTreeB` (checked:
  `(0,0,0)` vs `(0,1,0)`).
- `¬ (associahedron 4).Colorable 1` shows `A_4` is not edgeless/trivially colourable.
- `RotFwd quadTreeA quadTreeB` and `quadTreeA ≠ quadTreeB` show rotations are real and
  non-degenerate.

## 7. Weakening / vacuity / mismatch

None found. No extra hypotheses, no restated conclusion as hypothesis, no vacuous
quantification (vertices and edges are exhibited), correct direction, and the scope
(`for every n≥3` proper 12-colouring plus `χ ≤ 12` corollary) matches the queue's
required scope in `TASK.md`.
