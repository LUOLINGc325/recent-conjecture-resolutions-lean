PASS

# P01 fidelity audit — arXiv 2608.15281 (ten-vertex counterexample to Mizzi's conjecture)

Audited files: `DsBatch/P01/Defs.lean`, `DsBatch/P01/Statement.lean` (frozen-to-be),
against `papers/2608.15281/main.tex`, `papers/2608.15281/verify_counterexample.py`,
`TASK.md`, `queue/QUEUE.md`, `projects/P01/project.json`, `projects/P01/NOTES.md`.

Evidence gathered: `lake build DsBatch` succeeds (9051 jobs, only benign warnings —
a `module` suggestion on Defs.lean and the two expected `sorry` stubs in Main.lean).
`bash infra/eval.sh P01` reports `main_status=forbidden` with exactly two static hits,
both in Main.lean (`:8:sorry`, `:10:sorry`); Defs.lean and Statement.lean produce no
hits. That is the expected pre-freeze state and does not fail this audit.

## 1. Vertex set and edge set — CORRECT

- `V := Fin 10`; paper vertex `i` is `Fin 10` value `i-1`, as documented.
- Paper edge list `{12, 1·10, 24, 34, 36, 45, 57, 5·10, 6·10, 79, 8·10}` maps to the
  11 pairs `(0,1),(0,9),(1,3),(2,3),(2,5),(3,4),(4,6),(4,9),(5,9),(6,8),(7,9)`.
  `edgeList` in Defs.lean is exactly these 11, in the same order as the paper's
  verifier, with the same `i-1` shift. No missing, no extra edge.
- `G := SimpleGraph.fromRel (fun u v => (u,v) ∈ edgeList)`. `fromRel` symmetrizes
  (`r u v ∨ r v u`) and is loopless (`u ≠ v`), so both orientations of each edge are
  present and no loops are introduced; `G_adj` records this exactly
  (`G.Adj u v ↔ u ≠ v ∧ ((u,v) ∈ edgeList ∨ (v,u) ∈ edgeList)`). The `DecidableRel`
  instance matches this. Symmetry/looplessness is handled correctly.

## 2. IsTwoFoldAutomorphism and the explicit permutations — CORRECT

- `IsTwoFoldAutomorphism G α β := ∀ u v, G.Adj u v ↔ G.Adj (α u) (β v)`. This is the
  paper's eq. (1) `uv ∈ E(G) ⟺ α(u)β(v) ∈ E(G)` with both directions (the `↔`), over
  all ordered pairs including `u = v` (harmless: both sides are false on loopless
  graphs). No `u ≠ v` side condition, matching the paper.
- `alpha := Equiv.swap 0 5` is the paper's `α = (1 6)` (1→0, 6→5). Correct.
- `beta := Equiv.swap 1 2` is the paper's `β = (2 3)` (2→1, 3→2). Correct.
- The non-vacuity `example : IsTwoFoldAutomorphism G alpha beta` is decided by the
  kernel (`decide`), so the concrete condition is genuinely checked on the graph.

## 3. IsUnstable / IsTriviallyUnstable / IsNontriviallyUnstable — CORRECT reading

- `IsUnstable G := ∃ α β, α ≠ β ∧ IsTwoFoldAutomorphism G α β`. The paper: a two-fold
  automorphism is nontrivial when `α ≠ β`, and "a graph with such an automorphism is
  unstable". Matches.
- `IsTriviallyUnstable G := ¬ G.Connected ∨ G.IsBipartite`, and
  `IsNontriviallyUnstable G := IsUnstable G ∧ ¬ IsTriviallyUnstable G`
  (i.e. unstable ∧ connected ∧ non-bipartite).
- The paper's Verification proves exactly connectedness and non-bipartiteness and says
  this "satisfies the paper's exclusions of the two classes called trivially
  unstable". So "trivially unstable = disconnected OR bipartite" and "nontrivially
  unstable = unstable AND NOT trivially unstable" is the natural, defensible reading.
  The precise Mizzi definition (arXiv:2603.27559v2) is not in `papers/`; this is
  flagged in NOTES.md and does not weaken or strengthen the paper's claim beyond the
  text. Judgment call: acceptable, no defect.

## 4. VertexDetermining — CORRECT

- `VertexDetermining G := Function.Injective G.neighborSet`. `G.neighborSet v` is the
  open neighbourhood, so this is "open neighbourhoods are pairwise distinct", exactly
  the abstract's "vertex-determining" and the Verification's pairwise-distinct table.
- Note: `counterexample_statement` includes `VertexDetermining G`, which is stated in
  the abstract and proved in the Verification, but is not part of Theorem 1's literal
  wording ("connected and nontrivially unstable, but no odd k …"). This adds a
  conjunct to the goal (a strengthening, not a weakening) and is a genuine property
  stated in the paper, so it is acceptable and not a fidelity defect. It is
  additionally provable by finite `decide`.

## 5. HasCycleOfLength — CORRECT

- `HasCycleOfLength G k := 3 ≤ k ∧ ∃ f : Fin k → W, Injective f ∧
  ∀ i j, (cycleGraph k).Adj i j → G.Adj (f i) (f j)`.
- This is "C_k embeds into G as a subgraph": an injective edge-preserving map from the
  Mathlib `cycleGraph k`. Mathlib's `cycleGraph n` (`Adj a b := a - b = 1 ∨ b - a = 1`
  for `n ≥ 2`) is the standard cycle with the wrap-around edge, and `cycleGraph 3 = ⊤
  = C₃`. Extra chords among the image vertices are allowed (not an induced copy),
  which matches "contains C_k as a subgraph" and the paper's simple-cycle
  enumeration. Correct.

## 6. ContainsOddDoubleCycle — CORRECT

- `ContainsOddDoubleCycle G := ∃ k, Odd k ∧ HasCycleOfLength G k ∧
  HasCycleOfLength G (2*k)`. Exactly "there is an odd k with C_k and C_2k".
- `counterexample_statement` concludes with `¬ ContainsOddDoubleCycle G`, i.e. the
  negation, as Theorem 1 requires.

## 7. MizziConjecture and its negation — CORRECT

- `MizziConjecture := ∀ (W : Type) [Fintype W], ∀ G : SimpleGraph W,
  IsNontriviallyUnstable G → ContainsOddDoubleCycle G`. This is "every nontrivially
  unstable graph contains C_k and C_2k for some odd k", quantified over finite simple
  graphs (the paper: "All graphs here are finite and simple"). The `[Fintype W]`
  instance correctly captures finiteness.
- `mizzi_conjecture_false_statement := ¬ MizziConjecture`, i.e. there is a finite
  nontrivially unstable graph failing the conclusion — the required "the conjecture as
  stated in the paper is false".

## 8. Non-vacuity `example`s — CORRECT, all compile

`lake build DsBatch` succeeds, so every example type-checks (decidable propositions,
all checked by kernel `decide`):

- `IsTwoFoldAutomorphism G alpha beta` and `alpha ≠ beta` and `IsUnstable G`: show the
  object genuinely satisfies the hypotheses (explicit nontrivial TF automorphism).
- 5-cycle witness `![0,1,3,4,9]` = paper vertices `1,2,4,5,10`. Edges:
  1-2, 2-4, 4-5, 5-10, 10-1 — all present in `edgeList`. Verified by hand; genuine
  simple 5-cycle (paper's `1,2,4,5,10,1`).
- 6-cycle witness `![0,1,3,2,5,9]` = paper vertices `1,2,4,3,6,10`. Edges:
  1-2, 2-4, 4-3, 3-6, 6-10, 10-1 — all present. Genuine simple 6-cycle (the union of
  the two length-3 theta paths `4-2-1-10` and `4-3-6-10`).
- `¬ HasCycleOfLength ⊥ 3` on the edgeless `Fin 3` graph: shows the predicate is not
  trivially true (and the two positive examples show it is not trivially false).

## 9. project.json targets — CORRECT

Two entries, one per target, with `name`/`lean_type` matching existing declarations:
`DsBatch.P01.counterexample : counterexample_statement` and
`DsBatch.P01.mizzi_conjecture_false : mizzi_conjecture_false_statement`; both
`theorem`s exist in Main.lean (as expected `sorry` stubs) and the `_statement` defs
exist in Statement.lean.

## 10. No smuggling / forbidden tokens — CLEAN

- No `Prop`-field smuggling, no `True` placeholders, no `opaque`/`axiom`/`unsafe`.
  All definitions are transparent and use real Mathlib notions (`SimpleGraph`,
  `Equiv.Perm`, `Fin`, `Fintype`, `cycleGraph`, `neighborSet`).
- `infra/scan.py` (comments and string literals stripped) reports zero hits in
  Defs.lean and Statement.lean. The only "sorry" string in Statement.lean is inside a
  doc comment ("sorry-free"), which the scanner ignores. The two `sorry` tokens are in
  Main.lean only, which is expected at this stage and not audited here.

## Verdict

No fidelity defect found. The statement faithfully captures the paper's main theorem
and the required scope; the only judgment call (reading "nontrivially unstable" as
"unstable, connected, non-bipartite") is the one the paper's own Verification section
dictates.

MUST-FIX items: none.
