PASS

# P08 fidelity audit (statement phase S)

Verdict: **PASS**. The two frozen-to-be statements are faithful to the paper
(arXiv 2609.28702) and state exactly the queue's required scope, no more and no
less. `lake build DsBatch` succeeds; `DsBatch/P08/Defs.lean` and
`DsBatch/P08/Statement.lean` are `sorry`-free and contain none of the forbidden
tokens (`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
`implemented_by`, `extern`, `debug.skipKernelTC`); `Main.lean` carries only the
expected `:= by sorry` stubs (allowed at this phase).

## What I checked

### 1. `square` really is G² (distance ≤ 2)
Paper (Preliminaries): "The *square* of a graph $G$ is the graph denoted by
$G^2$ and obtained from $G$ by adding all edges connecting pairs of vertices at
distance 2." (i.e. adjacency = distance 1 or 2, on distinct vertices).

Lean (`Defs.lean`):
```lean
def square (G : SimpleGraph V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ (G.Adj x y ∨ ∃ z, G.Adj x z ∧ G.Adj z y)
```
`G.Adj x y` is distance 1; `∃ z, G.Adj x z ∧ G.Adj z y` is distance exactly 2
(looplessness forces `z ≠ x`, `z ≠ y`). The `x ≠ y` conjunct excludes loops.
This is exactly "distance ≤ 2", and the doc comment correctly notes that
vertices in different components (distance `∞`) are not adjacent. **Correct.**

### 2. `IsSquareComplementary` really means G² ≅ Ḡ
Paper: "a graph $G$ is *square-complementary* (squco) if $G^2 \cong
\overline{G}$".

Lean (`Defs.lean`):
```lean
def sq (G : SimpleGraph V) : SimpleGraph V := (square G)ᶜ
def IsSquareComplementary (G : SimpleGraph V) : Prop := Nonempty (square G ≃g Gᶜ)
```
`Gᶜ` is the complement (adjacent iff non-adjacent in `G`), `≃g` is graph
isomorphism. This is `G² ≅ Ḡ` verbatim, not a weakened/strengthened variant.
**Correct.**

### 3. `IsNontrivialGraph` really means ≥ 2 vertices
Paper: "A graph is *nontrivial* if it has at least two vertices".

Lean:
```lean
def IsNontrivialGraph (_G : SimpleGraph V) [Fintype V] : Prop := 2 ≤ Fintype.card V
```
**Correct.** The `Fintype` bound matches the paper's "only simple, finite,
undirected graphs" (and is present on both statements).

### 4. `closedNhd` / `DominatedBy`
Paper: "$N[x]=N_G[x]$" the closed neighborhood, and "A vertex *x is dominated
by* a vertex y if $N[x]\subseteq N[y]$".

Lean:
```lean
def closedNhd (G : SimpleGraph V) (x : V) : Set V := {x} ∪ G.neighborSet x
def DominatedBy (G : SimpleGraph V) (x y : V) : Prop := closedNhd G x ⊆ closedNhd G y
```
`neighborSet x` is the open neighborhood `N(x)`, so `closedNhd` is
`N[x] = {x} ∪ N(x)` and `DominatedBy` is `N[x] ⊆ N[y]`. **Correct.**

### 5. `IsSimplicial` (paper definition)
Paper: "A vertex $x$ is *simplicial* if $N[x]$ induces a complete subgraph of $G$".

Lean:
```lean
def IsSimplicial (G : SimpleGraph V) (x : V) : Prop := G.IsClique (closedNhd G x)
```
`IsClique s` is `s.Pairwise G.Adj` = any two *distinct* vertices of `s` are
adjacent, i.e. `N[x]` induces a complete subgraph. **Correct.**

### 6. The two targets are exactly the required scope
Queue scope (row P08): "required: in a nontrivial square-complementary graph no
two distinct vertices have comparable closed neighbourhoods, hence no simplicial
vertex".

Target 1 (`Statement.lean`):
```lean
def no_comparable_closed_neighborhoods_statement : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    IsSquareComplementary G → IsNontrivialGraph G →
      ∀ x y : V, x ≠ y → ¬ (DominatedBy G x y ∨ DominatedBy G y x)
```
This is "no two *distinct* vertices have comparable closed neighbourhoods"
(neither direction of `N[x] ⊆ N[y]`). It matches the paper's Lemma 3.1
(`lem:notruedompairs`: "$G$ does not contain true dominating pairs", where a true
dominating pair is an unordered pair $\{x,y\}$ with $N[x]\subseteq N[y]$) and
the abstract ("no two vertices have comparable closed neighborhoods"). It also
subsumes the "no true twins" item of Theorem 3.2, since $N[x]=N[y]$ is a special
case of comparability. Hypotheses are exactly `IsSquareComplementary G` and
`IsNontrivialGraph G` — no extra hypotheses, no conclusion-as-hypothesis, no
weakening.

Target 2 (`Statement.lean`):
```lean
def no_simplicial_vertex_statement : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    IsSquareComplementary G → IsNontrivialGraph G → ∀ x : V, ¬ IsSimplicial G x
```
This is the "hence no simplicial vertex" part of the abstract and of Theorem
3.2 (`thm:notruetwins`). Same hypotheses, no extras. **Correct.**

**Exactly the required scope, no more and no less**: the optional "not chordal"
and "not distance-hereditary" parts are correctly omitted (per the scope, they
are attempted only after the required part is proved).

### 7. Legitimacy of "hence" (isolated-vertex subtlety)
"Is no simplicial vertex a legitimate corollary of the first target?" Not by
pure logic alone: an *isolated* vertex has `N[x] = {x}`, which trivially induces
a complete subgraph, so an isolated vertex is simplicial while producing no
comparable-closed-neighbourhood pair. The corollary is valid only because a
nontrivial squco graph has no isolated vertices. This is delivered by the paper's
Theorem 2.1 (`thm:squco-radius-diameter`): a nontrivial squco graph is connected
with radius 3 (and squco graphs are "free of pendant vertices"), so every vertex
has a neighbour. The statements do **not** add "connected" or "no isolated
vertex" as a hypothesis — instead the proof of the second target must derive
non-isolation from `IsSquareComplementary G` + `IsNontrivialGraph G` (via
Theorem 2.1). That is a legitimate consequence of the stated hypotheses, not a
restatement of the conclusion as a hypothesis, so there is no fidelity problem.
This is the isolated-vertex subtlety flagged in the scope; it affects the proof
plan, not the statement's faithfulness. (Note also that the nontriviality
hypothesis is *essential* for this target: the one-vertex graph is squco and its
single vertex is simplicial.)

### 8. `project.json`
- `targets`:
  - `{"name": "DsBatch.P08.no_comparable_closed_neighborhoods", "lean_type": "DsBatch.P08.no_comparable_closed_neighborhoods_statement"}`
  - `{"name": "DsBatch.P08.no_simplicial_vertex", "lean_type": "DsBatch.P08.no_simplicial_vertex_statement"}`
  These match the theorem names in `Main.lean` (`theorem
  no_comparable_closed_neighborhoods : no_comparable_closed_neighborhoods_statement`,
  `theorem no_simplicial_vertex : no_simplicial_vertex_statement`) and the
  `_statement` defs in `Statement.lean`. **Correct.**
- `scope` string is byte-identical to the queue row P08 scope (including the
  optional parts).
- `cap_cny` = 4.0 = queue cap; `chunk_min` = 100 = TASK chunk length.
  **Unchanged from the queue.**

### 9. Non-vacuity examples in `Statement.lean`
- `sevenCycleEquiv` is multiplication by 2 mod 7 with inverse ×4 (2·4 ≡ 1 mod 7).
- `sevenCycleIso : square (cycleGraph 7) ≃g (cycleGraph 7)ᶜ` is checked by
  `fin_cases <;> decide`. Spot-check (LaTeX-free): C₇² edges are pairs at cyclic
  distance 1 or 2; C̄₇ edges are pairs at cyclic distance 2 or 3; the map
  x ↦ 2x sends differences {±1, ±2} to {±2, ±4} ≡ {±2, ∓3}, i.e. exactly the
  C̄₇ differences. So the isomorphism claim is genuine.
- `example : IsSquareComplementary (cycleGraph 7) := ⟨sevenCycleIso⟩` and
  `example : IsNontrivialGraph (cycleGraph 7)` show the hypotheses are
  satisfiable.
- `example : ¬ DominatedBy (cycleGraph 7) 0 1` shows the conclusion is not
  vacuously true (in C₇, `6 ∈ N[0]` but `6 ∉ N[1]`).
- `example : DominatedBy (⊤ : SimpleGraph (Fin 2)) 0 1` (K₂: the two vertices
  have equal closed neighbourhoods) and `example : IsSimplicial (⊤ : SimpleGraph
  (Fin 2)) 0` show `DominatedBy`/`IsSimplicial` are not trivially false.
- `example : IsSquareComplementary (⊥ : SimpleGraph (Fin 1))` and
  `example : ¬ IsNontrivialGraph (⊥ : SimpleGraph (Fin 1))` show the
  nontriviality hypothesis genuinely excludes the one-vertex squco graph.
All examples are legitimate and compile (build succeeded).

### 10. Build / hygiene
`lake build DsBatch` completes; `DsBatch.P08.Statement` and `DsBatch.P08.Main`
build (Main with the two expected `sorry` declarations, flagged by the
compiler). `Defs.lean` and `Statement.lean` contain no `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`/`implemented_by`/`extern`/`debug.skipKernelTC`; the
`decide`/`fin_cases`/`norm_num` usage is kernel-checkable, as required.

## Gaps / risks (none blocking)
- The proof of `no_simplicial_vertex` will need the non-isolation (connectedness,
  Theorem 2.1) argument, per §7 above; this is a proof-phase obligation, not a
  statement defect.
- `ball2` is defined but unused by the statements; it is a faithful definition
  (dist ≤ 2) and harmless.
- Doc comments in `Defs.lean` state facts about squco graphs ("distance ≥ 3"
  adjacency in `sq G`); these are true for the relevant connected case and are
  comments only, not load-bearing.
