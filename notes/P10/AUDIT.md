PASS

Audit of `DsBatch/P10/{Defs,Statement,Main}.lean` and `projects/P10/project.json`
against `papers/2609.38417/LTCC.tex` (read in full). Verdict: the formalization is
faithful to the paper and to the queue's required scope; no fidelity errors found.

## 1. The graph `G` (Defs.lean)

- Vertex set `V := (Fin 4 × Priv) ⊕ Term` with `Term = {p : Fin 4 × Fin 4 // p.1 ≠ p.2}`.
  This is `4·2 + 4·3 = 20` vertices, exactly the paper's blocks `B_1..B_4` each with
  private vertices `a_i,b_i` and terminals `v_{i,j}` (`j ≠ i`).
- The adjacency relation `rel` encodes exactly the paper's edges:
  - a private vertex `a_i`/`b_i` is joined to a terminal `v_{k,l}` iff `i = k`
    (internal edges `a_i v_{i,j}`, `b_i v_{i,j}`), giving each block its `K_{2,3}`;
  - terminal `v_{p.1,p.2}` is joined to `v_{q.1,q.2}` iff `q.1 = p.2 ∧ q.2 = p.1`,
    i.e. the unique cross edge `v_{i,j}v_{j,i}`;
  - all other cases (`private–private`, `private–terminal` of a different block,
    `terminal–terminal` within a block) are `False`.
  No loops arise (the cross-edge condition forces `p.1 ≠ p.2`), and `G` is built via
  `SimpleGraph.fromRel`, so it is simple (loopless, symmetric) by construction, matching
  the paper's "simple cubic graph".
- `Cubic := ∀ v, G.degree v = 3` is the correct notion (degree three at every vertex).
  Each private vertex has exactly three terminal neighbours; each terminal `v_{i,j}` is
  adjacent to `a_i`, `b_i` and `v_{j,i}` — degree three. So `G` is the claimed cubic graph.
- The edge type `E := (Term × Priv) ⊕ CrossIdx` has `12·2 + 6 = 30` elements, and `G` has
  `20·3/2 = 30` edges; `eLeft`/`eRight` map each `E`-element to the correct endpoints
  (`a_i v_{i,j}`, `b_i v_{i,j}`, `v_{i,j}v_{j,i}`), so `E` is exactly the graph's edge set
  — no missing or extra incidences.

## 2. Total colouring notion

`elAdj` matches Section 1 of the paper ("adjacent vertices receive different colours,
edges sharing an endpoint receive different colours, and each edge receives a colour
different from those of its endpoints"):
- vertex–vertex: `G.Adj u w`;
- vertex–edge / edge–vertex: `eLeft e = u ∨ eRight e = u` (edge incident to its endpoint);
- edge–edge: `e ≠ f` and the two edges share an endpoint.
`ProperTotalColoring` is `∀ x y, elAdj x y → c x ≠ c y`, i.e. exactly a proper total
colouring. Correct.

## 3. The explicit 4-colouring `colour4`

Matches the paper's Section 2 colouring exactly (0-based indices; paper colour `k` is
index `k-1`, paper colour `4` is index `3`):
- private vertices and cross edges get colour `3` (= paper `4`);
- `termColour` reproduces the table on p. 2 verbatim:
  `c(v_{i,j}) = j` for `i,j ≤ 3`, `c(v_{i,4}) = i` for `i ≤ 3`, and
  `(c(v_{4,1}),c(v_{4,2}),c(v_{4,3})) = (2,3,1)`;
- internal edges: the `a_i`-edge at a terminal of colour `r` gets the cyclic successor
  (`cycSucc`, `r+1 mod 3`) and the `b_i`-edge gets the cyclic predecessor (`cycPred`,
  `r+2 mod 3`), exactly "follows" / "precedes" in the paper (also matching Figure 1's
  `σ = (1 2 3)` / `σ²`). Verified case-by-case against both the table and Figure 1.

## 4. The list assignment `Lstar`

Matches the paper's description and Figure 2 exactly:
- every vertex and internal edge of `B_i` has list `{1,2,3,4,5} \ {i}` — encoded as
  `Finset.univ.erase (Fin.castSucc (block i))` (0-based, omitting index `i-1` = paper `i`);
- consecutive cross edges `B_iB_{i+1}` (cyclically) omit `i+2` (cyclically) — `omitCol`
  returns `(i.val+2)%4` when `j = i+1 (mod 4)`, and the symmetric branch when `i = j+1`;
- the two remaining cross edges `B_1B_3` and `B_2B_4` omit `5` — `omitCol`'s fallback is
  index `4` (paper `5`). Verified all six cross edges against Figure 2's
  `{3}{2}{4}{1}{5}{5}` (i.e. omits 3, 2, 4, 1, 5, 5). `omitCol` is symmetric, so the
  canonical `CrossIdx` ordering (`p.1 < p.2`) is irrelevant. Correct.

## 5. Statements (Statement.lean)

- `graph_structure_statement := Fintype.card V = 20 ∧ Cubic` — the paper's "simple cubic
  graph on 20 vertices" (simplicity is type-level via `SimpleGraph`). No extra hypotheses,
  no weakening.
- `total_colouring_statement := TotalColouringExists ∧ ¬ ∃ c : El → Fin 3, ProperTotalColoring c`,
  with `TotalColouringExists := ∃ c : El → Fin 4, ProperTotalColoring c`. This is exactly
  `χ''(G) = 4` (a 4-colouring exists, none with ≤3 colours). Correct.
- `list_assignment_statement := (∀ x : El, (Lstar x).card = 4) ∧ ¬ ListTotalColourable Lstar`.
  `ListTotalColourable L := ∃ c : El → Fin 5, ProperTotalColoring c ∧ ∀ x, c x ∈ L x` demands
  both properness and list membership for every vertex and edge. Correct — it states `Lstar`
  is a 4-list assignment with no proper list total colouring.
- `counterexample_statement := graph_structure_statement ∧ total_colouring_statement ∧ list_assignment_statement`.
  This establishes `χ''_ℓ(G) ≥ 5 > 4 = χ''(G)`, i.e. `χ''_ℓ > χ''` and the LTCC is false —
  exactly the queue's required scope.

Scope note (not an error): the paper's Theorem 1 states `χ''_ℓ(G) = 5` (needing the
Juvan–Mohar–Škrekovski upper bound `χ''_ℓ ≤ Δ+2 = 5`). The queue explicitly marks
`χ''_ℓ = 5` as *optional* and out of required scope, and Statement.lean documents this in
its header. The formalized counterexample statement asserts only the required
`χ''_ℓ > χ''`, so it is faithful to the required scope; it does not silently claim the
optional equality.

## 6. Non-vacuity

All examples in Statement.lean compile and contain no `sorry`/`admit`/`axiom` (grep
confirmed; the only "admit" hits are the English word "admits" in docstrings). They are
meaningful:
- `Fintype.card V = 20` and `Cubic` — the explicit object satisfies the structural hypotheses;
- `ProperTotalColoring colour4` — the paper's colouring really is proper (so a 4-colouring
  exists), while `¬ ProperTotalColoring (fun _ => 0)` shows properness is not automatic;
- `∀ x : El, (Lstar x).card = 4` — `Lstar` really is a 4-list assignment;
- `ListTotalColourable (fun _ => univ)` (via `colour4`) — list total colourability is not
  vacuous with the full lists;
- `G.Adj (va 0) (vt 0 1 …)` and `¬ G.Adj (va 0) (vb 0)` — the graph is non-trivial.

## 7. project.json ↔ Main.lean ↔ Statement.lean

Each target in `projects/P10/project.json` matches a theorem in `Main.lean` and the
corresponding `_statement` definition in `Statement.lean`:
`graph_structure`/`graph_structure_statement`, `total_colouring`/`total_colouring_statement`,
`list_assignment`/`list_assignment_statement`, `counterexample`/`counterexample_statement`.
Names and `lean_type` fields all agree.

## 8. Compilation

`lake env lean DsBatch/P10/Statement.lean` compiles cleanly (no output);
`lake build DsBatch` succeeds. The only warnings are benign (unused `simp` args in Defs.lean,
a `module` suggestion, and the expected `sorry` stubs in `Main.lean` — proofs are produced
later and this is not a fidelity failure).
