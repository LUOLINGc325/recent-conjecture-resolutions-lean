# P10 — DONE

Paper: arXiv 2609.38417, Jonathan A. Noel, *The List Total Colouring Conjecture
is False*.

**Status: proved.** `bash infra/eval.sh P10` reports `main_status: proved`
(`frozen_ok=true`, `build_ok=true`, `static_hits=0`); all four targets have
axioms `[propext, Classical.choice, Quot.sound]`, and the fidelity audit in
`projects/P10/AUDIT.md` starts with `PASS`.

## What is proved

For the explicit graph `G` of Section 2 (four copies of `K_{2,3}` on private
vertices `a_i, b_i` and terminals `v_{i,j}`, with the cross edges
`v_{i,j}v_{j,i}`):

| target | proved statement |
|---|---|
| `DsBatch.P10.graph_structure` | `Fintype.card V = 20 ∧ Cubic` — the graph is simple by construction and cubic on 20 vertices. |
| `DsBatch.P10.total_colouring` | `TotalColouringExists ∧ ¬ ∃ c : El → Fin 3, ProperTotalColoring c` — the explicit four-colouring of Section 2 is proper, and there is no proper total 3-colouring (at a vertex of degree 3, the vertex and its three incident edges are four pairwise conflicting elements). Hence `χ''(G) = 4`. |
| `DsBatch.P10.list_assignment` | `(∀ x : El, (Lstar x).card = 4) ∧ ¬ ListTotalColourable Lstar` — `Lstar` (Figure 2) assigns a list of four colours to every vertex and every edge, and `G` has no proper total colouring drawn from these lists. Hence `χ''_ℓ(G) > 4`. |
| `DsBatch.P10.counterexample` | The conjunction: the List Total Colouring Conjecture fails at this graph, `χ''_ℓ > χ''`. |

Together: a simple cubic graph on 20 vertices with a total 4-colouring and a
4-list assignment on its vertices and edges admitting no proper list total
colouring, so `χ''_ℓ > χ''` and the LTCC is false.

The proof in `DsBatch/P10/Proof.lean` follows the paper: the `K_{2,3}` lemma
(two private vertices of a block have equal colours), the sets `S_i = {i, s_i}`,
the fact that every cross edge is coloured in `S_i ∩ S_j`, the four-sets
common-element step (kernel `decide` over the 625 functions `Fin 4 → Fin 5`),
and the final cross edge whose list omits the common colour.

## Size and effort

- Lean: 992 lines total — `Defs.lean` 320, `Statement.lean` 81,
  `Proof.lean` 563, `Main.lean` 28.
- Frozen files: `DsBatch/P10/Defs.lean` SHA-256
  `92a59ad13c580c182b32743ba7585f8bdf076dfebef3d6b98ec92be451781d3d`,
  `DsBatch/P10/Statement.lean` SHA-256
  `3cbdcc7c6b95ccf553a34198d80e7ad5d147dc55ed62fce4dc2db04e7c769005`.
- Spend: 1.418866 CNY of the 5.0 CNY cap; 1 chunk.
- Wall time: 2026-11-05T17:20:56Z → 2026-11-05T17:46:50Z (about 26 minutes).

## Paper gaps / deviations reported plainly

- The optional refinement `χ''_ℓ(G) = 5` was **not** formalized. Its upper
  bound `χ''_ℓ(G) ≤ 5` is not proved in the paper; the paper cites
  Juvan–Mohar–Škrekovski [98, Theorem 3.1] (`χ''_ℓ ≤ 5` for every cubic
  graph). The required direction, a 4-list assignment with no proper total
  colouring, is fully formalized, and it yields `χ''_ℓ ≥ 5` once `χ''_ℓ` is
  defined in the usual way; combined with the proved `χ'' = 4` this is
  `χ''_ℓ > χ''`.
- The targets are stated in witness form (explicit colouring, explicit list
  assignment, explicit excluded 3-colouring) rather than through a general
  `sInf`-defined `χ''`/`χ''_ℓ`. This is exactly the queue's required scope;
  it is not a weakening, since the witness statements are the content from
  which the inequality between the invariants follows.
- No mathematical error was found in the paper's counterexample or its proof.
  The graph, the four-colouring (terminal table and cyclic edge colours), and
  the list assignment (Figure 2: omitted colours `3,2,4,1,5,5` for the cross
  edges) were checked element by element against the Lean formalization. The
  only citation the paper relies on beyond the explicit construction is the
  Juvan–Mohar–Škrekovski upper bound, which is needed only for the optional
  `χ''_ℓ = 5`.
