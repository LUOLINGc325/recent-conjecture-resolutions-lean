import DsBatch.P10.Defs

/-!
# P10 — Statements

Formal targets of arXiv 2609.38417 (Jonathan A. Noel, "The List Total
Colouring Conjecture is False").

Required scope (from `queue/QUEUE.md`): the explicit cubic graph of Section 2
has a total 4-colouring and a 4-list assignment on its vertices and edges with
no proper list total colouring, so `χ''_ℓ > χ''` and the List Total Colouring
Conjecture is false.  The optional refinement `χ''_ℓ = 5` (which needs the
Juvan–Mohar–Škrekovski bound `χ''_ℓ ≤ Δ + 2`) is not part of the required
scope and is not a target here.

Each target is a proposition about the explicit objects of `Defs.lean`.  The
interpretation as `χ''_ℓ > χ''` is: `total_colouring_statement` exhibits a
proper total colouring with four colours and excludes three, while
`list_assignment_statement` exhibits an assignment of four-element lists, one
for every vertex and every edge, that admits no proper total colouring at all —
so the list total chromatic number is strictly larger than the total chromatic
number.
-/

namespace DsBatch.P10

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- **Target `graph_structure`.** The graph `G` of Section 2 is a cubic graph on
`20` vertices.  It is built as a `SimpleGraph`, so it is simple by
construction; `Cubic` says every vertex has degree three. -/
def graph_structure_statement : Prop := Fintype.card V = 20 ∧ Cubic

/-- **Target `total_colouring`.** The total chromatic number of `G` is `4`:
`G` has a proper total colouring with four colours (the explicit one of
Section 2), and none with three colours. -/
def total_colouring_statement : Prop :=
  TotalColouringExists ∧ ¬ ∃ c : El → Fin 3, ProperTotalColoring c

/-- **Target `list_assignment`.** The assignment `Lstar` of Section 2 is a list
assignment of size four on all vertices and edges (every list has four
colours), and `G` has no proper total colouring whose colours are drawn from
these lists — so `G` is not `Lstar`-list-total-colourable. -/
def list_assignment_statement : Prop :=
  (∀ x : El, (Lstar x).card = 4) ∧ ¬ ListTotalColourable Lstar

/-- **Target `counterexample` (headline).** The List Total Colouring Conjecture
is false: the explicit simple cubic graph on `20` vertices of Section 2 has a
total 4-colouring and carries a 4-list assignment on its vertices and edges
with no proper list total colouring.  Hence `χ''_ℓ > χ''` for this graph,
against the conjecture that the two invariants always agree. -/
def counterexample_statement : Prop :=
  graph_structure_statement ∧ total_colouring_statement ∧ list_assignment_statement

/-! ## Non-vacuity checks -/

/-- The explicit object satisfies the structural hypothesis: it has `20`
vertices and every vertex has degree three. -/
example : Fintype.card V = 20 := by decide
example : Cubic := by decide

/-- The explicit four-colouring of the paper is proper, so `ProperTotalColoring`
is satisfiable; the constant colouring is not proper, so it is not automatic. -/
example : ProperTotalColoring colour4 := by decide
example : ¬ ProperTotalColoring (fun _ => (0 : Fin 4)) := by decide

/-- Every list of `Lstar` has four elements, so `Lstar` really is a 4-list
assignment. -/
example : ∀ x : El, (Lstar x).card = 4 := by decide

/-- `ListTotalColourable` is not vacuous: with the full lists, the paper's
four-colouring uses only allowed colours. -/
example : ListTotalColourable (fun _ => (Finset.univ : Finset (Fin 5))) :=
  ⟨fun x => Fin.castSucc (colour4 x), by decide, fun _ => Finset.mem_univ _⟩

/-- The graph is not trivial: it has an edge and a non-edge. -/
example : G.Adj (va 0) (vt 0 1 (by decide)) := by decide
example : ¬ G.Adj (va 0) (vb 0) := by decide

end DsBatch.P10
