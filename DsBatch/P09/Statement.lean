import DsBatch.P09.Defs

/-!
# P09 — Statements

The targets of the formalization of arXiv 2609.04257 (Yousof Yavari,
"A Counterexample to Teschner's Bondage-Number Conjecture").

Required scope (from `queue/QUEUE.md`): the 18-vertex cubic bipartite graph `G`
has `γ(G) = 6`, deleting any at most 4 edges leaves `γ = 6`, hence
`b(G) ≥ 5 > 4.5 = (3/2)·Δ(G)`, so Teschner's conjecture is false.

The optional refinement `b(G) = 5` is not part of the required scope and is not
a target here.
-/

namespace DsBatch.P09

open SimpleGraph

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- **Target `graph_structure`.** The paper's graph `G` (Section 3) is a
connected cubic bipartite graph on the 18 vertices `{0, …, 17}`. -/
def graph_structure_statement : Prop :=
  Fintype.card V = 18 ∧ G.Connected ∧ G.IsRegularOfDegree 3 ∧ G.IsBipartite

/-- **Target `gamma_eq_six`.** The domination number of the paper's graph is
`6` (paper Theorem 3.1 / Section 3: `γ(G) = 6`). -/
def gamma_eq_six_statement : Prop :=
  dominationNumber G = 6

/-- **Target `four_edge`.** Deleting any at most four edges of `G` (that is,
"for any edge set `F` with `≤ 4` edges") leaves the domination number equal to
`6`; equivalently `γ(G − F) = 6` (paper Section 3, used for `b(G) ≥ 5`). -/
def four_edge_statement : Prop :=
  ∀ F : Finset (Sym2 V), (∀ e ∈ F, e ∈ G.edgeSet) → F.card ≤ 4 →
    dominationNumber (G.deleteEdges (F : Set (Sym2 V))) = 6

/-- **Target `bondage_ge_five`.** The bondage number of `G` is at least `5`:
no set of at most four edges increases the domination number (paper
Proposition 3.2 / the lower bound `b(G) ≥ 5`). -/
def bondage_ge_five_statement : Prop :=
  5 ≤ bondageNumber G

/-- **Target `teschner_false`.** Teschner's conjecture is false: there is a
finite simple graph with at least one edge whose bondage number exceeds
`(3/2)·Δ`. The witness is the paper's graph `G` (Theorem 1.2 /
Section 3 of the paper). -/
def teschner_false_statement : Prop :=
  ¬ TeschnerConjecture

/-! ## Non-vacuity checks

The explicit graph exists (`18` vertices, and a concrete edge `0–6`), it has a
dominating set of size `6` (this one is in fact a minimum dominating set of the
paper), domination is not automatic (a single vertex does not dominate the
graph), and the statement `TeschnerConjecture` is not a definitional triviality
(it has content: it is a universally quantified inequality in `ℚ`). -/

example : Fintype.card V = 18 := by decide
example : (0 : V) ≠ 6 := by decide
example : G.Adj 0 6 := by decide
example : ¬ G.Adj 0 1 := by decide
example : Dominates G {0, 1, 2, 3, 14, 15} := by
  unfold Dominates
  decide
example : ¬ Dominates G {0} := by
  unfold Dominates
  decide
example : (3 / 2 : ℚ) * 3 = 9 / 2 := by norm_num
example : (4.5 : ℚ) < 5 := by norm_num

end DsBatch.P09
