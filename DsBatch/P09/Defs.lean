import Mathlib

/-!
# P09 — a counterexample to Teschner's bondage-number conjecture
(arXiv 2609.04257, Yousof Yavari)

Formal objects of the paper:

* the explicit graph `G` on `V(G) = {0, …, 17}` with the 27 edges of
  Eq. (3.2) (`eq:edge-set`);
* a *dominating set* `D` of a graph `H`: every vertex outside `D` has a
  neighbour in `D` (paper §2);
* the *domination number* `γ(H)`, the minimum cardinality of a dominating set;
* the *maximum degree* `Δ(H)`;
* the *bondage number* `b(H)`, the least number of edges whose deletion
  increases the domination number (paper Eq. (2.2), `eq:bondage-definition`);
* Teschner's conjecture (paper Conjecture 1.1, `conj:Teschner`).
-/

namespace DsBatch.P09

open SimpleGraph

/-- The vertex type of the paper's graph: `V(G) = {0, 1, …, 17}`. -/
abbrev V : Type := Fin 18

/-- The 27 edges of the paper's graph, Eq. (3.2) (`eq:edge-set`), listed as
ordered pairs (the pairs of the paper are unordered). -/
def edgeList : List (V × V) :=
  [(0, 6), (0, 10), (0, 16), (1, 8), (1, 11), (1, 12), (2, 4), (2, 5), (2, 13),
   (3, 4), (3, 5), (3, 9), (4, 16), (5, 11), (6, 7), (6, 13), (7, 8), (7, 14),
   (8, 13), (9, 10), (9, 14), (10, 15), (11, 15), (12, 15), (12, 17), (14, 17),
   (16, 17)]

/-- The paper's graph `G` (Section 3): the simple graph with vertex set
`{0, …, 17}` and the 27 edges of Eq. (3.2). -/
def G : SimpleGraph V := SimpleGraph.fromRel (fun u v => (u, v) ∈ edgeList)

instance instDecidableRelGAdj : DecidableRel G.Adj := by
  unfold G
  infer_instance

instance instFintypeGEdgeSet : Fintype G.edgeSet := by
  unfold G
  infer_instance

/-- `D` is a dominating set of `H`: every vertex outside `D` has a neighbour in
`D` (paper §2). -/
def Dominates {V : Type*} (H : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v : V, v ∈ D ∨ ∃ u ∈ D, H.Adj v u

/-- The domination number `γ(H)`: the minimum cardinality of a dominating set. -/
noncomputable def dominationNumber {V : Type*} [Fintype V] (H : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ D : Finset V, D.card = n ∧ Dominates H D}

/-- The maximum degree `Δ(H)`. -/
noncomputable def maxDegree {V : Type*} [Fintype V] (H : SimpleGraph V) : ℕ :=
  Finset.univ.sup (fun v => (H.neighborSet v).ncard)

/-- The bondage number `b(H)` (paper Eq. (2.2)): the least number of edges whose
deletion increases the domination number. -/
noncomputable def bondageNumber {V : Type*} [Fintype V] (H : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ F : Finset (Sym2 V), (∀ e ∈ F, e ∈ H.edgeSet) ∧ F.card = k ∧
    dominationNumber (H.deleteEdges (F : Set (Sym2 V))) > dominationNumber H}

/-- Teschner's conjecture (paper Conjecture 1.1): every finite simple graph with
at least one edge satisfies `b(G) ≤ (3/2)·Δ(G)`. -/
def TeschnerConjecture : Prop :=
  ∀ {V : Type} [Fintype V] (H : SimpleGraph V), (∃ e, e ∈ H.edgeSet) →
    (bondageNumber H : ℚ) ≤ (3 / 2 : ℚ) * (maxDegree H : ℚ)

end DsBatch.P09
