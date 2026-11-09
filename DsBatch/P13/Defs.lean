import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# P13 — Order 14 is the largest order for which every 4-total coloring of
every cubic graph is equitable

Formal objects of arXiv 2609.05259 (Adauto, de Figueiredo, Sasaki, Schneider).

The paper's notions formalised here (Section 2, "Preliminaries"):

* a graph is simple and finite, and is *cubic* when it is 3-regular
  (`SimpleGraph.IsRegularOfDegree 3`);
* the *circular ladder* `L_n` (`n` even, `n ≥ 6`) is the prism
  `C_{n/2} □ K_2`; the required counterexample is
  `L_12 = C_6 □ K_2`, with vertex set `Fin 6 × Fin 2`;
* a *4-total colouring* of a graph assigns one of four colours to each vertex
  and each edge so that adjacent vertices, adjacent edges, and incident
  vertex–edge pairs receive distinct colours;
* the *colour class* of a colour is the set of vertices and edges of that
  colour, and the *colour class configuration* is the multiset of the four
  class cardinalities;
* a colouring is *equitable* if the cardinalities of any two colour classes
  differ by at most one, and *non-equitable* otherwise;
* Stemock's conjecture (Conjecture 1.2 of the paper): every 4-total colouring
  of a cubic graph of order less than 20 is equitable.

The elements of a total colouring of `G : SimpleGraph V` are represented by
`El G = V ⊕ G.edgeSet`: vertices together with the actual edges of `G` (as
unordered pairs, Mathlib's `Sym2`).  This avoids colouring non-edges.

The paper's explicit non-equitable colouring of `L_12` (Section 5, Figure 2)
has configuration `(8,8,8,6)`.  Its vertex profile is `(4,4,4,0)`: one colour
is used on six pairwise independent edges forming a perfect matching (the six
rungs), and each of the other three colours is used on four vertices and four
edges.  `vertexColour`, `pairColour` and `colour12` below give such a
colouring in closed form (the colours are `0,1,2,3` for the paper's
`1,2,3,4`).  Its properness and configuration are verified in
`Statement.lean`/`Main.lean`.
-/

namespace DsBatch.P13

/-! ## The circular ladder `L_12 = C_6 □ K_2` -/

/-- Vertex set of `L_12 = C_6 □ K_2`: `(i, s)` with `i` the position on the
rim cycle and `s` the copy of `C_6`. -/
abbrev V12 : Type := Fin 6 × Fin 2

/-- The circular ladder `L_12 = C_6 □ K_2`, the prism over the 6-cycle. -/
def L12 : SimpleGraph V12 :=
  SimpleGraph.cycleGraph 6 □ SimpleGraph.completeGraph (Fin 2)

instance : DecidableRel L12.Adj := fun x y =>
  decidable_of_iff
    ((SimpleGraph.cycleGraph 6).Adj x.1 y.1 ∧ x.2 = y.2 ∨
      (SimpleGraph.completeGraph (Fin 2)).Adj x.2 y.2 ∧ x.1 = y.1)
    (by simp [L12, SimpleGraph.boxProd_adj])

/-! ## Total colourings -/

/-- The elements of a total colouring of `G`: the vertices of `G` together
with the edges of `G`.  An edge is a `Sym2` pair, i.e. an unordered pair of
vertices. -/
abbrev El {V : Type} (G : SimpleGraph V) : Type := V ⊕ G.edgeSet

/-- Two elements of the total graph conflict when they are adjacent vertices,
adjacent (distinct) edges, or a vertex and an incident edge. -/
abbrev Conflicts {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    El G → El G → Prop
  | Sum.inl u, Sum.inl v => G.Adj u v
  | Sum.inl u, Sum.inr e => u ∈ (e : Sym2 V)
  | Sum.inr e, Sum.inl u => u ∈ (e : Sym2 V)
  | Sum.inr e, Sum.inr f =>
      e ≠ f ∧ ∃ u ∈ (Finset.univ : Finset V), u ∈ (e : Sym2 V) ∧ u ∈ (f : Sym2 V)

instance {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (Conflicts G) := by
  intro x y
  cases x with
  | inl u =>
    cases y with
    | inl v => exact inferInstanceAs (Decidable (G.Adj u v))
    | inr f => exact inferInstanceAs (Decidable (u ∈ (f : Sym2 V)))
  | inr e =>
    cases y with
    | inl v => exact inferInstanceAs (Decidable (v ∈ (e : Sym2 V)))
    | inr f =>
      exact inferInstanceAs
        (Decidable (e ≠ f ∧ ∃ u ∈ (Finset.univ : Finset V),
          u ∈ (e : Sym2 V) ∧ u ∈ (f : Sym2 V)))

/-- A proper total colouring with the four colours `Fin 4`: conflicting
elements receive distinct colours. -/
abbrev ProperTotalColouring {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : El G → Fin 4) : Prop :=
  ∀ x y, Conflicts G x y → c x ≠ c y

/-- `G` is cubic, i.e. 3-regular (the paper's standing hypothesis). -/
abbrev Cubic {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.IsRegularOfDegree 3

/-- The cardinality of the colour class of colour `i`: the number of vertices
and edges receiving colour `i`. -/
abbrev colourClassSize {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : El G → Fin 4) (i : Fin 4) : ℕ :=
  ((Finset.univ : Finset (El G)).filter (fun x => c x = i)).card

/-- The colour class configuration of a 4-total colouring: the multiset of
the four colour class cardinalities. -/
abbrev ColourConfig {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : El G → Fin 4) : Multiset ℕ :=
  (Finset.univ : Finset (Fin 4)).val.map (fun i => colourClassSize G c i)

/-- A 4-total colouring is equitable when the cardinalities of any two colour
classes differ by at most one. -/
abbrev Equitable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : El G → Fin 4) : Prop :=
  ∀ i j : Fin 4, colourClassSize G c i ≤ colourClassSize G c j + 1

/-- A 4-total colouring is non-equitable when it is not equitable. -/
abbrev NonEquitable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : El G → Fin 4) : Prop :=
  ¬ Equitable G c

/-- **Stemock's conjecture** (Conjecture 1.2 of the paper): every 4-total
colouring of a cubic graph of order less than `20` is equitable. -/
def StemockConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V < 20 → Cubic G → ∀ c : El G → Fin 4,
      ProperTotalColouring G c → Equitable G c

/-! ## An explicit non-equitable colouring of `L_12` -/

/-- Vertex colours of the paper's non-equitable colouring: on the copy `s = 0`
the vertex `(i,0)` receives colour `i mod 3`; on the copy `s = 1` the vertex
`(i,1)` receives colour `(i+1) mod 3`.  (Two copies of the 6-cycle are
properly 3-coloured with each colour used four times, and the two colourings
differ across each rung.) -/
def vertexColour : V12 → Fin 4
  | (i, 0) => ⟨i.val % 3, by omega⟩
  | (i, 1) => ⟨(i.val + 1) % 3, by omega⟩

/-- Colours of the rim edges of `L_12`: the edge from `(i,0)` to `(i+1,0)`
(top copy) receives colour `(i+2) mod 3`, and the edge from `(i,1)` to
`(i+1,1)` (bottom copy) receives colour `i mod 3`.  Pairs that are not rim
edges receive an arbitrary value; the rungs are handled by `pairColour` and
receive colour `3`. -/
def pairColour (a b : V12) : Fin 4 :=
  if a.2 = b.2 then
    if a.2 = 0 then
      if (a.1.val + 1) % 6 = b.1.val then ⟨(a.1.val + 2) % 3, by omega⟩
      else if (b.1.val + 1) % 6 = a.1.val then ⟨(b.1.val + 2) % 3, by omega⟩
      else 0
    else
      if (a.1.val + 1) % 6 = b.1.val then ⟨a.1.val % 3, by omega⟩
      else if (b.1.val + 1) % 6 = a.1.val then ⟨b.1.val % 3, by omega⟩
      else 0
  else if a.1 = b.1 then 3 else 0

/-- The colour of an edge (an unordered pair of vertices), as given by
`pairColour` on its two endpoints. -/
def edgeColour (e : Sym2 V12) : Fin 4 :=
  Sym2.lift ⟨pairColour, by decide⟩ e

/-- The explicit non-equitable 4-total colouring of `L_12` of Section 5: the
six rungs have colour `3`, the rim edges have colours among `0,1,2` given by
`pairColour`, and the vertices have colours given by `vertexColour`.  Its
colour class configuration is `(8,8,8,6)`. -/
def colour12 : El L12 → Fin 4
  | Sum.inl v => vertexColour v
  | Sum.inr e => edgeColour (e : Sym2 V12)

end DsBatch.P13
