import DsBatch.P13.Defs

/-!
# P13 — Statements

Formal targets of arXiv 2609.05259 (Adauto, de Figueiredo, Sasaki, Schneider,
"Order 14 is the largest order for which every 4-total coloring of every
cubic graph is equitable").

Required scope (from `queue/QUEUE.md`): the circular ladder
`L_12 = C_6 □ K_2` (12 vertices, cubic) has a 4-total colouring (colours on
its 12 vertices and 18 edges; adjacent vertices, adjacent edges and incident
vertex–edge pairs get distinct colours) with colour class sizes `(8,8,8,6)`,
hence not equitable, so Stemock's conjecture is false.

The three targets below state exactly this:

* `l12_structure` — `L_12` is the prism `C_6 □ K_2`, with 12 vertices,
  18 edges, and is cubic;
* `l12_nonequitable_colouring` — `L_12` has a proper 4-total colouring whose
  colour class configuration is `(8,8,8,6)`, and it is non-equitable;
* `stemock_conjecture_false` — the universal statement "every 4-total
  colouring of a cubic graph of order less than 20 is equitable"
  (`StemockConjecture`) is false.

The optional parts of the paper (equitability at orders 6, 8, 10, 14; the
order-12, order-16 and order-18 configuration theorems; splicing) are not
part of the required scope and are not stated here.
-/

namespace DsBatch.P13

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- **Target `l12_structure`.** The circular ladder `L_12 = C_6 □ K_2` has
12 vertices and 18 edges, and is cubic. -/
def l12_structure_statement : Prop :=
  Fintype.card V12 = 12 ∧ Fintype.card L12.edgeSet = 18 ∧ Cubic L12

/-- **Target `l12_nonequitable_colouring`.** The circular ladder `L_12` has a
proper 4-total colouring — colours on its 12 vertices and 18 edges, with
adjacent vertices, adjacent edges and incident vertex–edge pairs getting
distinct colours — whose colour class configuration is `(8,8,8,6)`.  Such a
colouring is not equitable. -/
def l12_nonequitable_colouring_statement : Prop :=
  ∃ c : El L12 → Fin 4,
    ProperTotalColouring L12 c ∧
    ColourConfig L12 c = ({8, 8, 8, 6} : Multiset ℕ) ∧
    NonEquitable L12 c

/-- **Target `stemock_conjecture_false`.** Stemock's conjecture (Conjecture
1.2 of the paper) is false: not every 4-total colouring of a cubic graph of
order less than 20 is equitable. -/
def stemock_conjecture_false_statement : Prop := ¬ StemockConjecture

/-! ## Non-vacuity checks

The explicit object satisfies the hypotheses, the defined properties are not
vacuous, and neither `ProperTotalColouring` nor `Equitable` is trivially
true or trivially false. -/

/-- `L_12` has 12 vertices. -/
example : Fintype.card V12 = 12 := by decide

/-- `L_12` has 18 edges. -/
example : Fintype.card L12.edgeSet = 18 := by decide

/-- `L_12` is cubic. -/
example : Cubic L12 := by unfold Cubic SimpleGraph.IsRegularOfDegree; decide

/-- `L_12` is the prism `C_6 □ K_2`: `(0,0)` is adjacent to the next rim
vertex `(1,0)`, to the rung partner `(0,1)`, and not to the opposite rim
vertex `(2,0)`. -/
example : L12.Adj ((0, 0) : V12) ((1, 0) : V12) := by decide
example : L12.Adj ((0, 0) : V12) ((0, 1) : V12) := by decide
example : ¬ L12.Adj ((0, 0) : V12) ((2, 0) : V12) := by decide

/-- The explicit colouring `colour12` is a proper 4-total colouring of
`L_12`: the object satisfies the property. -/
example : ProperTotalColouring L12 colour12 := by decide

/-- Properness is a real constraint: the constant colouring is not proper. -/
example : ¬ ProperTotalColouring L12 (fun _ => (0 : Fin 4)) := by decide

/-- The colour class configuration of `colour12` is really `(8,8,8,6)`. -/
example : ColourConfig L12 colour12 = ({8, 8, 8, 6} : Multiset ℕ) := by decide

/-- That colouring is non-equitable. -/
example : NonEquitable L12 colour12 := by decide

/-- `Equitable` is not trivially false: the two-vertex complete graph `K_2`
has a proper 4-total colouring (its two vertices get colours `0,1` and its
unique edge gets colour `2`) whose colour classes have sizes `1,1,1,0`. -/
example :
    ∃ c : El (SimpleGraph.completeGraph (Fin 2)) → Fin 4,
      ProperTotalColouring (SimpleGraph.completeGraph (Fin 2)) c ∧
      Equitable (SimpleGraph.completeGraph (Fin 2)) c :=
  ⟨fun x => match x with
    | Sum.inl i => Fin.castSucc (Fin.castSucc i)
    | Sum.inr _ => 2,
   by decide, by decide⟩

/-- The hypothesis class of `StemockConjecture` is not empty: `L_12` is a
cubic graph of order `12 < 20`. -/
example : Fintype.card V12 < 20 ∧ Cubic L12 :=
  ⟨by decide, by unfold Cubic SimpleGraph.IsRegularOfDegree; decide⟩

end DsBatch.P13
