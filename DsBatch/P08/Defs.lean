import Mathlib

/-!
# P08: There are no nontrivial chordal square-complementary graphs
(arXiv 2609.28702, Aboulker–Milanič–Muršič–Pizaña)

Formal objects of the paper.

A graph `G` is **square-complementary** (`squco`) when its square `G²` is
isomorphic to its complement `Ḡ` (equivalently `G ≅ (G²)ᶜ`).  The paper proves
that in a nontrivial squco graph no two distinct vertices have comparable
closed neighbourhoods, hence there is no simplicial vertex.

Terminology follows the paper:
* `N[x] = {x} ∪ N(x)` is the closed neighbourhood of `x`;
* `B₂(x) = {y | dist_G x y ≤ 2}` is the closed ball of radius two at `x`
  (defined here by an explicit distance-at-most-two condition, so that it also
  makes sense in disconnected graphs);
* `sq G = (G²)ᶜ` is the complement of the square;
* a vertex is *simplicial* when its closed neighbourhood induces a complete
  subgraph.
-/

namespace DsBatch.P08

open SimpleGraph

variable {V : Type*}

/-- The square `G²` of a graph `G`: two distinct vertices are adjacent when they
are adjacent in `G` or have a common neighbour in `G`, i.e. when they are at
distance at most two.  (Vertices in different components of a disconnected
graph are at distance `∞ > 2` and are correctly not adjacent in `G²`.) -/
def square (G : SimpleGraph V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ (G.Adj x y ∨ ∃ z, G.Adj x z ∧ G.Adj z y)
  symm := ⟨fun _ _ h =>
    ⟨h.1.symm, h.2.elim (fun hxy => Or.inl hxy.symm)
      (fun ⟨z, hxz, hzy⟩ => Or.inr ⟨z, hzy.symm, hxz.symm⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance instDecidableRelSquare (G : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] : DecidableRel (square G).Adj :=
  fun _ _ => by
    dsimp only [square]
    infer_instance

/-- The complement of the square, `sq G = (G²)ᶜ`.  In a squco graph `G` one has
`G ≃ sq G`, and two distinct vertices are adjacent in `sq G` exactly when their
distance in `G` is at least three. -/
def sq (G : SimpleGraph V) : SimpleGraph V := (square G)ᶜ

/-- The closed neighbourhood `N[x] = {x} ∪ N(x)`. -/
def closedNhd (G : SimpleGraph V) (x : V) : Set V := {x} ∪ G.neighborSet x

/-- `DominatedBy G x y` means `N[x] ⊆ N[y]`: the vertex `x` is dominated by `y`
(the closed neighbourhoods are comparable). -/
def DominatedBy (G : SimpleGraph V) (x y : V) : Prop := closedNhd G x ⊆ closedNhd G y

/-- The closed ball of radius two at `x`,
`B₂(x) = {y | dist_G x y ≤ 2} = {x} ∪ N(x) ∪ {y | ∃ z, x ~ z ~ y}`. -/
def ball2 (G : SimpleGraph V) (x : V) : Set V :=
  {y | y = x ∨ G.Adj x y ∨ ∃ z, G.Adj x z ∧ G.Adj z y}

/-- A vertex `x` is simplicial when its closed neighbourhood `N[x]` induces a
complete subgraph of `G`. -/
def IsSimplicial (G : SimpleGraph V) (x : V) : Prop := G.IsClique (closedNhd G x)

/-- A graph is square-complementary when `G² ≅ Ḡ`. -/
def IsSquareComplementary (G : SimpleGraph V) : Prop := Nonempty (square G ≃g Gᶜ)

/-- A graph is nontrivial when it has at least two vertices. -/
def IsNontrivialGraph (_G : SimpleGraph V) [Fintype V] : Prop := 2 ≤ Fintype.card V

end DsBatch.P08
