import Mathlib

/-!
# P06: A diamond-free claw-free cubic graph with strong chromatic index 7
(arXiv 2607.23462)

Formal objects from K. R. Tanwar, *A diamond-free claw-free cubic graph with strong
chromatic index 7*.

The paper builds an explicit graph `H` on 18 vertices as follows.  The nine-vertex
**gadget** `Q` consists of three vertex-disjoint triangles

`A = a₀a₁a₂`, `B = b₀b₁b₂`, `C = c₀c₁c₂`

together with the four connecting edges `a₀b₀`, `a₁c₀`, `b₁c₁`, `b₂c₂`.  Every vertex of
`Q` has degree `3` except `a₂`, which has degree `2`.  The graph `H` consists of two
disjoint copies `Q₁`, `Q₂` of `Q` joined by the single bridge `a₂⁽¹⁾a₂⁽²⁾`.

A **strong edge colouring** is a colouring of the edges in which any two edges that are
adjacent or joined by an edge receive distinct colours.  Two distinct edges `uv` and `xy`
are in conflict when they share an endpoint (`u = x`, `u = y`, `v = x` or `v = y`) or when
an endpoint of one is adjacent to an endpoint of the other.  The least number of colours
is the strong chromatic index `χ'_s`.
-/

namespace DsBatch.P06

/-- The 18 vertices of the paper's graph `H`: two copies of the nine-vertex gadget `Q`.
The primed constructors are the vertices of the second copy `Q₂`. -/
inductive V where
  | a0 | a1 | a2 | b0 | b1 | b2 | c0 | c1 | c2
  | a0' | a1' | a2' | b0' | b1' | b2' | c0' | c1' | c2'
  deriving DecidableEq, Repr

open V

instance : Fintype V where
  elems := ⟨[a0, a1, a2, b0, b1, b2, c0, c1, c2,
    a0', a1', a2', b0', b1', b2', c0', c1', c2'], by decide⟩
  complete := fun x => by cases x <;> decide

/-- The thirteen edges of the gadget `Q` (Construction 3) inside the first copy: the
triangles `A`, `B`, `C` and the four connecting edges `a₀b₀`, `a₁c₀`, `b₁c₁`, `b₂c₂`. -/
def Q₁edges : List (V × V) :=
  [(a0, a1), (a1, a2), (a2, a0),
   (b0, b1), (b1, b2), (b2, b0),
   (c0, c1), (c1, c2), (c2, c0),
   (a0, b0), (a1, c0), (b1, c1), (b2, c2)]

/-- The thirteen edges of the gadget `Q` inside the second copy. -/
def Q₂edges : List (V × V) :=
  [(a0', a1'), (a1', a2'), (a2', a0'),
   (b0', b1'), (b1', b2'), (b2', b0'),
   (c0', c1'), (c1', c2'), (c2', c0'),
   (a0', b0'), (a1', c0'), (b1', c1'), (b2', c2')]

/-- The 27 edges of `H` (Construction 4): two copies of `Q`, joined by the bridge
`a₂⁽¹⁾a₂⁽²⁾`. -/
def Hedges : List (V × V) := Q₁edges ++ Q₂edges ++ [(a2, a2')]

/-- The underlying edge relation of `H`: the pair is one of the 27 listed edges. -/
abbrev HedgesRel (u v : V) : Prop := (u, v) ∈ Hedges

instance : DecidableRel HedgesRel := fun _ _ => inferInstance

/-- The paper's graph `H` (Construction 4), as a simple graph on the 18 vertices `V`.
The relation is symmetrized by `SimpleGraph.fromRel`, so listing each edge once is
enough. -/
abbrev H : SimpleGraph V := SimpleGraph.fromRel HedgesRel

/-- The number of neighbours of `v` in `G`. -/
def degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter fun w => G.Adj v w).card

/-- `G` is **cubic**: every vertex has degree `3`. -/
def Cubic (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v, degree G v = 3

/-- `G` is **claw-free**: it has no induced `K_{1,3}`, i.e. no vertex has three
pairwise non-adjacent neighbours. -/
def ClawFree (G : SimpleGraph V) : Prop :=
  ∀ v x y z : V, G.Adj v x → G.Adj v y → G.Adj v z →
    x ≠ y → x ≠ z → y ≠ z → G.Adj x y ∨ G.Adj x z ∨ G.Adj y z

/-- `G` is **diamond-free**: it contains no `K₄ - e` as a subgraph, equivalently no edge
has two common neighbours (equivalently, no edge lies in two triangles). -/
def DiamondFree (G : SimpleGraph V) : Prop :=
  ∀ u v x y : V, G.Adj u v → G.Adj u x → G.Adj v x → G.Adj u y → G.Adj v y → x = y

/-- Two distinct edges `uv` and `xy` are in **conflict** when they share an endpoint or
an endpoint of one is adjacent to an endpoint of the other.  This is the adjacency
relation of the square `L(G)²` of the line graph: a strong edge colouring is exactly a
proper vertex colouring of `L(G)²`. -/
def EdgeConflict (G : SimpleGraph V) (u v x y : V) : Prop :=
  G.Adj u v ∧ G.Adj x y ∧
    ¬((u = x ∧ v = y) ∨ (u = y ∧ v = x)) ∧
    (u = x ∨ u = y ∨ v = x ∨ v = y ∨
      G.Adj u x ∨ G.Adj u y ∨ G.Adj v x ∨ G.Adj v y)

/-- `G` has a **strong `k`-edge-colouring**: an assignment of one of `k` colours to
every unordered pair of vertices, symmetric in its two arguments, such that conflicting
edges receive distinct colours.  Values on non-edges are irrelevant, so this is
equivalent to colouring the edges of `G`; symmetry makes the colour of `{u,v}`
well defined. -/
def StrongEdgeColoring (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → V → Fin k,
    (∀ u v, c u v = c v u) ∧
      ∀ u v x y, EdgeConflict G u v x y → c u v ≠ c x y

end DsBatch.P06
