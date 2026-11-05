import Mathlib

/-!
# Project P01 — a ten-vertex counterexample to Mizzi's conjecture

arXiv:2608.15281, "A Ten-Vertex Counterexample to a Conjecture on Unstable Graphs".

This file contains the paper's objects and definitions.  Vertices `1, …, 10` of the paper are
represented by `Fin 10`, paper vertex `i` being `Fin 10` value `i - 1`.
-/

namespace DsBatch.P01

/-! ## The counterexample graph -/

/-- The vertex set of the paper's graph: `Fin 10` with value `i` standing for paper vertex `i + 1`. -/
abbrev V : Type := Fin 10

/-- The edge set of Theorem 1, `{12, 1·10, 24, 34, 36, 45, 57, 5·10, 6·10, 79, 8·10}`, with each
edge written in one orientation (`SimpleGraph.fromRel` symmetrizes it). -/
def edgeList : List (V × V) :=
  [(0, 1), (0, 9), (1, 3), (2, 3), (2, 5), (3, 4), (4, 6), (4, 9), (5, 9), (6, 8), (7, 9)]

/-- The graph `G` of the paper's Theorem 1. -/
def G : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => (u, v) ∈ edgeList

instance : DecidableRel G.Adj := fun u v =>
  decidable_of_iff (u ≠ v ∧ ((u, v) ∈ edgeList ∨ (v, u) ∈ edgeList))
    (SimpleGraph.fromRel_adj (fun u v => (u, v) ∈ edgeList) u v).symm

@[simp] theorem G_adj {u v : V} :
    G.Adj u v ↔ u ≠ v ∧ ((u, v) ∈ edgeList ∨ (v, u) ∈ edgeList) :=
  SimpleGraph.fromRel_adj (fun u v => (u, v) ∈ edgeList) u v

/-! ## Unstable graphs ([Lauri–Mizzi–Scapellato], as used in the paper) -/

section General

variable {W : Type*}

/-- A pair of permutations `(α, β)` of the vertex set is a *two-fold automorphism* of `G` when
`uv ∈ E(G) ↔ α(u)β(v) ∈ E(G)` for all vertices `u, v` (the paper's equation (1)). -/
def IsTwoFoldAutomorphism (G : SimpleGraph W) (α β : Equiv.Perm W) : Prop :=
  ∀ u v : W, G.Adj u v ↔ G.Adj (α u) (β v)

/-- A graph is *unstable* when it has a nontrivial (`α ≠ β`) two-fold automorphism. -/
def IsUnstable (G : SimpleGraph W) : Prop :=
  ∃ α β : Equiv.Perm W, α ≠ β ∧ IsTwoFoldAutomorphism G α β

/-- The two classes of graphs called *trivially unstable*: disconnected graphs and bipartite
graphs (paper, Verification: "the paper's exclusions of the two classes called trivially
unstable"). -/
def IsTriviallyUnstable (G : SimpleGraph W) : Prop :=
  ¬ G.Connected ∨ G.IsBipartite

/-- A graph is *nontrivially unstable* when it is unstable without being trivially unstable,
i.e. it is unstable, connected and non-bipartite. -/
def IsNontriviallyUnstable (G : SimpleGraph W) : Prop :=
  IsUnstable G ∧ ¬ IsTriviallyUnstable G

/-- A graph is *vertex-determining* when no two distinct vertices have the same open
neighbourhood. -/
def VertexDetermining (G : SimpleGraph W) : Prop :=
  Function.Injective G.neighborSet

/-- `G` contains a copy of the cycle `C_k` on `k ≥ 3` vertices: the Mathlib cycle graph
`SimpleGraph.cycleGraph k` embeds into `G`. -/
def HasCycleOfLength (G : SimpleGraph W) (k : ℕ) : Prop :=
  3 ≤ k ∧ ∃ f : Fin k → W, Function.Injective f ∧
    ∀ i j : Fin k, (SimpleGraph.cycleGraph k).Adj i j → G.Adj (f i) (f j)

/-- `G` contains both `C_k` and `C_{2k}` for some odd `k`. -/
def ContainsOddDoubleCycle (G : SimpleGraph W) : Prop :=
  ∃ k : ℕ, Odd k ∧ HasCycleOfLength G k ∧ HasCycleOfLength G (2 * k)

end General

/-- Mizzi's conjecture on unstable graphs, as stated in the paper: every nontrivially unstable
graph contains `C_k` and `C_{2k}` for some odd `k`. -/
def MizziConjecture : Prop :=
  ∀ (W : Type) [Fintype W], ∀ G : SimpleGraph W,
    IsNontriviallyUnstable G → ContainsOddDoubleCycle G

/-! ## The explicit permutations of the paper -/

/-- The paper's permutation `α = (1 6)`. -/
def alpha : Equiv.Perm V := Equiv.swap 0 5

/-- The paper's permutation `β = (2 3)`. -/
def beta : Equiv.Perm V := Equiv.swap 1 2

end DsBatch.P01
