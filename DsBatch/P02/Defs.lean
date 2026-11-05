import Mathlib

/-!
# Project P02 — the Partial List Colouring Conjecture is false

arXiv:2609.23291, "The Partial List Colouring Conjecture is False" (Jonathan A. Noel).

The paper constructs a 14-vertex graph `G` and a 2-list assignment `L` such that at most `9`
vertices of `G` can be properly coloured from `L`, while `G` has list chromatic number `3`.
Since `9 < 14 · (2/3)`, this refutes the Partial List Colouring Conjecture of Albertson,
Grossman and Haas: for every graph with `n` vertices and list chromatic number `k ≥ 2`, every
`ℓ`-list assignment (`1 ≤ ℓ < k`) should admit a proper partial colouring of at least `n·ℓ/k`
vertices.

The paper's colours `1, 2, 3, 4` are encoded here as `0, 1, 2, 3` (a harmless relabelling).

This file contains the paper's objects and the definitions of list colouring.  It is frozen
after the fidelity audit; `Statement.lean` holds the frozen propositions and `Main.lean` the
proofs.
-/

namespace DsBatch.P02

/-! ## The counterexample graph

The paper takes four pairwise disjoint triangles `T_1, …, T_4`; triangle `T_i` has a *private*
vertex `p_i` and two other (non-private) vertices.  Two non-adjacent terminals `s_1, s_2` are
adjacent to every non-private vertex of every triangle, and there are no further edges.
-/

/-- The 14 vertices of the paper's graph: the two terminals and the three vertices of each of
the four triangles.  Paper triangle `T_{i+1}` is `T i`; its private vertex is `p i` and its
non-private vertices are `u i` and `v i`. -/
inductive V : Type
  | s1 : V
  | s2 : V
  | u : Fin 4 → V
  | v : Fin 4 → V
  | p : Fin 4 → V
  deriving DecidableEq, Fintype, Repr

/-- The adjacency relation of the paper's graph `G`, as a Boolean function.

* `s_1` and `s_2` are non-adjacent;
* both `s_1` and `s_2` are adjacent to `u i` and `v i` for every `i`;
* the private vertices `p i` are adjacent to no terminal;
* each `{u i, v i, p i}` is a triangle;
* there are no other edges. -/
def adjB : V → V → Bool
  | .s1, .s1 => false
  | .s1, .s2 => false
  | .s1, .u _ => true
  | .s1, .v _ => true
  | .s1, .p _ => false
  | .s2, .s1 => false
  | .s2, .s2 => false
  | .s2, .u _ => true
  | .s2, .v _ => true
  | .s2, .p _ => false
  | .u _, .s1 => true
  | .u _, .s2 => true
  | .u _, .u _ => false
  | .u i, .v j => decide (i = j)
  | .u i, .p j => decide (i = j)
  | .v _, .s1 => true
  | .v _, .s2 => true
  | .v i, .u j => decide (i = j)
  | .v _, .v _ => false
  | .v i, .p j => decide (i = j)
  | .p _, .s1 => false
  | .p _, .s2 => false
  | .p i, .u j => decide (i = j)
  | .p i, .v j => decide (i = j)
  | .p _, .p _ => false

/-- Adjacency of the paper's graph. -/
def AdjRel (a b : V) : Prop := adjB a b = true

instance : DecidableRel AdjRel := fun a b => by unfold AdjRel; infer_instance

/-- The paper's graph `G`. -/
def G : SimpleGraph V where
  Adj := AdjRel
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> simp_all [AdjRel, adjB]⟩
  loopless := ⟨by
    intro a
    cases a <;> simp [AdjRel, adjB]⟩

/-- Characterisation of adjacency in `G`. -/
@[simp] theorem G_adj {a b : V} : G.Adj a b ↔ adjB a b = true := Iff.rfl

/-- Computable decidability of adjacency in `G` (needed for concrete `decide` checks). -/
instance : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable (adjB a b = true))

/-! ## The triangles and the terminal pair -/

/-- The triangle `T_i` of the paper (paper `T_{i+1}`). -/
def T (i : Fin 4) : Finset V := {V.u i, V.v i, V.p i}

/-- The two terminals. -/
def terminals : Finset V := {V.s1, V.s2}

/-- The union of the four triangles. -/
def allTriangles : Finset V := (Finset.univ : Finset (Fin 4)).biUnion T

/-! ## The 2-list assignment of the paper -/

/-- The common list of the vertices of `T_i`.  In the paper's colours these are
`T_1 ↦ {1,3}`, `T_2 ↦ {1,4}`, `T_3 ↦ {2,3}`, `T_4 ↦ {2,4}`; with the encoding
`1,2,3,4 ↦ 0,1,2,3` this is `{0,2}, {0,3}, {1,2}, {1,3}`. -/
def listOf : Fin 4 → Finset ℕ
  | ⟨0, _⟩ => {0, 2}
  | ⟨1, _⟩ => {0, 3}
  | ⟨2, _⟩ => {1, 2}
  | _ => {1, 3}

/-- The paper's 2-list assignment `L`: `L(s_1) = {1,2}`, `L(s_2) = {3,4}` and every vertex of
`T_i` has the common list `listOf i`.  (Paper colours are encoded as `0,1,2,3`.) -/
def L : V → Finset ℕ
  | .s1 => {0, 1}
  | .s2 => {2, 3}
  | .u i => listOf i
  | .v i => listOf i
  | .p i => listOf i

/-! ## List colourings

All lists are finite sets of colours drawn from `ℕ`.  This is the usual setting for list
colouring: a `k`-list assignment gives every vertex a list of exactly `k` colours, and a proper
`L`-colouring assigns to each vertex a colour from its own list, with adjacent vertices getting
different colours.  A *partial* colouring colours only a subset `S` of the vertices. -/

section Colouring

variable {W : Type*}

/-- A partial proper list-colouring: `S` is the set of coloured vertices and `c v` is the
colour of `v`.  Every coloured vertex receives a colour from its own list, and adjacent
coloured vertices receive different colours. -/
def IsPartialListColoring (G : SimpleGraph W) (L : W → Finset ℕ) (S : Finset W)
    (c : W → ℕ) : Prop :=
  (∀ v ∈ S, c v ∈ L v) ∧ ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v

/-- A full proper list-colouring of `G` from the lists `L`. -/
def IsListColoring (G : SimpleGraph W) (L : W → Finset ℕ) (c : W → ℕ) : Prop :=
  (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

/-- `G` can be properly coloured from the lists `L`. -/
def ListColorable (G : SimpleGraph W) (L : W → Finset ℕ) : Prop :=
  ∃ c : W → ℕ, IsListColoring G L c

/-- `L` is a `k`-list assignment: every vertex has a list of exactly `k` colours. -/
def IsListAssignment (L : W → Finset ℕ) (k : ℕ) : Prop :=
  ∀ v, (L v).card = k

/-- `G` is `k`-choosable: from every `k`-list assignment `G` admits a proper list-colouring. -/
def Choosable (G : SimpleGraph W) (k : ℕ) : Prop :=
  ∀ L : W → Finset ℕ, IsListAssignment L k → ListColorable G L

/-- The list chromatic number of `G` is exactly `k`: `G` is `k`-choosable and, for every
`j < k`, is not `j`-choosable.  (This is the standard "least `k` such that `G` is
`k`-choosable" definition.) -/
def ListChromaticNumberEq (G : SimpleGraph W) (k : ℕ) : Prop :=
  Choosable G k ∧ ∀ j, j < k → ¬ Choosable G j

end Colouring

/-! ## The Partial List Colouring Conjecture

Albertson, Grossman and Haas conjectured: if `G` has `n` vertices and list chromatic number
`k ≥ 2`, then for every `ℓ` with `1 ≤ ℓ < k` and every `ℓ`-list assignment `L` of `G`, it is
possible to properly `L`-colour at least `n·ℓ/k` vertices.  The inequality
`Fintype.card W * ℓ ≤ k * S.card` is equivalent (as `k > 0`) to
`S.card ≥ Fintype.card W · ℓ / k`. -/

/-- The Partial List Colouring Conjecture of Albertson, Grossman and Haas (2000). -/
def PartialListColouringConjecture : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W], ∀ (G : SimpleGraph W),
    ∀ (k ℓ : ℕ), 2 ≤ k → 1 ≤ ℓ → ℓ < k → ListChromaticNumberEq G k →
      ∀ L : W → Finset ℕ, IsListAssignment L ℓ →
        ∃ (S : Finset W) (c : W → ℕ),
          IsPartialListColoring G L S c ∧ Fintype.card W * ℓ ≤ k * S.card

end DsBatch.P02
