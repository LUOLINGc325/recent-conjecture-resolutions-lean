import DsBatch.P08.Defs

/-! Frozen specification for project P08. This file must stay sorry-free:
    state each target as `def <name>_statement : Prop := <type>` here and put
    the proof-carrying `theorem` in Main.lean.

    Targets (queue scope, required part, arXiv 2609.28702):

    1. `no_comparable_closed_neighborhoods_statement` — the abstract's main
       result (paper Lemma 3.1 `lem:notruedompairs` and Theorem 3.2
       `thm:notruetwins`): in a nontrivial square-complementary graph no two
       distinct vertices have comparable closed neighbourhoods.
    2. `no_simplicial_vertex_statement` — the "hence" part of Theorem 3.2: a
       nontrivial square-complementary graph has no simplicial vertex. -/

namespace DsBatch.P08

open SimpleGraph

universe u

/-- **Main theorem** (paper: Lemma 3.1 and Theorem 3.2, see also the abstract):
in a nontrivial square-complementary graph `G` (i.e. `G² ≅ Ḡ` and `|V(G)| ≥ 2`)
no two distinct vertices `x ≠ y` have comparable closed neighbourhoods, that is
neither `N[x] ⊆ N[y]` nor `N[y] ⊆ N[x]` holds. -/
def no_comparable_closed_neighborhoods_statement : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    IsSquareComplementary G → IsNontrivialGraph G →
      ∀ x y : V, x ≠ y → ¬ (DominatedBy G x y ∨ DominatedBy G y x)

/-- **Corollary** (the "hence" part of the abstract and of Theorem 3.2): a
nontrivial square-complementary graph has no simplicial vertex, where a vertex
is simplicial when its closed neighbourhood induces a complete subgraph. -/
def no_simplicial_vertex_statement : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    IsSquareComplementary G → IsNontrivialGraph G →
      ∀ x : V, ¬ IsSimplicial G x

/-! ## Non-vacuity checks

The hypotheses are satisfiable and none of the defined properties is trivial:

* the cycle `C₇` is a nontrivial square-complementary graph (the smallest one);
* some graph (`K₂`) does have two distinct vertices with comparable closed
  neighbourhoods, and a simplicial vertex, so the theorem's conclusion is not a
  triviality true of every graph;
* `K₁` is square-complementary but not nontrivial, so the nontriviality
  hypothesis genuinely excludes it. -/

/-- Multiplication by `2` modulo `7` is a permutation of `Fin 7`; it is the
isomorphism `C₇² ≅ C̄₇` (edges at cyclic distance `1` or `2` are sent to edges at
cyclic distance `2` or `3`, which are exactly the complement's edges). -/
def sevenCycleEquiv : Fin 7 ≃ Fin 7 where
  toFun x := ⟨(2 * x.val) % 7, Nat.mod_lt _ (by norm_num)⟩
  invFun x := ⟨(4 * x.val) % 7, Nat.mod_lt _ (by norm_num)⟩
  left_inv x := by ext; fin_cases x <;> decide
  right_inv x := by ext; fin_cases x <;> decide

/-- `C₇` is square-complementary: `C₇² ≅ C̄₇`. -/
def sevenCycleIso : square (cycleGraph 7) ≃g (cycleGraph 7)ᶜ where
  toEquiv := sevenCycleEquiv
  map_rel_iff' := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide

/-- The explicit nontrivial square-complementary graph `C₇` exists, so the
theorem's hypotheses are satisfiable. -/
example : IsSquareComplementary (cycleGraph 7) := ⟨sevenCycleIso⟩

/-- `C₇` has seven vertices, hence is nontrivial. -/
example : IsNontrivialGraph (cycleGraph 7) := by simp [IsNontrivialGraph]

/-- In `C₇` the closed neighbourhoods of the adjacent vertices `0` and `1` are
incomparable, as the theorem asserts: `6 ∈ N[0]` but `6 ∉ N[1]`. -/
example : ¬ DominatedBy (cycleGraph 7) 0 1 := by
  intro h
  have h6 : (6 : Fin 7) ∈ closedNhd (cycleGraph 7) 0 := by
    rw [closedNhd, Set.mem_union, Set.mem_singleton_iff, mem_neighborSet]
    right
    decide
  have h' := h h6
  rw [closedNhd, Set.mem_union, Set.mem_singleton_iff, mem_neighborSet] at h'
  rcases h' with h' | h'
  · exact absurd h' (by decide)
  · exact absurd h' (by decide)

/-- The conclusion is not trivially true of every graph: the two vertices of
`K₂` have equal (hence comparable) closed neighbourhoods. -/
example : DominatedBy (⊤ : SimpleGraph (Fin 2)) 0 1 := by
  intro z hz
  simp only [closedNhd, Set.mem_union, Set.mem_singleton_iff, mem_neighborSet,
    top_adj] at hz ⊢
  tauto

/-- The property "simplicial vertex" is not always false: both vertices of `K₂`
are simplicial. -/
example : IsSimplicial (⊤ : SimpleGraph (Fin 2)) 0 := by
  intro x hx y hy hxy
  simp only [closedNhd, Set.mem_union, Set.mem_singleton_iff, mem_neighborSet] at hx hy
  simp only [top_adj]
  exact hxy

/-- The trivial one-vertex graph is square-complementary ... -/
example : IsSquareComplementary (⊥ : SimpleGraph (Fin 1)) := by
  refine ⟨{ toEquiv := Equiv.refl (Fin 1), map_rel_iff' := ?_ }⟩
  intro x y
  fin_cases x
  fin_cases y
  simp [square]

/-- ... but not nontrivial, so the nontriviality hypothesis is not redundant. -/
example : ¬ IsNontrivialGraph (⊥ : SimpleGraph (Fin 1)) := by simp [IsNontrivialGraph]

end DsBatch.P08
