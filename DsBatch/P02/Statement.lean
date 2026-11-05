import DsBatch.P02.Defs

/-! Frozen specification for project P02. This file must stay sorry-free:
    state each target as `def <name>_statement : Prop := <type>` here and put
    the proof-carrying `theorem` in Main.lean. -/

namespace DsBatch.P02

/-- The paper's Theorem 1 (`th:main`) for the explicit 14-vertex graph `G` and the explicit
2-list assignment `L` of the paper:

* `G` has 14 vertices;
* the list chromatic number of `G` is exactly 3;
* `L` is a 2-list assignment of `G`;
* every partial proper `L`-colouring of `G` colours at most 9 vertices
  (i.e. at most 9 vertices of `G` can be properly coloured from `L`). -/
def counterexample_statement : Prop :=
  Fintype.card V = 14 ∧
  ListChromaticNumberEq G 3 ∧
  IsListAssignment L 2 ∧
  ∀ (S : Finset V) (c : V → ℕ), IsPartialListColoring G L S c → S.card ≤ 9

/-- The Partial List Colouring Conjecture of Albertson, Grossman and Haas (2000) is false.

The paper's corollary: `G` has `n = 14` vertices and list chromatic number `k = 3`, and the
2-list assignment `L` admits no partial proper colouring of more than `9` vertices; since
`9 < 28/3 = 14 · (2/3)`, the conjecture fails. -/
def plcc_false_statement : Prop :=
  ¬ PartialListColouringConjecture

/-! ## Non-vacuity checks

The explicit objects of the paper satisfy the hypotheses of the statement, and the predicates
involved are neither empty nor universal.
-/

/-- The graph has 14 vertices. -/
example : Fintype.card V = 14 := by decide

/-- `L` is a 2-list assignment. -/
example : IsListAssignment L 2 := by unfold IsListAssignment; decide

/-- Each `T i` is a triangle whose three vertices have the common list `listOf i`. -/
example : ∀ i : Fin 4, ∀ a ∈ T i, ∀ b ∈ T i, a ≠ b → G.Adj a b := by decide

example : ∀ i : Fin 4, ∀ a ∈ T i, L a = listOf i := by decide

/-- The terminals are the only vertices outside the four triangles. -/
example : ∀ v : V, v ∈ allTriangles ↔ v ≠ V.s1 ∧ v ≠ V.s2 := by decide

/-- The explicit partial colouring of `9` vertices (so the bound `9` is attained and the
statement "at most 9 vertices" is not vacuous).  Triangles are `T 0 = {2,3,4}`,
`T 1 = {5,6,7}`, `T 2 = {8,9,10}`, `T 3 = {11,12,13}`; the coloured vertices are
`s1, s2, p0, u1, p1, u2, p2, u3, v3`. -/
def S9 : Finset V := {V.s1, V.s2, V.p 0, V.u 1, V.p 1, V.u 2, V.p 2, V.u 3, V.v 3}

/-- The colours of the nine vertices above (paper colours: `s1 ↦ 1`, `s2 ↦ 3`, `p0 ↦ 1`,
`u1 ↦ 4`, `p1 ↦ 1`, `u2 ↦ 2`, `p2 ↦ 3`, `u3 ↦ 2`, `v3 ↦ 4`). -/
def c9 : V → ℕ
  | .s1 => 0
  | .s2 => 2
  | .p 0 => 0
  | .u 1 => 3
  | .p 1 => 0
  | .u 2 => 1
  | .p 2 => 2
  | .u 3 => 1
  | .v 3 => 3
  | _ => 0

example : S9.card = 9 := by decide

/-- A proper partial `L`-colouring of nine vertices exists. -/
example : IsPartialListColoring G L S9 c9 := by unfold IsPartialListColoring; decide

/-- `Choosable` is not vacuously false: the edgeless graph on two vertices is 1-choosable. -/
example : Choosable (⊥ : SimpleGraph (Fin 2)) 1 := by
  intro L hL
  have h1 : ∀ v : Fin 2, ∃ a : ℕ, L v = {a} := fun v => Finset.card_eq_one.mp (hL v)
  choose x hx using h1
  refine ⟨x, ?_, ?_⟩
  · intro v; rw [hx v]; simp
  · intro u v huv
    exact absurd huv (by simp)

/-- `Choosable` is not vacuously true: the complete graph on two vertices is not
1-choosable. -/
example : ¬ Choosable (⊤ : SimpleGraph (Fin 2)) 1 := by
  intro h
  have hL : IsListAssignment (fun _ : Fin 2 => ({0} : Finset ℕ)) 1 := by
    intro v; simp
  obtain ⟨c, hc, hproper⟩ := h (fun _ => {0}) hL
  have h0 : c 0 = 0 := by simpa using hc 0
  have h1 : c 1 = 0 := by simpa using hc 1
  exact hproper 0 1 (by simp) (by rw [h0, h1])

/-- `IsPartialListColoring` is not vacuously false and not vacuously true: the empty colouring
is allowed, and a vertex may not take a colour outside its list. -/
example : IsPartialListColoring G L ∅ (fun _ => 0) := by
  refine ⟨?_, ?_⟩
  · intro v hv; simp at hv
  · intro u hu; simp at hu

example : ¬ IsPartialListColoring G L {V.s1} (fun _ => 2) := by
  unfold IsPartialListColoring; decide

end DsBatch.P02
