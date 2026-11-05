import DsBatch.P03.Defs

/-! Frozen specification for project P03. This file must stay sorry-free:
    state each target as `def <name>_statement : Prop := <type>` here and put
    the proof-carrying `theorem` in Main.lean. -/

namespace DsBatch.P03

open OBT

/-! ## Target statements -/

/-- Paper, Theorem 1 (the main theorem): the explicit product colouring
`κ(T) = (ℓ(T), f(T), d(T))` of a tree `T` into `ZMod 3 × ZMod 2 × ZMod 2` (twelve
colours) is a proper colouring of the associahedron `A_n` for every `n ≥ 3`.

Equivalently: for every `n ≥ 3`, the flip graph of triangulations of a convex
`n`-gon (in the paper's ordered-full-binary-tree model) has the proper 12-colouring
`κ`. -/
def kappa_proper_statement : Prop :=
  ∀ (n : ℕ), 3 ≤ n →
    ∀ (T T' : {T : OBT // numLeaves T = n - 1}),
      (associahedron n).Adj T T' → kappa T.1 ≠ kappa T'.1

/-- Paper, Theorem 1 as stated in the introduction: `χ(A_n) ≤ 12` for all `n ≥ 3`,
i.e. the chromatic number of the flip graph of triangulations of a convex `n`-gon is
bounded by `12` for every `n`. -/
def chromaticNumber_le_twelve_statement : Prop :=
  ∀ (n : ℕ), 3 ≤ n → (associahedron n).chromaticNumber ≤ 12

/-! ## Non-vacuity checks

The paper's objects exist, the hypotheses are satisfiable, and the statements are
not trivially true or false.
-/

/-- The colour set has exactly twelve elements. -/
example : Fintype.card (ZMod 3 × ZMod 2 × ZMod 2) = 12 := by decide

/-- For `n = 3` the associahedron has a vertex (a triangle has a unique
triangulation). -/
example : Nonempty {T : OBT // numLeaves T = 3 - 1} :=
  ⟨node leaf leaf, rfl⟩

/-- The two trees with three leaves, which are the two triangulations of a convex
quadrilateral. -/
def quadTreeA : OBT := node (node leaf leaf) leaf

def quadTreeB : OBT := node leaf (node leaf leaf)

/-- They are the two vertices of `A_4`. -/
example : numLeaves quadTreeA = 4 - 1 := rfl
example : numLeaves quadTreeB = 4 - 1 := rfl

/-- They are adjacent, related by a rotation at the root. -/
example : (associahedron 4).Adj ⟨quadTreeA, rfl⟩ ⟨quadTreeB, rfl⟩ :=
  Or.inl ⟨Ctx.hole, leaf, leaf, leaf, rfl, rfl⟩

/-- `κ` is not constant: the two adjacent triangulations of the quadrilateral get
different colours, so the properness statement is meaningful. -/
example : kappa quadTreeA ≠ kappa quadTreeB := by decide

/-- The statement is not about edgeless graphs: `A_4` has an edge, hence cannot be
properly coloured with one colour. -/
example : ¬ (associahedron 4).Colorable 1 := by
  rintro ⟨c⟩
  have h := c.valid (Or.inl ⟨Ctx.hole, leaf, leaf, leaf, rfl, rfl⟩ :
    (associahedron 4).Adj ⟨quadTreeA, rfl⟩ ⟨quadTreeB, rfl⟩)
  exact h (Subsingleton.elim _ _)

/-- The rotation relation is not vacuously empty: a rotation really changes the tree
and produces an associahedron edge. -/
example : RotFwd quadTreeA quadTreeB :=
  ⟨Ctx.hole, leaf, leaf, leaf, rfl, rfl⟩

/-- A rotation is not a no-op, so adjacency is not degenerate. -/
example : quadTreeA ≠ quadTreeB := by decide

end DsBatch.P03
