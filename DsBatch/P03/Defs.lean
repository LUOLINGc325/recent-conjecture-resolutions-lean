import Mathlib

/-!
# P03: Associahedra are 12-colourable (arXiv 2611.05323)

This file sets up the objects of the paper.

The paper (Jane Tan, *Associahedra are 12-colourable*) works with the associahedron
`A_n` in its standard rooted-binary-tree model: the vertices are the ordered full
binary trees with `n - 1` leaves (equivalently `n - 2` internal vertices), and two
trees are adjacent when they are related by one tree rotation (associativity).
The paper notes that this graph is the flip graph of triangulations of a convex
`n`-gon; we use the tree model, which is the model used for the proof in the paper.

A tree is `leaf` or `node l r` (left and right subtrees).

Following the paper:

* `lab T` is the root label in `ZMod 3`, with leaves labelled `0` and a node
  labelled `1 - a - b` when its children have labels `a`, `b`;
* a left edge is *highlighted* when its endpoints have equal labels; `f T` is the
  parity of the number of highlighted left edges;
* highlighted edges form paths; `dAux T k e` computes the parity of the number of
  highlighted left edges whose upper endpoint has even path depth, where `e` says
  whether the root is joined to its parent by a highlighted edge and `k` is the
  parity of the parent's path depth; `d T = dAux T 0 false`;
* `kappa T = (lab T, f T, d T)` takes values in `ZMod 3 × ZMod 2 × ZMod 2`, a
  twelve-element colour set.
-/

namespace DsBatch.P03

/-- Ordered full binary trees: a leaf, or a node with a left and a right subtree. -/
inductive OBT : Type
  | leaf : OBT
  | node : OBT → OBT → OBT
  deriving DecidableEq, Repr

namespace OBT

/-- The number of leaves of an ordered full binary tree. -/
def numLeaves : OBT → ℕ
  | leaf => 1
  | node l r => numLeaves l + numLeaves r

lemma numLeaves_pos : ∀ T : OBT, 1 ≤ numLeaves T
  | leaf => le_rfl
  | node l r => by
      have hl := numLeaves_pos l
      have hr := numLeaves_pos r
      simp only [numLeaves]
      omega

/-- The paper's vertex label in `ZMod 3`: leaves get `0`, and a node whose children
have labels `a`, `b` gets `1 - a - b`. -/
def lab : OBT → ZMod 3
  | leaf => 0
  | node l r => 1 - lab l - lab r

/-- Parity of the number of highlighted left edges (edges whose endpoints have the
same label). -/
def f : OBT → ZMod 2
  | leaf => 0
  | node l r => f l + f r + (if lab l = lab (node l r) then 1 else 0)

/-- Auxiliary path-depth statistic.  `k` is the parity of the path depth of the
parent, and `e` says whether the edge from the parent to the current root is
highlighted; the path depth of the root is `k + 1` in that case and `0` otherwise.
The value is the parity of the number of highlighted left edges whose upper
endpoint has even path depth. -/
def dAux : OBT → ZMod 2 → Bool → ZMod 2
  | leaf, _, _ => 0
  | node l r, k, e =>
      let p := lab (node l r)
      let k' := if e then k + 1 else 0
      let eL : Bool := lab l = p
      let eR : Bool := lab r = p
      dAux l k' eL + dAux r k' eR + (if eL ∧ k' = 0 then 1 else 0)

/-- The paper's `d(T)`: parity of highlighted left edges whose upper endpoint has
even path depth, for the highlighted paths read from the root. -/
def d (T : OBT) : ZMod 2 := dAux T 0 false

/-- The paper's product colouring `κ(T) = (ℓ(T), f(T), d(T))`, with values in the
twelve-element set `ZMod 3 × ZMod 2 × ZMod 2`. -/
def kappa (T : OBT) : ZMod 3 × ZMod 2 × ZMod 2 := (lab T, f T, d T)

/-- A one-hole context: the hole can be filled by a tree to build a larger tree. -/
inductive Ctx : Type
  | hole : Ctx
  | left : Ctx → OBT → Ctx
  | right : OBT → Ctx → Ctx
  deriving DecidableEq

/-- Fill the hole of a context with a tree. -/
def Ctx.fill : Ctx → OBT → OBT
  | Ctx.hole, T => T
  | Ctx.left C X, T => node (C.fill T) X
  | Ctx.right X C, T => node X (C.fill T)

/-- Filling a context is injective in the filled tree. -/
lemma Ctx.fill_inj : ∀ (C : Ctx) (A B : OBT), C.fill A = C.fill B → A = B
  | Ctx.hole, _, _, h => h
  | Ctx.left C X, A, B, h => by
      have h' : C.fill A = C.fill B := by
        exact (OBT.node.inj h).1
      exact Ctx.fill_inj C A B h'
  | Ctx.right X C, A, B, h => by
      have h' : C.fill A = C.fill B := by
        exact (OBT.node.inj h).2
      exact Ctx.fill_inj C A B h'

/-- `node (node U V) W` and `node U (node V W)` are different trees (a rotation is
not a no-op). -/
lemma node_node_ne (U V W : OBT) : node (node U V) W ≠ node U (node V W) := by
  intro h
  have h1 : node U V = U := (OBT.node.inj h).1
  have h2 := congrArg numLeaves h1
  simp only [numLeaves] at h2
  have := numLeaves_pos V
  omega

/-- One forward tree rotation, at an arbitrary position: a subtree
`((U,V),W)` is replaced by `(U,(V,W))`. -/
def RotFwd (T T' : OBT) : Prop :=
  ∃ (C : Ctx) (U V W : OBT),
    T = C.fill (node (node U V) W) ∧ T' = C.fill (node U (node V W))

/-- The tree-rotation relation (either direction of associativity). -/
def Rot (T T' : OBT) : Prop := RotFwd T T' ∨ RotFwd T' T

lemma rot_symm : Std.Symm Rot := ⟨fun _ _ h => h.symm⟩

lemma rot_fwd_irrefl : ∀ T : OBT, ¬ RotFwd T T := by
  rintro T ⟨C, U, V, W, h1, h2⟩
  have hfill : C.fill (node (node U V) W) = C.fill (node U (node V W)) := by
    rw [← h1, h2]
  exact node_node_ne U V W (Ctx.fill_inj C _ _ hfill)

lemma rot_irrefl : ∀ T : OBT, ¬ Rot T T := by
  intro T h
  rcases h with h | h
  · exact rot_fwd_irrefl T h
  · exact rot_fwd_irrefl T h

/-- The associahedron `A_n`, in the paper's tree model: vertices are ordered full
binary trees with `n - 1` leaves (so `n - 2` internal vertices), and two vertices
are adjacent when they differ by a tree rotation. -/
def associahedron (n : ℕ) : SimpleGraph {T : OBT // numLeaves T = n - 1} where
  Adj T T' := Rot T.1 T'.1
  symm := ⟨fun _ _ h => rot_symm.symm _ _ h⟩
  loopless := ⟨fun T => rot_irrefl T.1⟩

end OBT

end DsBatch.P03
