import DsBatch.P15.Defs

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Frozen specification for project P15. This file must stay sorry-free:
    state each target as `def <name>_statement : Prop := <type>` here and put
    the proof-carrying `theorem` in Main.lean. -/

namespace DsBatch.P15

/-- The paper's caterpillar `T₃ = Cat(8,7,25)`: the path `a–b–c = vA–vB–vC`
with 8, 7 and 25 pendant leaves attached to `a`, `b` and `c` respectively.
It has 43 vertices, 42 edges and 40 leaves, with degrees `d(a) = d(b) = 9`
and `d(c) = 26`. -/
def t3_caterpillar_statement : Prop :=
  IsCaterpillar T3 ∧ Fintype.card V3 = 43 ∧ Fintype.card T3.edgeSet = 42 ∧
    leafCount T3 = 40 ∧ T3.degree vA = 9 ∧ T3.degree vB = 9 ∧ T3.degree vC = 26

/-- Every local antimagic bijection `E(T₃) → {1,…,42}` induces 43 distinct
vertex weights, i.e. all induced weights are pairwise distinct.  (This is the
consequence of the separation criterion used in the proof of Theorem 4.1; it
implies `χ_la(T₃) = 43`.) -/
def t3_weight_separation_statement : Prop :=
  ∀ L : Labeling T3, IsLocalAntimagic T3 L → (weightImage T3 L).card = 43

/-- Theorem 4.1 of the paper: `χ_la(T₃) = 43 = ℓ(T₃) + 3`. -/
def t3_chiLa_statement : Prop :=
  chiLa T3 = 43 ∧ chiLa T3 = leafCount T3 + 3

/-- The leaf conjecture (Conjecture 2.2) is false. -/
def leaf_conjecture_false_statement : Prop :=
  ¬ LeafConjecture

/-! ### Non-vacuity checks

The definitions are exercised on the paper's concrete caterpillar `T₃`. -/

example : Fintype.card V3 = 43 := by decide

example : Fintype.card T3.edgeSet = 42 := by decide

example : leafCount T3 = 40 := by decide

example : T3.degree vA = 9 := by decide

example : T3.degree vB = 9 := by decide

example : T3.degree vC = 26 := by decide

/-- The hypothesis of `t3_weight_separation_statement` is satisfiable: the
paper's explicit labelling `t3Labeling` is local antimagic. -/
example : ∃ L : Labeling T3, IsLocalAntimagic T3 L :=
  ⟨t3Labeling, t3Labeling_isLocalAntimagic⟩

end DsBatch.P15
