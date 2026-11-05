import DsBatch.P01.Defs

/-! Frozen specification for project P01. This file must stay sorry-free:
    state each target as `def <name>_statement : Prop := <type>` here and put
    the proof-carrying `theorem` in Main.lean. -/

namespace DsBatch.P01

/-- The paper's main theorem (Theorem 1): the explicit ten-vertex graph `G` is connected and
nontrivially unstable (indeed vertex-determining), and there is no odd `k` for which `G`
contains both `C_k` and `C_{2k}`. -/
def counterexample_statement : Prop :=
  G.Connected ∧ VertexDetermining G ∧ IsNontriviallyUnstable G ∧ ¬ ContainsOddDoubleCycle G

/-- The conjecture as stated in the paper is false: Mizzi conjectured that every nontrivially
unstable graph contains `C_k` and `C_{2k}` for some odd `k`. -/
def mizzi_conjecture_false_statement : Prop :=
  ¬ MizziConjecture

/-! ## Non-vacuity checks

`G` is a genuine unstable graph: the paper's explicit permutations `α = (1 6)` and `β = (2 3)`
form a nontrivial two-fold automorphism.  `HasCycleOfLength` is neither empty nor universal:
`G` has a 5-cycle and a 6-cycle, while the edgeless graph has no 3-cycle. -/

example : IsTwoFoldAutomorphism G alpha beta := by
  unfold IsTwoFoldAutomorphism
  decide

example : alpha ≠ beta := by decide

example : IsUnstable G :=
  ⟨alpha, beta, by decide, by unfold IsTwoFoldAutomorphism; decide⟩

/-- The 5-cycle `1, 2, 4, 5, 10, 1` (indices `0, 1, 3, 4, 9, 0`). -/
example : HasCycleOfLength G 5 := by
  unfold HasCycleOfLength
  refine ⟨by norm_num, (![0, 1, 3, 4, 9] : Fin 5 → V), by decide, ?_⟩
  decide

/-- The 6-cycle `1, 2, 4, 3, 6, 10, 1` (indices `0, 1, 3, 2, 5, 9, 0`). -/
example : HasCycleOfLength G 6 := by
  unfold HasCycleOfLength
  refine ⟨by norm_num, (![0, 1, 3, 2, 5, 9] : Fin 6 → V), by decide, ?_⟩
  decide

/-- The cycle-length predicate is not trivially true. -/
example : ¬ HasCycleOfLength (⊥ : SimpleGraph (Fin 3)) 3 := by
  unfold HasCycleOfLength
  decide

end DsBatch.P01
