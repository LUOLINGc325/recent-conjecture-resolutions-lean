import DsBatch.P13.Statement

/-!
# P13 — Proofs

Proofs of the frozen targets in `Statement.lean`.  Every target is a finite
check on the explicit objects of `Defs.lean`, discharged in the kernel by
`decide`; `l12_structure` and `l12_nonequitable_colouring` are direct
computations on `L_12`, and `stemock_conjecture_false` instantiates the
universal conjecture at `L_12` and the explicit non-equitable colouring
`colour12`.
-/

namespace DsBatch.P13

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- `L_12` has 12 vertices and 18 edges and is cubic. -/
theorem l12_structure : l12_structure_statement := by
  unfold l12_structure_statement Cubic SimpleGraph.IsRegularOfDegree
  decide

/-- `L_12` admits a proper 4-total colouring with colour class configuration
`(8,8,8,6)`, which is non-equitable. -/
theorem l12_nonequitable_colouring : l12_nonequitable_colouring_statement := by
  unfold l12_nonequitable_colouring_statement
  exact ⟨colour12, by decide, by decide, by decide⟩

/-- Stemock's conjecture is false: `L_12` is a cubic graph of order `12 < 20`
with a non-equitable 4-total colouring. -/
theorem stemock_conjecture_false : stemock_conjecture_false_statement := by
  unfold stemock_conjecture_false_statement
  intro h
  exact (by decide : NonEquitable L12 colour12)
    (h V12 L12 (by decide)
      (by unfold Cubic SimpleGraph.IsRegularOfDegree; decide)
      colour12 (by decide))

end DsBatch.P13
