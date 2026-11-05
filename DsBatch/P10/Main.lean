import DsBatch.P10.Proof
import DsBatch.P10.Statement

/-! Proofs for project P10 (arXiv 2609.38417).  The statements are in
    `DsBatch/P10/Statement.lean`, the mathematical argument in
    `DsBatch/P10/Proof.lean`, and this file connects the two. -/

namespace DsBatch.P10

/-- The paper's graph is a cubic graph on 20 vertices. -/
theorem graph_structure : graph_structure_statement :=
  ⟨card_V, cubic_G⟩

/-- The graph has total chromatic number 4: the explicit four-colouring of
Section 2 is proper, and a cubic graph admits no 3-total-colouring. -/
theorem total_colouring : total_colouring_statement :=
  ⟨⟨colour4, colour4_proper⟩, no_three_colouring⟩

/-- The assignment `Lstar` is a 4-list assignment with no proper list total
colouring. -/
theorem list_assignment : list_assignment_statement :=
  ⟨lists_card, not_list_total_colourable⟩

/-- The List Total Colouring Conjecture is false. -/
theorem counterexample : counterexample_statement :=
  ⟨graph_structure, total_colouring, list_assignment⟩

end DsBatch.P10
