import DsBatch.P14.Basic
import DsBatch.P14.Counting
import DsBatch.P14.Claim
import DsBatch.P14.Statement
import DsBatch.P14.Proof

/-! Root module for project P14: imports the proof development and states the
    frozen target `DsBatch.P14.main`. -/

namespace DsBatch.P14

/-- **Theorem main** (Theorem `thMain` of arXiv 2610.03151, attributed there to
the Mousavi–Poozesh–Zamani conjecture in the case `K = G`): for every finite
group `G`, every `x : G` and every subgroup `K ≤ G`, the order of
`N_G(x) ∩ K` divides the order of `Sol_G(x) ∩ K`. -/
theorem main : main_statement := by
  intro G _ _ x K
  exact main_of_finite (G := G) x K

end DsBatch.P14
