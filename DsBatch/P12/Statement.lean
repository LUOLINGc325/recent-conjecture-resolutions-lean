import DsBatch.P12.Defs

/-! Frozen specification for project P12. This file must stay sorry-free:
    state each target as `def <name>_statement : Prop := <type>` here and put
    the proof-carrying `theorem` in Main.lean.

    Targets (queue scope, required part, arXiv 2610.34808):

    1. `master_formula_statement` — Proposition 3.5 (Master formula): for every
       odd prime `p ≠ 3` and every `s ≥ 1`,
       `X_{2p^s} = {2p^s+1, 2(2p^s+1)}` if `2p^s+1` is prime, and
       `X_{2p^s} = ∅` otherwise.
    2. `even_statement` — Theorem 3.7 (even): for `p` an odd prime with `p ≠ 3`
       and `s` an even positive integer, `X_{2p^s} = ∅`.
    3. `odd_statement` — Theorem 3.8 (odd): for `p` an odd prime with `p ≠ 3`
       and `s` an odd positive integer, `X_{2p^s} = {2p^s+1, 2(2p^s+1)}` if
       `2p^s+1` is prime, and `X_{2p^s} = ∅` otherwise. -/

namespace DsBatch.P12

/-- **Proposition 3.5 (Master formula).**  For every odd prime `p ≠ 3` and
every integer `s ≥ 1`,
`X_{2p^s} = {2p^s+1, 2(2p^s+1)}` if `2p^s+1` is prime, and `X_{2p^s} = ∅`
if `2p^s+1` is not prime. -/
def master_formula_statement : Prop :=
  ∀ p s : ℕ, Nat.Prime p → Odd p → p ≠ 3 → 1 ≤ s →
    (Nat.Prime (2 * p ^ s + 1) →
        X (2 * p ^ s) = ({2 * p ^ s + 1, 2 * (2 * p ^ s + 1)} : Set ℕ)) ∧
    (¬ Nat.Prime (2 * p ^ s + 1) → X (2 * p ^ s) = ∅)

/-- **Theorem 3.7 (even).**  Let `p` be an odd prime with `p ≠ 3` and let `s` be
an even positive integer.  Then `X_{2p^s} = ∅`. -/
def even_statement : Prop :=
  ∀ p s : ℕ, Nat.Prime p → Odd p → p ≠ 3 → 0 < s → Even s → X (2 * p ^ s) = ∅

/-- **Theorem 3.8 (odd).**  Let `p` be an odd prime with `p ≠ 3` and let `s` be
an odd positive integer.  If `2p^s+1` is prime then
`X_{2p^s} = {2p^s+1, 2(2p^s+1)}`; otherwise `X_{2p^s} = ∅`. -/
def odd_statement : Prop :=
  ∀ p s : ℕ, Nat.Prime p → Odd p → p ≠ 3 → 0 < s → Odd s →
    (Nat.Prime (2 * p ^ s + 1) →
        X (2 * p ^ s) = ({2 * p ^ s + 1, 2 * (2 * p ^ s + 1)} : Set ℕ)) ∧
    (¬ Nat.Prime (2 * p ^ s + 1) → X (2 * p ^ s) = ∅)

/-! ## Non-vacuity checks

The hypotheses are satisfiable, the objects are the paper's, and each statement
is neither trivially true nor trivially false.  In particular the hypothesis
`p ≠ 3` is essential: at `p = 3`, `s = 1` the value `9` is a solution of
`φ(n) = 6` that is not one of the two values predicted by the master formula. -/

/-- The hypothesis "`p` is an odd prime, `p ≠ 3`" is satisfiable. -/
example : Nat.Prime 5 ∧ Odd 5 ∧ (5 : ℕ) ≠ 3 := by
  norm_num

/-- The definitional candidate `q_1 = 2p+1` of §3 at `p = 5`. -/
example : qCandidate 5 1 = 11 := by
  norm_num [qCandidate]

/-- The predicted solution set is nonempty in the prime case: `11` and `22` are
both solutions of `φ(n) = 10` (the case `p = 5`, `s = 1` of the master
formula). -/
example : (11 : ℕ) ∈ X 10 ∧ (22 : ℕ) ∈ X 10 := by
  constructor <;>
    · simp only [X, Set.mem_ofPred_eq]
      decide

/-- Both branches of the master formula genuinely occur for prime `p ≠ 3`:
`2·5+1 = 11` is prime while `2·7+1 = 15` is not. -/
example : Nat.Prime (2 * 5 ^ 1 + 1) ∧ ¬ Nat.Prime (2 * 7 ^ 1 + 1) := by
  norm_num

/-- The hypothesis `p ≠ 3` is not redundant: `φ(9) = 6`, but `9` is neither
`2·3+1 = 7` nor `2·(2·3+1) = 14`, so the master formula would be false at
`p = 3`. -/
example : (9 : ℕ) ∈ X 6 ∧
    (9 : ℕ) ∉ ({2 * 3 ^ 1 + 1, 2 * (2 * 3 ^ 1 + 1)} : Set ℕ) := by
  constructor
  · simp only [X, Set.mem_ofPred_eq]
    decide
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    decide

/-- The parity hypothesis in the even theorem is not redundant: at the odd
exponent `s = 1` (with `p = 5`) the set `X 10` is nonempty. -/
example : (11 : ℕ) ∈ X (2 * 5 ^ 1) ∧ ¬ Even (1 : ℕ) := by
  constructor
  · simp only [X, Set.mem_ofPred_eq]
    decide
  · decide

/-- An even positive exponent with the other hypotheses: `p = 5`, `s = 2`. -/
example : Nat.Prime 5 ∧ Odd 5 ∧ (5 : ℕ) ≠ 3 ∧ 0 < 2 ∧ Even 2 := by
  norm_num

end DsBatch.P12
