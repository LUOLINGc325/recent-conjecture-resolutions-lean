import DsBatch.P07.Defs

/-! Frozen specification for project P07. This file must stay sorry-free:
    state each target as `def <name>_statement : Prop := <type>` here and put
    the proof-carrying `theorem` in Main.lean.

    Target (queue scope, required part, arXiv 2609.08137):

    1. `key31_statement` — Theorem key31 (`thm:key31`): for all `n, m ≥ 1`,
       `557 ∣ F n + F m ↔ 2417 ∣ F n + F m`.
    2. `counterexample_statement` — hence there is a multiplicative
       `f : ℕ → ℕ`, not the identity, with
       `f (F n + F m) = f (F n) + f (F m)` for all `n, m ≥ 1`, answering
       Spiro's question negatively. -/

namespace DsBatch.P07

/-- Theorem key31 (the paper's Theorem `thm:key31`): for every `n, m ≥ 1`,
`557` divides `F n + F m` if and only if `2417` does.  The two primes are the
prime factors of `F 31 = 1346269 = 557 * 2417`. -/
def key31_statement : Prop :=
  ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
    (557 ∣ F n + F m ↔ 2417 ∣ F n + F m)

/-- The negative answer to Spiro's 1992 question: there is a multiplicative
function `f : ℕ → ℕ`, not the identity, satisfying the Fibonacci additivity
condition `f (F n + F m) = f (F n) + f (F m)` for all `n, m ≥ 1`.  Thus the
positive Fibonacci numbers are not an additive uniqueness set. -/
def counterexample_statement : Prop :=
  ∃ f : ℕ → ℕ, IsMultiplicative f ∧ f ≠ id ∧
    ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → f (F n + F m) = f (F n) + f (F m)

/-! ## Non-vacuity checks

The explicit objects exist with the stated structure, and each defined property
is neither vacuous nor trivially true/false. -/

/-- `557` and `2417` are the two prime factors of `F 31`. -/
example : F 31 = 557 * 2417 := by decide

/-- Both primes are prime and distinct. -/
example : Nat.Prime 557 ∧ Nat.Prime 2417 ∧ (557 : ℕ) ≠ 2417 := by norm_num

/-- The divisibility of `key31_statement` is not vacuous: at `n = m = 31` both
primes divide the sum. -/
example : 557 ∣ F 31 + F 31 ∧ 2417 ∣ F 31 + F 31 := by decide

/-- The divisibility can fail: at `n = m = 1` neither prime divides the sum, so
`key31_statement` is not a statement about a condition that always holds. -/
example : ¬ (557 ∣ F 1 + F 1) ∧ ¬ (2417 ∣ F 1 + F 1) := by decide

/-- The multiplicativity predicate is not vacuous: the identity is
multiplicative. -/
example : IsMultiplicative (id : ℕ → ℕ) := by
  refine ⟨rfl, ?_⟩
  intro a b _
  simp

/-- Non-identity multiplicative functions exist, so `counterexample_statement`
is not trivially false: `n ↦ n ^ 2` is multiplicative and not the identity. -/
example : ∃ f : ℕ → ℕ, IsMultiplicative f ∧ f ≠ id := by
  refine ⟨fun n => n ^ 2, ⟨by simp, ?_⟩, ?_⟩
  · intro a b _
    ring
  · intro h
    have h2 := congrFun h 2
    norm_num at h2

/-- The additivity condition is consistent with multiplicativity: the identity
satisfies it. -/
example : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
    (id : ℕ → ℕ) (F n + F m) = id (F n) + id (F m) := by
  intro n m _ _
  rfl

/-- The explicit function `swapFibPrimes` swaps the two primes. -/
example : swapFibPrimes 557 = 2417 := by decide

/-- ... in the other direction. -/
example : swapFibPrimes 2417 = 557 := by decide

/-- It fixes numbers divisible by neither prime. -/
example : swapFibPrimes 6 = 6 := by decide

/-- It fixes numbers divisible by both primes. -/
example : swapFibPrimes (557 * 2417) = 557 * 2417 := by decide

/-- It sends `p` times a `p`-only multiple to `q` times the quotient:
`f (557 * 6) = 2417 * 6`. -/
example : swapFibPrimes (557 * 6) = 2417 * 6 := by decide

/-- It fixes `1`, as multiplicativity requires. -/
example : swapFibPrimes 1 = 1 := by decide

end DsBatch.P07
