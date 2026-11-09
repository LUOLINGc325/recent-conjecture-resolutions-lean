import Mathlib

/-!
# P12: The family `X_{qp^s}` for distinct primes `q, p`

(He, *The Family `X_{qp^s}` for Distinct Primes `q, p` in Connection with
Carmichael's Totient Conjecture*, arXiv:2610.34808)

For a positive integer `k` the paper writes

`X_k = { n ∈ ℕ : φ(n) = k }`

where `φ` is Euler's totient function (`Nat.totient` in Mathlib).  The family
studied here is `k = 2 p^s` with `p` an odd prime; the candidates that can occur
as prime factors of a solution are `q_j = 2 p^j + 1`.
-/

namespace DsBatch.P12

/-- `X k` is the set of natural numbers `n` with `φ(n) = k`, as in the paper:
`X_k = {n ∈ ℕ : φ(n) = k}`. -/
def X (k : ℕ) : Set ℕ := {n | Nat.totient n = k}

/-- The number `q_j = 2 p^j + 1` (`j ≥ 1`), the candidate prime factors of a
solution of `φ(n) = 2 p^s` singled out in Lemma 3.2 and Proposition 3.5. -/
def qCandidate (p j : ℕ) : ℕ := 2 * p ^ j + 1

end DsBatch.P12
