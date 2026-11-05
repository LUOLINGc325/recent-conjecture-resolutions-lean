import Mathlib

/-!
# P07: The Fibonacci numbers are not an additive uniqueness set
(arXiv 2609.08137)

Formal objects from Poo-Sung Park, *The Fibonacci numbers are not an additive
uniqueness set for multiplicative functions*.

A set `E` of positive integers is an **additive uniqueness set** for the class
of multiplicative functions when the single condition `f (a + b) = f a + f b`
for all `a, b ∈ E` forces `f` to be the identity.  The paper answers negatively
for the set of Fibonacci numbers: the two prime factors `p = 557` and
`q = 2417` of `F 31 = 1346269 = 557 * 2417` have the same divisibility
behaviour on every Fibonacci number and every sum of two Fibonacci numbers, so
their multiplicative contributions can be exchanged.

Throughout, `F n` denotes the `n`-th Fibonacci number with `F 0 = 0`,
`F 1 = 1` (Mathlib's `Nat.fib`).
-/

namespace DsBatch.P07

/-- The smaller prime factor of `F 31`. -/
def p : ℕ := 557

/-- The larger prime factor of `F 31`. -/
def q : ℕ := 2417

/-- The `n`-th Fibonacci number, with `F 0 = 0` and `F 1 = 1`. -/
abbrev F (n : ℕ) : ℕ := Nat.fib n

/-- A function `f : ℕ → ℕ` is **multiplicative** in the sense of the paper
(Spiro 1992, Park): `f 1 = 1` and `f (a * b) = f a * f b` whenever `a` and `b`
are coprime. -/
def IsMultiplicative (f : ℕ → ℕ) : Prop :=
  f 1 = 1 ∧ ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b

/-- The explicit function of the paper (equation (2.1)), which swaps the
multiplicative contributions of the primes `p = 557` and `q = 2417`:
`f N = N * (q / p) ^ (1_{p ∣ N} - 1_{q ∣ N})`.  Written directly in `ℕ`, this
is the case analysis

* `f N = N`          if `p ∣ N` and `q ∣ N`, or if neither divides `N`;
* `f N = q * (N / p)` if `p ∣ N` and `q ∤ N`;
* `f N = p * (N / q)` if `q ∣ N` and `p ∤ N`. -/
def swapFibPrimes (N : ℕ) : ℕ :=
  if p ∣ N then (if q ∣ N then N else q * (N / p))
  else (if q ∣ N then p * (N / q) else N)

end DsBatch.P07
