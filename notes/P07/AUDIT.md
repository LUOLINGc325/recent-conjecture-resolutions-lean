PASS

# Fidelity audit — P07 (arXiv 2609.08137, Spiro's Fibonacci AU question)

Verdict: PASS. The frozen files are faithful to the queue scope, the proofs
are sound, and the numerical certificates were independently re-verified.
Build is green (`lake build DsBatch`, 9069 jobs, no errors).

## 1. Definitional fidelity

- `F n := Nat.fib n` (`DsBatch/P07/Defs.lean`). Mathlib's `Nat.fib` has
  `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib (n+1) + fib n` — exactly the
  paper's normalization. Confirmed indirectly by `example : F 31 = 557 * 2417`
  and `F 1 = 1` usage compiling.
- `IsMultiplicative f := f 1 = 1 ∧ ∀ a b, Nat.Coprime a b → f (a*b) = f a * f b`.
  `Nat.Coprime a b` is `Nat.gcd a b = 1`, matching the paper's
  "f(1)=1 and f(ab)=f(a)f(b) whenever gcd(a,b)=1". No weakening, no extra
  hypotheses.
- `p = 557`, `q = 2417`. Correct.
- `swapFibPrimes N := if p ∣ N then (if q ∣ N then N else q * (N / p))
  else (if q ∣ N then p * (N / q) else N)`. This is exactly the paper's
  equation (2.1) `f(N) = N (q/p)^{1_{p|N} - 1_{q|N}}`:
  p|N,q∤N ↦ q·(N/p); q|N,p∤N ↦ p·(N/q); otherwise N. The Nat-division form is
  well-defined precisely because p∣N (resp. q∣N) in the two nontrivial cases.
- No vacuous/degenerate definitions, no Prop-encoded data. `IsMultiplicative`
  is a plain predicate (appropriate); `counterexample_statement` is a genuine
  existential over `ℕ → ℕ` functions.

## 2. Statement fidelity

- `key31_statement := ∀ n m, 1 ≤ n → 1 ≤ m → (557 ∣ F n + F m ↔ 2417 ∣ F n + F m)`.
  Matches the queue scope exactly: quantifiers n,m ≥ 1, correct iff direction.
- `counterexample_statement := ∃ f : ℕ → ℕ, IsMultiplicative f ∧ f ≠ id ∧
  ∀ n m, 1 ≤ n → 1 ≤ m → f (F n + F m) = f (F n) + f (F m)`. Matches the queue
  scope exactly: "multiplicative f : ℕ → ℕ", "not the identity", additivity on
  all Fibonacci sums with n,m ≥ 1. `f ≠ id` is non-identity in the sense of
  function extensionality, which is the intended meaning.
- Positivity: the queue scope says only "f : ℕ → ℕ" with no positivity
  hypothesis, so the absence of `∀ N, 0 < f N` is a faithful rendering of the
  queue text (the paper's construction is positive-valued, but the queue does
  not require that). Not a failure. In fact the witness `swapFibPrimes` is
  ℕ-valued and positive on all N ≥ 1.

## 3. Non-vacuity

The `example`s in `Statement.lean` are meaningful and all compile:
- `F 31 = 557 * 2417` — object exists.
- `Nat.Prime 557 ∧ Nat.Prime 2417 ∧ 557 ≠ 2417` — the two primes are real and distinct.
- `557 ∣ F 31 + F 31 ∧ 2417 ∣ F 31 + F 31` — divisibility side of `key31` is satisfiable.
- `¬ (557 ∣ F 1 + F 1) ∧ ¬ (2417 ∣ F 1 + F 1)` — the divisibility side also fails, so the iff is not vacuous.
- `IsMultiplicative id`, and `∃ f, IsMultiplicative f ∧ f ≠ id` (witness `n ↦ n^2`) — predicate is neither empty nor forced to identity.
- `swapFibPrimes 557 = 2417`, `swapFibPrimes 2417 = 557`, fixes 6, fixes 557·2417, sends 557·6 ↦ 2417·6, fixes 1 — the witness behaves as the paper claims.

## 4. Proof soundness (high level)

- `fib_period` derives `fib (n+124) ≡ fib n (mod M)` from `fib 124 ≡ 0` and
  `fib 123 ≡ 1 (mod M)` via `Nat.fib_add`, the standard addition formula
  `F(m+n+1) = F m·F n + F(m+1)·F(n+1)`, instantiated with m=123. Sound.
- `fib_mod_period` (strong induction) reduces `fib n mod M` to
  `fib (n mod 124) mod M`. The induction handles `n < 124` directly and
  `n ≥ 124` via `n = (n-124)+124` plus the period step. Sound.
- Instantiations for M = 557 and M = 2417 use `(by decide)` for
  `fib 124 % M = 0` and `fib 123 % M = 1`. Both verified (see below).
- `finite_check : ∀ i j : Fin 124, (557 ∣ fib i + fib j ↔ 2417 ∣ fib i + fib j)`
  is proven by kernel `decide` (not `native_decide`). `Fin 124` carries values
  0..123, so it covers `n % 124` and `m % 124` for every n,m (including residue
  0). The mapping `⟨n % 124, Nat.mod_lt _ (by norm_num)⟩` is correct.
- `key31` glues the reduction: `Nat.dvd_iff_mod_eq_zero` + `Nat.add_mod` +
  the two period lemmas show `(557 ∣ F n + F m) ↔ (557 ∣ F(n%124) + F(m%124))`
  and the analogous 2417 fact, then `finite_check` bridges them. The
  `hdvd557.trans (hfin.trans hdvd2417.symm)` chain has the right directions.
- `fib_dvd_iff` derives `557 ∣ F n ↔ 2417 ∣ F n` from `key31 n n` (so
  `557 ∣ 2·F n ↔ 2417 ∣ 2·F n`), dividing by the factor 2 via
  `dvd_two_mul_iff` for odd primes 557, 2417. Correct.
- `swapFibPrimes_mul` is an exhaustive case analysis on `p∣a, q∣a, p∣b, q∣b`
  under coprime a,b. Impossible cases (`p` dividing both a and b, or `q`
  dividing both) are discharged via `Nat.Prime.not_dvd_one` and
  `Nat.dvd_gcd`/`Nat.gcd a b = 1`. All 9 feasible combinations are covered;
  the `Nat.mul_div_cancel'` / `Nat.mul_div_assoc` rewrites are valid exactly
  where divisibility is assumed. Sound.
- `counterexample` uses `swapFibPrimes`, `swapFibPrimes_isMultiplicative`,
  non-identity by `swapFibPrimes 557 = 2417`, and additivity by
  `swapFibPrimes_eq_self (key31 n m hn hm)` together with
  `swapFibPrimes_fib n/m`. This is exactly the paper's argument
  ("applying the theorem first to a single Fibonacci number and then to a sum").

## 5. Numerical certificates (independently re-verified in Python)

- `F 31 = 1346269 = 557 · 2417`. ✓
- `F 124 % 557 = 0`, `F 123 % 557 = 1`, `F 125 % 557 = 1`. ✓
- `F 124 % 2417 = 0`, `F 123 % 2417 = 1`, `F 125 % 2417 = 1`. ✓
- Periodicity `F n mod M = F (n mod 124) mod M` holds for both M = 557 and
  M = 2417 for all n in 0..399 (exhaustive over the claimed period). ✓
- Full 124×124 residue check: 0 mismatches between the 557- and 2417-
  divisibility of `F i + F j`. ✓

## 6. Forbidden-token scan

No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`,
`extern`, or `debug.skipKernelTC` occur in `DsBatch/P07/*.lean`. The only
match for the string "sorry" is inside the comment "This file must stay
sorry-free" (`Statement.lean:3`), which is not a `sorry` term. All finite
computations use the kernel-checked `decide` tactic.

## Caveats

- The `1 ≤ n` / `1 ≤ m` hypotheses are unused inside `key31`'s proof: the
  theorem actually holds for all n,m ≥ 0. This is a harmless strengthening of
  the proof internals, not of the statement.
- `project.json` still has `freeze.frozen: false`; that is project-state
  bookkeeping, not a defect in the formalization.
