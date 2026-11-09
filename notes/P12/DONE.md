# P12 — DONE

Project: formalization of Tian-Xiao He, *The Family `X_{qp^s}` for Distinct Primes `q, p`
in Connection with Carmichael's Totient Conjecture* (arXiv:2610.34808), required scope from
`queue/QUEUE.md`.

Status: `main_status: proved` (eval at 2026-11-05T22:29:20Z; `frozen_ok: true`,
`build_ok: true`, `static_hits: 0`).

## What is proved

The three frozen targets each compile as `example : <lean_type> := <name>` with axiom set
`{propext, Classical.choice, Quot.sound}` (no `sorry`, no extra axioms):

* `DsBatch.P12.master_formula : DsBatch.P12.master_formula_statement` — Proposition
  (Master formula): for every odd prime `p ≠ 3` and every `s ≥ 1`,
  `X_{2p^s} = {2p^s+1, 2(2p^s+1)}` if `2p^s+1` is prime, and `X_{2p^s} = ∅` otherwise.
* `DsBatch.P12.even_case : DsBatch.P12.even_statement` — Theorem (even): `X_{2p^s} = ∅`
  for every even positive `s`.
* `DsBatch.P12.odd_case : DsBatch.P12.odd_statement` — Theorem (odd): the master formula
  for every odd positive `s`.

Here `X k = {n : ℕ | Nat.totient n = k}` and `qCandidate p j = 2*p^j+1` (`DsBatch/P12/Defs.lean`,
frozen); the statements are exactly those frozen in `DsBatch/P12/Statement.lean` (frozen).

## Proof contents (`DsBatch/P12/Main.lean`)

The proof follows the paper's structure:

* `five_le_of_odd_prime_ne_three`, `prime_dvd_candidate` (paper `lem:candidates`):
  classification of the prime divisors of a solution.
* `not_dvd_of_totient_eq` (paper `lem:p-not-divide`): `p ∤ n`.
* `factorization_two_le_two`, `factorization_three_le_one`, `factorization_q_le_one`
  (paper `lem:factorization`): exponent bounds `v_2(n) ≤ 2`, `v_3(n) ≤ 1`, `v_{q_j}(n) ≤ 1`.
* `sum_factor_sub_one_factorization_p`: the exact `p`-adic comparison
  `∑_{j∈T} j = s`, via the identity `φ(n)·∏_{ℓ|n}ℓ = n·∏_{ℓ|n}(ℓ-1)`
  (`Nat.totient_mul_prod_primeFactors`) rather than an explicit factorization of `n`.
* `key_classification`: the `2`-adic comparison gives `|T| = 1`, `v_3(n) = 0`,
  `v_2(n) ∈ {0,1}`, `T = {s}`; hence `q_s` is prime and `n = q_s` or `2q_s`.
* `three_dvd_candidate_of_even`, `not_prime_candidate_of_even` (paper `lem:mod3`):
  for even `s`, `3 ∣ 2p^s+1 > 3`, so `2p^s+1` is composite; this feeds `even_case`.
* `master_formula`, `even_case`, `odd_case`: assembly, including the converse
  `φ(q_s) = φ(2q_s) = 2p^s` via `Nat.totient_prime` and `Nat.totient_mul`.

No statement was weakened and no hypothesis was added; the frozen files were not edited after
the freeze.

## Size

* `DsBatch/P12/Defs.lean`: 28 lines (frozen)
* `DsBatch/P12/Statement.lean`: 96 lines (frozen)
* `DsBatch/P12/Main.lean`: 757 lines
* Total Lean: 881 lines

## Spend and wall time

* Spend: 1.182563 CNY as reported by the eval snapshot (budget 4 CNY), 1 chunk; the ledger
  cumulative at the last recorded request (22:29:31Z) was 1.201019 CNY.
* Wall time: 2026-11-05T22:09:49Z → 2026-11-05T22:29:20Z (about 20 minutes).

## Deviations, paper gaps and errors

* No mathematical gap or error was found in the required scope; every step of the paper's
  proof was reproduced in Lean.
* Documentation-only discrepancy: the frozen `Statement.lean` docstrings say
  "Proposition 3.5" / "Theorems 3.7, 3.8". The paper's preamble declares
  `\newtheorem{theorem}{Theorem}` without `[section]`, so its counter is global and the
  compiled numbers are Proposition 5, Lemma 6, Theorem 7, Theorem 8. The frozen statements
  themselves are unaffected; the files are frozen and this note records the discrepancy
  rather than papering over it.
* The optional parts of the paper (the `p = 3` formula for `X_{2·3^s}` and the `X_{4q}`
  formula for primes `q ≥ 7`) were out of the frozen required scope and were not formalized;
  doing so would require new statements, a fresh audit and a re-freeze.
