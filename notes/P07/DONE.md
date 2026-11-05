# DONE: P07

Project: P07 — *The Fibonacci numbers are not an additive uniqueness set for
multiplicative functions* (arXiv 2609.08137, Poo-Sung Park). Finished 2026-11-05.

## Result

`bash infra/eval.sh P07` reports `main_status: proved` (`frozen_ok=true`,
`build_ok=true`, `static_hits=0`).  Both targets are proved with axioms exactly
`{propext, Classical.choice, Quot.sound}`:

- `DsBatch.P07.key31 : DsBatch.P07.key31_statement`
- `DsBatch.P07.counterexample : DsBatch.P07.counterexample_statement`

What is proved (the queue's required scope):

- `DsBatch/P07/Defs.lean` defines `p = 557`, `q = 2417`, `F := Nat.fib`
  (`F 0 = 0`, `F 1 = 1`), the paper's notion of a multiplicative function
  (`IsMultiplicative`: `f 1 = 1` and `f (ab) = f a * f b` for coprime `a, b`),
  and the paper's explicit function `swapFibPrimes` (equation (2.1)) exchanging
  the multiplicative contributions of the two prime factors of
  `F 31 = 1346269 = 557 · 2417`.
- `DsBatch/P07/Statement.lean` (frozen) states
  1. `key31_statement`: `∀ n m ≥ 1, 557 ∣ F n + F m ↔ 2417 ∣ F n + F m`
     (the paper's Theorem `thm:key31`);
  2. `counterexample_statement`: there is a multiplicative `f : ℕ → ℕ`, not the
     identity, with `f (F n + F m) = f (F n) + f (F m)` for all `n, m ≥ 1`,
     answering Spiro's 1992 question negatively.
  It also contains non-vacuity checks: `F 31 = 557 · 2417`; both primes prime
  and distinct; an instance where both divide a Fibonacci sum (`n = m = 31`);
  an instance where neither does (`n = m = 1`); `id` and `n ↦ n²` are
  multiplicative; the additivity equation is consistent; and the explicit
  `swapFibPrimes` swaps `557 ↔ 2417` while fixing `6`, `557·2417` and `1`.
- `DsBatch/P07/Main.lean` proves them:
  - **Periodicity.** `F 123 ≡ 1` and `F 124 ≡ 0` modulo both primes; the
    Fibonacci addition formula `F (m+n+1) = F m · F n + F (m+1) · F (n+1)`
    gives `F (n+124) ≡ F n`, hence `F n ≡ F (n mod 124)`.
  - **`key31`.** Reduces to the `124 × 124` residue check, a kernel `decide`
    over `Fin 124 × Fin 124` (≈15 376 cases; kernel-checked, not
    `native_decide`).  This is exactly the modular certificate displayed in
    Section 4 of the paper.
  - **`counterexample`.** `swapFibPrimes` is multiplicative (exhaustive case
    analysis on which of `p, q` divide `a` and `b`, using coprimality and
    primality of `p, q`); it fixes every Fibonacci number (apply `key31` with
    `m = n` and cancel the odd factor `2`) and every Fibonacci sum (apply
    `key31` directly); and it swaps `557` and `2417`, so it is not the
    identity.  Hence the Fibonacci numbers are not an additive uniqueness set.

## Size

| file | lines |
|---|---|
| `DsBatch/P07/Defs.lean` | 51 |
| `DsBatch/P07/Statement.lean` | 95 |
| `DsBatch/P07/Main.lean` | 236 |
| total | 382 |

## Spend and wall time

- Spend: **0.805 CNY** of the 4 CNY cap.
- Wall time: **≈17 minutes** (start 2026-11-05T14:15:31Z; eval at 14:30:46Z).
- Chunks: 1 (chunk limit 100 minutes).

## Paper gaps / errors

No mathematical error found.  The paper's Theorem `thm:key31`, its modular
certificate (`rank` 31, `F 32 ≡ 439 (557)`, `F 32 ≡ 592 (2417)`, the
fourth-power residue table) and the counterexample construction all check out,
and the finite certificate was independently re-verified during the audit.

One omitted-but-routine step (not an error): the paper says "Applying the
theorem first to a single Fibonacci number and then to a sum gives
`f(F_n) = F_n`".  Formally this uses `thm:key31` with `m = n` (so the sum is
`2F_n`) together with the fact that `557` and `2417` are odd, whence
`r ∣ 2 F_n ↔ r ∣ F_n`.  This is done in `fib_dvd_iff`.

Scope note: the frozen statement asks for an `ℕ`-valued `f`, exactly as the
queue scope says.  The explicit witness is in fact positive-valued (the paper's
"positive integer values"), but positivity is not part of the frozen statement.
The optional parts (signature-switching Proposition and the general criterion
Theorem) were not formalised; they are outside the required scope.
