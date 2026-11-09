PASS

Audit of P12 frozen-to-be statements against arXiv 2610.34808 (paper TeX: `papers/2610.34808/qp_s_family_notes-Oct-25-2026.tex`).

## What I checked

1. **Definitional faithfulness.** `DsBatch.P12.X` is `{n | Nat.totient n = k} : Set ℕ`, exactly the paper's `X_k = {n ∈ ℕ : φ(n) = k}` (φ = `Nat.totient`). `qCandidate p j = 2*p^j + 1` matches the paper's `q_j = 2p^j + 1`. No forbidden constructs.

2. **Statement exactness.** All three propositions match the paper's hypotheses, quantifiers, case split, and solution sets:
   - `master_formula_statement` = Proposition (Master formula), label `prop:master`: `∀ p s, Prime p → Odd p → p ≠ 3 → 1 ≤ s → (Prime(2p^s+1) → X(2p^s) = {2p^s+1, 2(2p^s+1)}) ∧ (¬Prime(2p^s+1) → X(2p^s) = ∅)`. Matches the paper exactly (odd prime p ≠ 3, s ≥ 1, prime/composite split on `2p^s+1`).
   - `even_statement` = Theorem (`thm:even`): `∀ p s, Prime p → Odd p → p ≠ 3 → 0 < s → Even s → X(2p^s) = ∅`. Matches the paper's Theorem 3.7: `p` prime with `3 ∤ p` (equivalently `p ≠ 3`), `p` odd, `s` an even positive integer.
   - `odd_statement` = Theorem (`thm:odd`): `∀ p s, Prime p → Odd p → p ≠ 3 → 0 < s → Odd s → (Prime(2p^s+1) → X(2p^s) = {2p^s+1, 2(2p^s+1)}) ∧ (¬Prime(2p^s+1) → X(2p^s) = ∅)`. Matches the paper's Theorem 3.8: `p` odd prime, `p ≠ 3`, `s` odd positive, with the same prime/composite dichotomy.
   - The implication/conjunction form `(P → A) ∧ (¬P → B)` is a faithful rendering of the paper's brace case split (not a weakening); `P` and `¬P` are exhaustive, and the primality condition is not smuggled in as a global hypothesis.
   - No weakening, no added hypothesis, no missing hypothesis, no conclusion restated as hypothesis.

3. **Scope.** Only the required scope is stated: the master formula and the even/odd theorems. The optional parts — the p=3 formula (`prop:p3-master`) and the `X_{4q}` formula (`prop:mirror-master`) — are NOT stated. The p=3 appearance in the non-vacuity checks is only a negative test that the master formula would fail at p=3, not a statement of the p=3 formula.

4. **Non-vacuity.** All `example`s compile (verified by `lake build DsBatch`, which succeeds; only Main.lean stubs carry `sorry`). Checks are mathematically correct: `φ(11)=φ(22)=10`, `φ(9)=6`; `2·5+1=11` prime and `2·7+1=15` composite; the `p ≠ 3` hypothesis is shown non-redundant via `9 ∈ X 6 ∧ 9 ∉ {7,14}`; the parity hypothesis in the even theorem is shown non-redundant via `11 ∈ X(2·5^1)` with `s=1` odd. Hypotheses are shown satisfiable (e.g. `5` is an odd prime ≠ 3; `s=2` is even and positive).

5. **Forbidden tokens.** `python3 -I infra/scan.py DsBatch/P12/Defs.lean DsBatch/P12/Statement.lean` returned `[]` (clean). The non-vacuity checks use only kernel `decide` / `norm_num`, not `native_decide`.

6. **Targets.** `projects/P12/project.json` lists exactly three targets with matching names/types, and `DsBatch/P12/Main.lean` declares `theorem master_formula : master_formula_statement`, `theorem even_case : even_statement`, `theorem odd_case : odd_statement`. Names and `lean_type`s align.

## Paper's proof / statement-level discrepancies

- The paper's Theorem 3.7 hypothesis is "p a prime with 3 ∤ p (equivalently p ≠ 3; together with p odd, i.e. p ≥ 5), s an even positive integer" — the Lean `Odd p` is faithful, not added (and is essential: dropping it would make the claim false at p = 2, where X_{2^{s+1}} is non-empty).
- The paper's Theorem 3.8 hypothesis is "p an odd prime, p ≠ 3, s an odd positive integer" — matches `odd_statement` exactly.
- No statement-level discrepancy found. The paper's internal numbering of these results is Prop (Master formula), Thm (even), Thm (odd), matching the task's "Proposition 3.5 / Theorem 3.7 / Theorem 3.8" (labels `prop:master`, `thm:even`, `thm:odd`).

## Residual risk

None material. The statement of the master formula requires `¬ Nat.Prime (2p^s+1)` to mean "composite"; this is exact because `2p^s+1 ≥ 2·5+1 = 11 > 1` for all odd primes p ≠ 3 and s ≥ 1, so non-prime is equivalent to composite.
