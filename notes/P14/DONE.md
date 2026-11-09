# P14 — Done

Project: P14, arXiv 2610.03151 (Luca Sabatini, "Arithmetic properties of
solubilizers").

## What is proved

`DsBatch.P14.main : DsBatch.P14.main_statement`, i.e. for every finite group
`G`, every `x : G` and every subgroup `K ≤ G`,

```
|N_G(x) ∩ K|  divides  |Sol_G(x) ∩ K|,
```

where

- `N_G(x) = {g : G | ⟨x⟩ ⊴ ⟨x, g⟩}` (`normalizerOf x`, formalised as the
  Mathlib normalizer of the cyclic subgroup `⟨x⟩`), and
- `Sol_G(x) = {g : G | ⟨x, g⟩ is soluble}` (`solubilizer x`).

This is exactly the queue's required scope (the case `K = G` is the
Mousavi–Poozesh–Zamani conjecture). No hypotheses were added, nothing was
weakened, and the frozen files `Defs.lean` / `Statement.lean` are unchanged
(freeze verified by `infra/eval.sh`).

Evaluation (`projects/P14/state/eval.json`):

```
main_status = proved
frozen_ok   = true
build_ok    = true
static_hits = []
axioms of DsBatch.P14.main = [propext, Classical.choice, Quot.sound]
```

## Proof structure

Following the paper: induction on `|K|`. Let `H = N_G(x) ∩ K`,
`A = Sol_G(x) ∩ K`, and let `T ≤ K` be maximal among normal subgroups of
`K` contained in `H` with `⟨x, a, T⟩` soluble for all `a ∈ A`. The paper's
maximality claim `(H/T) ∩ Z(K/T) = 1` is `Claim.claim_center_inf`. Then
`A` is a union of right `T`-cosets, `H/T` acts by conjugation on `A/T`,
and a Cauchy–Frobenius count (`Counting.lean`) together with the induction
hypothesis applied to the proper subgroup `K`-preimage of `C_{K/T}(g)`
yields `|H/T| ∣ |A/T|`; multiplying by `|T|` (`Coset.lean`) gives the
result.

Modules: `Basic.lean` (conjugation helpers), `Claim.lean` (maximality
claim, `threeGen`), `Counting.lean` (Cauchy–Frobenius), `Coset.lean`
(coset-cardinality), `Proof.lean` (induction), `Main.lean` (the target).

## Statistics

- Lean line count (`DsBatch/P14/*.lean`, total): **1315**
  - frozen `Defs.lean` + `Statement.lean`: 166
  - proof development: **1149**
    (`Basic` 122, `Claim` 425, `Coset` 49, `Counting` 163, `Proof` 370,
    `Main` 20).
- Spend: **6.13 CNY** reported by the completing eval (`spent_cny`
  6.129138; the ledger total continued to accrue proxy usage afterwards,
  6.20 CNY when these notes were written), against a cap of 7.5 CNY
  (extended once from the queue cap of 5.0).
- Wall time: **2 h 25 min** (project start 2026-11-09T05:06:51Z → eval
  2026-11-09T07:31:50Z), including the S phase and freeze.

## Errors or gaps in the paper

None found. The paper's argument went through as stated; the only friction
was formalisation detail (normalizer-of-cyclic-subgroup definitions and
subtype/quotient coercions), not mathematical content.
