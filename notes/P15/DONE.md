# DONE — P15

Paper: arXiv 2610.22783, *Counterexamples to the local antimagic leaf
conjecture* (Brondani–França).

Status: **proved** (`bash infra/eval.sh P15` → `main_status: proved`).

## What is proved

Four targets, stated in `DsBatch/P15/Statement.lean` and proved in
`DsBatch/P15/Main.lean`:

1. `t3_caterpillar` — `T₃ = Cat(8,7,25)` is a caterpillar (`IsCaterpillar`),
   with `|V| = 43`, `|E| = 42`, `ℓ(T₃) = 40` leaves and degrees
   `d(a) = d(b) = 9`, `d(c) = 26`.
2. `t3_weight_separation` — for every local antimagic bijection
   `L : E(T₃) → {1,…,42}`, the induced-weight image has cardinality 43
   (`(weightImage T3 L).card = 43`): all 43 induced vertex weights are
   pairwise distinct.
3. `t3_chiLa` — `χ_la(T₃) = 43` and `χ_la(T₃) = ℓ(T₃) + 3`.
4. `leaf_conjecture_false` — `¬ LeafConjecture`: the leaf conjecture
   (`χ_la(T) ≤ ℓ(T) + 2` for every tree of order at least three) is false,
   refuted by `T₃` with `χ_la(T₃) = 43 = 40 + 3`.

Proof outline:

* Lemma 3.1 of the paper (degree bounds on induced weights) is proved
  generally: the incident labels, sorted, satisfy `i ≤ tᵢ ≤ m-d+i`, so
  `d(d+1)/2 ≤ f⁺(v) ≤ d(2m-d+1)/2`. The two order-statistic inequalities are
  proved by induction (`range_sum_le_finset_sum`, `finset_sum_le_range_sum`)
  and applied to the incidence finset (`inducedWeight_lower`,
  `inducedWeight_upper`).
* For `T₃`: `I₄₂(9) = [45,342] = I₄₂(d(a)) = I₄₂(d(b))` and
  `I₄₂(26) = [351,767]`, all above `|E| = 42` and disjoint for the only
  nonadjacent internal pair `(a,c)`. Leaves have pairwise distinct weights
  (the label of their pendant edge) at most 42, and `a,b` are adjacent, so
  local antimagic separates them. Hence every local antimagic labelling has
  43 distinct weights.
* Existence for the `sInf` defining `χ_la` is supplied by the paper's explicit
  labelling `t3Labeling` (`ab = 1`, `bc = 2`, the 8 `a`-leaves `3..10`, the
  7 `b`-leaves `11..17`, the 25 `c`-leaves `18..42`; weights
  `f⁺(a) = 53`, `f⁺(b) = 101`, `f⁺(c) = 752`), proved local antimagic by
  kernel evaluation.
* `T₃` is proved to be a tree structurally: `Connected` by exhibiting walks
  from `a` to every vertex, then `IsTree` via
  `SimpleGraph.isTree_iff_connected_and_card` (`42 + 1 = 43`).
* `¬ LeafConjecture` instantiates the conjecture at `T₃`.

## Verification

* `lake build DsBatch`: 9051 jobs, success.
* Frozen statements: SHA-256 of `DsBatch/P15/Defs.lean` and
  `DsBatch/P15/Statement.lean` match `projects/P15/project.json`
  (`freeze.frozen = true`).
* All four targets check as `example : <lean_type> := <name>`; each depends
  only on `propext`, `Classical.choice`, `Quot.sound`.
* No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`,
  `extern` or `debug.skipKernelTC` in any P15 code file (`static_hits = []`).
* Independent `opus` fidelity audit: `projects/P15/AUDIT.md` first line
  `PASS` (re-audited after comment-only citation fixes).

## Lean line count

| file | lines |
| --- | --- |
| `DsBatch/P15/Defs.lean` | 248 |
| `DsBatch/P15/Statement.lean` | 56 |
| `DsBatch/P15/Main.lean` | 462 |
| total | 766 |

## Spend and wall time

* Spend: **4.728544 CNY** of the 5.0 CNY cap (P15 ledger, 4 chunks).
* Wall time: start `2026-11-09T07:33:56Z`, finish about
  `2026-11-09T08:33Z` — roughly **1.0 h** of the 72 h budget.

## Paper gaps / errors found

1. **The queue/TASK paraphrase is false as written.** The required-scope
   sentence says that for `T₃ = Cat(8,7,25)` "every bijection
   `E(T₃) → {1,…,42}` has pairwise distinct induced vertex weights". This is
   false, and the paper does not assert it for `T₃`. Explicit bijection with
   a collision:

   ```
   f(ab) = 7, f(bc) = 16,
   a-leaves: 1, 8, 21, 22, 23, 25, 27, 30      (sum 157)
   b-leaves: 6, 9, 15, 20, 24, 26, 41          (sum 141)
   c-leaves: the remaining 25 labels
   ```

   Then `f⁺(a) = 7 + 157 = 164 = 7 + 16 + 141 = f⁺(b)`, so adjacent `a,b`
   have equal weights; the labelling is not local antimagic. The paper's
   Theorem 4.1 proves only `χ_la(T₃) = 43 = ℓ(T₃) + 3`. Its Corollary 3.3
   ("every bijection is antimagic") requires the intervals to be pairwise
   disjoint for *every* pair of distinct internal vertices, which fails for
   `a,b` (both have `I₄₂(9) = [45,342]`); Proposition 3.2 only requires
   disjointness for nonadjacent pairs, and adjacency handles `a,b`.
   Consequently `Statement.lean` freezes the true local-antimagic claim
   (`t3_weight_separation`) together with `χ_la(T₃) = 43` and
   `¬ LeafConjecture` — the required mathematical goal — rather than the
   false literal phrase. This is documented in `NOTES.md` and was verified
   independently by the audit.
2. No error was found in the paper's own proof of Theorem 4.1; the
   separation criterion is applied correctly (`a,c` are the only nonadjacent
   internal pair, their intervals lie above 42 and are disjoint).
3. The optional scope (`χ_la(Cat(21,20,99,100)) = 244`, and the infinite
   `H_{r,t}` families) was not attempted: the required scope is proved and
   the budget is nearly exhausted (4.73 of 5 CNY).

## Notes on numbering

The paper's actual numbering (shared theorem counter, numbered by section) is
Lemma 3.1, Proposition 3.2, Corollary 3.3, Theorem 4.1 for `T₃`; comments in
the Lean files cite these numbers.
