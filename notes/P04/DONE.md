# DONE: P04 (arXiv 2608.22635)

Paper: A. Jurasić, M. Jurasić, *Counterexamples to Dujella's conjecture on integral
points on the elliptic curve attached to a Diophantine triple*.

Status: **proved** (`bash infra/eval.sh P04` → `main_status: proved`,
`frozen_ok: true`, `build_ok: true`, `static_hits: []`).

## What is proved

The single frozen target `DsBatch.P04.counterexample`, with type
`DsBatch.P04.counterexample_statement`, establishes the paper's smallest explicit
counterexample (the case `k = 15`):

* `{5, 115, c_15}` with
  `c_15 = 19726599787079129775103071759543738099950374011720`
  is a Diophantine triple: `5·115+1 = 24²`, `5·c_15+1 = S_15²`,
  `115·c_15+1 = T_15²`, where
  `S_15 = 9931414749943516928215699`,
  `T_15 = 47629391928872028421837349`;
* `(x_15, y_15)` with
  `x_15 = 34307130064485443087135776973119544521652824368` and
  `y_15 = c_15·x_15 + 1`, is an integral point on
  `E : y² = (5x+1)(115x+1)(c_15·x+1)`, with `x_15 > 0`, `y_15 > 0`;
* `x_15 ≠ -1` and none of `5·x_15+1`, `115·x_15+1`, `c_15·x_15+1` is a perfect
  square; hence **Problem 4.8 is answered negatively** for this triple
  (`¬ Problem48At 5 115 c_15`);
* `x_15` is distinct from `0` and from both regular extension values
  `d_± = 120 + 1151·c_15 ± 48·S_15·T_15`
  (`d_- = 8569332541111894343538801554602513003703076192`,
  `d_+ = 45410624140523615630392927651668130503572757271903488`);
  hence **Dujella's Conjecture 1.4.5 is false** for this triple
  (`¬ DujellaConjectureAt 5 115 c_15 24 S_15 T_15`).

The proof is computational but small: the arithmetic identities are kernel
computations (`norm_num`), and nonsquareness is certified by quadratic
nonresidues modulo `7` (`5x+1 ≡ 3`, `115x+1 ≡ 5`) and modulo `13`
(`c_15·x_15+1 ≡ 11`). The paper uses moduli `11` and `2851`; any nonresidue
certificate is valid, and these smaller moduli keep the kernel checks tiny. No
`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern` or
`debug.skipKernelTC` occurs in the project files. `#print axioms` for the target is
`{propext, Classical.choice, Quot.sound}`.

## Files and size

| file | lines |
| --- | --- |
| `DsBatch/P04/Defs.lean` | 86 |
| `DsBatch/P04/Statement.lean` | 100 |
| `DsBatch/P04/Main.lean` | 89 |
| **total** | **275** |

Frozen SHA-256 (in `projects/P04/project.json`):
`Defs.lean f35499ef…331e07`, `Statement.lean 3a9e34c5…736c0537`.

## Cost and time

* Spend: about 0.79 CNY cumulative in the project ledger (0.760197 CNY when this
  report was first written, 0.7941 CNY at the final `eval` snapshot); cap 3.0 CNY,
  1 chunk.
* Wall time: 2026-11-05T13:19:22Z → 13:30:27Z, about 11 minutes.
* The fidelity audit was run by one fresh `opus` subagent (contract: result
  `PASS`, `projects/P04/AUDIT.md`).

## Paper gaps / errors

None found. All numerical data in the paper were checked independently: `c_15`,
`S_15`, `T_15`, `x_15`, the identities `5c+1=S²`, `115c+1=T²`, `5·115+1=24²`,
`c_15 = 575x_15+120`, `T_15² − 23 S_15² = −22`, the values of `d_±`, and the
residues used in the paper's certificates modulo `11` and `2851` all check out.

Scope note: only the queue's **required** part is formalized — one explicit
counterexample, the paper's smallest (`k = 15`). The optional infinite family
(Theorem 3.1 for all `k ≡ 15, 440 (mod 575)`, and the second Pell orbit of
Lemma 2.2/Remark 2.3) is not formalized. This is a scope choice, not a gap in the
paper.
