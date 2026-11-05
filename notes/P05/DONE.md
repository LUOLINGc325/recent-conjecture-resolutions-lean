# DONE: P05 (arXiv 2609.17006)

Paper: I. Chinyere, *Unipotence of a double commutator with transvections*.

Status: **proved** (`bash infra/eval.sh P05` → `main_status: proved`,
`frozen_ok: true`, `build_ok: true`, `static_hits: []`).

## What is proved

The single frozen target `DsBatch.P05.main`, with type
`DsBatch.P05.main_statement`, is precisely Theorem 2.9 of the paper:

* for every nonzero commutative ring `R` with identity, every `n ≥ 3`, and every
  `σ ∈ GL_n(R)` (modelled as `Matrix.GeneralLinearGroup (Fin n) R`), there exist
  nonidentity transvections `τ₁, τ₂` — `τ = I_n + u ⊗ f` with `f(u) = 0` and
  `u ⊗ f ≠ 0` (Definition 2.3) — such that `[[σ, τ₁], τ₂] = I_n`, where
  `[g, h] = g h g⁻¹ h⁻¹`.

The proof follows the paper's argument literally:

* Lemma 2.7 (`exists_functional`): for a standard basis vector `e i` and any `w`,
  and indices `j, k` distinct from `i` and each other, there is a nonzero
  functional `f` with `f(e i) = f(w) = 0`; explicitly
  `f = w k · e j^* − w j · e k^*`, or `f = e j^*` if `w j = w k = 0`.
* Set `N = v ⊗ f` with `v = e i`, so `N² = 0`, and `M = σ N σ⁻¹`, so
  `M² = 0`. One computes `N M = 0` (using `f(w) = 0`) and hence
  `(M N)² = 0`, and `[σ, 1 + N] = 1 + (M − N − M N)`.
* Case `M N ≠ 0`: take `τ₂ = 1 + M N`. Then `M N = (σ v) ⊗ g` with
  `g = f(σ⁻¹ v) · f`, and `g(σ v) = 0`, so `τ₂` is a transvection;
  `(M − N − M N)` commutes with `M N`.
* Case `M N = 0`: take `τ₂ = τ₁`. Then `(M − N − M N)` commutes with `N`.

In both cases `⁅σ, τ₁⁆` commutes with `τ₂`, which by
`commutatorElement_eq_one_iff_mul_comm` is `[[σ, τ₁], τ₂] = 1`.

No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`,
`extern` or `debug.skipKernelTC` occurs in the project files. `#print axioms` for
the target is `{propext, Classical.choice, Quot.sound}`.

## Files and size

| file | lines |
| --- | --- |
| `DsBatch/P05/Defs.lean` | 36 |
| `DsBatch/P05/Statement.lean` | 114 |
| `DsBatch/P05/Main.lean` | 257 |
| **total** | **407** |

Frozen SHA-256 (in `projects/P05/project.json`):
`Defs.lean a4363d9e…61f9396`, `Statement.lean f69fa1e5…5f2cfe`.

## Cost and time

* Spend: 0.917581 CNY at the `eval` snapshot; cap 4.0 CNY, 1 chunk.
* Wall time: 2026-11-05T13:32:42Z → 13:47:46Z, about 15 minutes.
* The fidelity audit was run by one fresh `opus` subagent; verdict `PASS`
  (`projects/P05/AUDIT.md`).

## Paper gaps / errors

None found. The proof was checked line by line against the TeX and follows it.

Scope note: the formalization does not use Remark 2.4 (unimodularity / the
"usual rank-one type" discussion). This is not a gap: Definition 2.3 only
requires `u ⊗ f ≠ 0`, and in the case `M N ≠ 0` the matrix `M N = (σ v) ⊗ g`
is nonzero by the case hypothesis, so the paper's `τ₂` is a transvection under
the paper's own definition. The paper's numbering (all theorem-like
environments share one counter) gives Definition 2.1, Definition 2.3,
Lemma 2.5, Lemma 2.7, Theorem 2.9; the doc comments use these numbers.
