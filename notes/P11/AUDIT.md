PASS

# Fidelity audit: P11 (atlas-lean port of P02, Noel arXiv:2609.23291)

Audited against the source of truth in `papers/atlas-P02/`:
- `PartialListColoringWanted.lean` (defines `IsListColoring`, `lambdaMax`, `lambdaMin`, `conjecture`, plus a `theorem_wanted conjecture_refuted : ¬ conjecture` line)
- `ListColoring.lean` (defines `SimpleGraph.IsListColorable`, `SimpleGraph.IsChoiceNumber`, and two lemmas `IsListColorable.mono` / `IsListColorable.colorable`)

Audited files: `DsBatch/P11/Defs.lean`, `DsBatch/P11/Statement.lean`, `DsBatch/P11/Main.lean`,
`projects/P11/project.json`; P02 context in `DsBatch/P02/{Defs,Statement,Main}.lean` (already reviewed/proved).

## 1. Verbatim fidelity of the copied definitions

Every required definition body is **byte-identical** to the atlas source (verified with `sed` +
`diff`, not just by eye). Docstrings aside, the following pairs are IDENTICAL:

| Definition | atlas source lines | Defs.lean lines | Result |
|---|---|---|---|
| `IsListColoring` | `PartialListColoringWanted.lean` 29–31 | 83–85 | identical |
| `lambdaMax` | `PartialListColoringWanted.lean` 36–38 | 90–92 | identical |
| `lambdaMin` | `PartialListColoringWanted.lean` 42–44 | 96–98 | identical |
| `conjecture` | `PartialListColoringWanted.lean` 49–53 | 103–107 | identical |
| `SimpleGraph.IsListColorable` | `ListColoring.lean` 29–32 | 47–50 | identical |
| `SimpleGraph.IsChoiceNumber` | `ListColoring.lean` 36–37 | 54–55 | identical |
| `IsListColorable.mono` + `.colorable` | `ListColoring.lean` 40–49 | 58–67 | identical |

Also identical: the Meta copyright header (7 lines), the `namespace
MathlibExt.GraphTheory.PartialListColoringWanted` / `namespace SimpleGraph` lines, and the
`variable {V : Type*} {G : SimpleGraph V} {q r : ℕ}` line.

Permitted deletions / adaptations (all present exactly as required, none a fidelity violation):
- `module` line: dropped. OK.
- `public import ...` lines (Batteries.Util.ProofWanted, Mathlib.Combinatorics...,
  MathlibExt...): dropped; the single `import Mathlib` at line 1 is the necessary replacement. OK.
- `@[expose] public section` lines: dropped. OK.
- `MathlibExt` import: dropped; the `ListColoring.lean` content is inlined **before** the
  `PartialListColoringWanted` namespace (lines 33–69), because `conjecture` needs
  `SimpleGraph.IsChoiceNumber` which the dropped import used to provide. Definition bodies
  unchanged. OK — this is exactly the adaptation the queue prescribes.
- `public theorem_wanted conjecture_refuted : ¬ conjecture` (atlas line 63): not copied. Its
  Batteries `ProofWanted` macro and import are dropped, and the real
  `theorem conjecture_refuted : conjecture_refuted_statement` in `Main.lean` replaces it. OK.

## 2. Target statement and project.json

- `DsBatch/P11/Statement.lean` line 16: `def conjecture_refuted_statement : Prop := ¬ conjecture`
  — exactly the negation of the copied `conjecture`, no added hypotheses, no weakening or
  strengthening. `conjecture` is the byte-identical atlas definition.
- `projects/P11/project.json` target: `{"name": "DsBatch.P11.conjecture_refuted",
  "lean_type": "DsBatch.P11.conjecture_refuted_statement"}` — matches the definition name and
  type exactly.
- `DsBatch/P11/Main.lean` line 89: `theorem conjecture_refuted : conjecture_refuted_statement :=
  by ...` — the target theorem has the target type.

## 3. Non-vacuity (build + examples)

`lake build DsBatch` succeeds (exit 0, 9088 jobs). The `example`s in `Statement.lean` are all
elaborated (the file has no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`/`implemented_by`/
`extern`/`debug.skipKernelTC` — the only `sorry` strings are inside doc comments).

Genuine, non-trivial checks:
- `example : DsBatch.P02.G.IsChoiceNumber 3 := p02_isChoiceNumber` — the explicit 14-vertex graph
  satisfies the hypothesis of `conjecture` (choice number 3 in the atlas sense); `p02_isChoiceNumber`
  is a real theorem in `Statement.lean`, not a stub.
- `example : Fintype.card DsBatch.P02.V = 14 := by decide` — the object exists with 14 vertices.
- `example : DsBatch.P02.IsListAssignment DsBatch.P02.L 2` — `L` is a genuine 2-list assignment.
- `example : ∃ S f, IsListColoring DsBatch.P02.G DsBatch.P02.L f S ∧ S.card = 9` — a genuine
  9-vertex partial list colouring in the *atlas* `IsListColoring` sense (via P02's `S9`/`c9`;
  P02's `IsPartialListColoring` is definitionally equal to atlas `IsListColoring`, so the reuse is
  sound).
- `example : (⊥ : SimpleGraph (Fin 1)).IsChoiceNumber 1` — `IsChoiceNumber` is not vacuously false
  (the one-vertex edgeless graph has choice number 1).

## 4. Correctness of the bridge lemmas and non-vacuity of `¬ conjecture`

- `isListColorable_of_choosable` (Statement.lean 26–62): sound. It shrinks each list of size `≥ q`
  to size exactly `q` via `Finset.exists_subset_card_eq (hlists v)` — legitimate for P02's
  `Choosable`, which needs lists of size exactly `q`. The `ℕ`-encoding `ψ` is built from
  `Fintype.equivFin` on the finite union `U`, so it is injective on `U` (proved in `hψ`); each
  shrunk list `ls v ⊆ U`, so `ψ` is injective on `ls v` and
  `Finset.card_image_of_injOn` preserves the cardinality `q`. The returned `H.Coloring C` carries
  the properness proof via `hprop'` and `hg_val`. Correct.
- `choosable_of_isListColorable` (Statement.lean 65–69): sound. Instantiates atlas
  `IsListColorable` with colour type `ℕ`; `rw [hL v]` turns the P02 `IsListAssignment` equality
  `(L v).card = q` into the needed `q ≤ (L v).card`. The `H.Coloring ℕ`'s `valid` gives P02's
  properness. Correct.
- `p02_isChoiceNumber` (Statement.lean 73–80): correct. Positive direction from P02's
  `choosable_three`; minimality (`∀ r < 3, ¬ IsListColorable r`) by `interval_cases` into
  `not_choosable_zero/one/two`. Correct.

- No vacuity/fidelity hazard: `lambdaMax`/`lambdaMin` are the atlas `sSup`/`sInf` definitions over
  the atlas `IsListColoring` predicate (byte-identical), not some silent variant. `conjecture` is
  the full atlas universal statement (over `V : Type`, arbitrary `G`, `χ_ℓ r s : ℕ`, with
  hypotheses `IsChoiceNumber χ_ℓ`, `1 ≤ r`, `r ≤ s`, `s ≤ χ_ℓ`), so `¬ conjecture` is the exact
  required scope — no extra hypotheses, no restriction to the counterexample graph.

## Notes

- During the audit the working tree progressed past the stub stage: `Main.lean` now contains a
  complete `sorry`-free proof of `conjecture_refuted` (it was a 13-line stub when the audit began).
  This does not affect the frozen-statement audit; `Defs.lean` (109 lines) and `Statement.lean`
  (124 lines) were unchanged throughout. The proof reuses `p02_isChoiceNumber` and the bridge
  lemmas as intended, so the proof stage is consistent with the audited statement.
- `lake build` emits only a benign module-system hint for `DsBatch/P11/Defs.lean`
  ("imports `Mathlib` … consider adding `module`"), also present for P10; not a fidelity issue.
- `project.json` still has `"freeze": {"frozen": false}` — the freeze step (`infra/freeze.sh P11`)
  has not yet been run; nothing here blocks it.

## Verdict

**PASS.** All five required definitions (plus the two lemmas and the copyright header) are copied
verbatim; the permitted deletions are exactly the prescribed ones; the target is the exact negation
of the copied `conjecture`; `project.json` matches; and the non-vacuity examples compile and are
genuine.
