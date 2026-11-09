# P11 — DONE

Project: atlas-lean port of P02 (Noel, arXiv:2609.23291), target `¬ conjecture` (Iradmusa's
partial list colouring ratio conjecture, Open Problem Garden `OPG-788`).

Status: `main_status: proved` (eval at 2026-11-05T22:08:03Z; `frozen_ok: true`,
`build_ok: true`, `static_hits: 0`).

## What is proved

The frozen target compiles as `example : <lean_type> := <name>` with axiom set
`{propext, Classical.choice, Quot.sound}` (no `sorry`, no extra axioms):

* `DsBatch.P11.conjecture_refuted : DsBatch.P11.conjecture_refuted_statement`, where
  `conjecture_refuted_statement : Prop := ¬ conjecture`.

`Defs.lean` contains the atlas-lean definitions verbatim (Meta Apache-2.0 header kept; only the
`module` / `public import` / `@[expose] public section` lines and the `MathlibExt` import
dropped): `IsListColoring`, `lambdaMax`, `lambdaMin`, `conjecture`, and
`SimpleGraph.IsListColorable` / `SimpleGraph.IsChoiceNumber` together with the two accompanying
lemmas. The copied blocks were checked byte-for-byte against
`papers/atlas-P02/PartialListColoringWanted.lean` and `papers/atlas-P02/ListColoring.lean`.

The refutation uses the 14-vertex graph `G` and the 2-list assignment `L` of DsBatch/P02:

* `λ_2 ≤ 9`: `L` is a 2-list assignment, and P02's `nine_bound` shows no partial proper
  `L`-colouring colours more than nine vertices; hence the minimum `λ_2` over 2-list
  assignments is at most 9.
* `λ_3 = 14`: P02's `choosable_three` gives a full proper colouring from every 3-list
  assignment, so `λ_L = 14` for every 3-list assignment; hence `14 ≤ λ_3`.
* Therefore `λ_2 / 2 ≤ 9/2 < 14/3 ≤ λ_3 / 3`, contradicting `conjecture` at
  `χ_ℓ = 3`, `r = 2`, `s = 3` (all side conditions `1 ≤ 2`, `2 ≤ 3`, `3 ≤ 3` hold).

## Proof contents (DsBatch/P11/Main.lean)

* `lambdaMax_set_nonempty`: the empty colouring makes `lambdaMax`'s defining set nonempty.
* `lambdaMax_le_card`: `λ_L` never exceeds the number of vertices.
* `lambdaMax_P02L_le_nine`: `λ_L ≤ 9` for the paper's 2-list assignment `L` (via
  DsBatch/P02 `nine_bound`).
* `lambdaMax_eq_fourteen`: `λ_L = 14` for every 3-list assignment `L` (upper bound from
  `Finset.card_le_univ`; lower bound `14 ≤ λ_L` from a full colouring produced by
  DsBatch/P02 `choosable_three`).
* `lambdaMin_two_le_nine`, `fourteen_le_lambdaMin_three`: the two bounds on `λ_2`, `λ_3`,
  via `Nat.sInf_le` / `le_csInf`.
* `conjecture_refuted`: instantiate `conjecture` and contradict the rational inequality.

`DsBatch/P11/Statement.lean` also contains the bridge between P02's `ℕ`-list `Choosable`
predicate and atlas-lean's `ListColorable` over an arbitrary colour type
(`isListColorable_of_choosable`, `choosable_of_isListColorable`), the proof
`p02_isChoiceNumber : DsBatch.P02.G.IsChoiceNumber 3`, and the non-vacuity examples (the
14-vertex object, the genuine 2-list assignment with a 9-vertex partial colouring, and
`(⊥ : SimpleGraph (Fin 1)).IsChoiceNumber 1`).

## Size

* `DsBatch/P11/Defs.lean`: 109 lines (frozen)
* `DsBatch/P11/Statement.lean`: 124 lines (frozen)
* `DsBatch/P11/Main.lean`: 104 lines
* Total Lean: 337 lines

## Spend and wall time

* Spend: 0.823051 CNY (budget 3 CNY), 1 chunk.
* Wall time: 2026-11-05T21:59:42Z → 2026-11-05T22:08:03Z (about 8 minutes).

## Deviations, paper gaps and errors

* `papers/atlas-P02/` contains the atlas-lean sources (`PartialListColoringWanted.lean`,
  `ListColoring.lean`) and the Apache-2.0 `LICENSE`, not a TeX manuscript. The audit therefore
  checked fidelity against those Lean sources, which are the source of truth for this port.
* Because the `MathlibExt` import is dropped, the `ListColoring.lean` block is inlined before
  the `PartialListColoringWanted` namespace (Lean needs `SimpleGraph.IsChoiceNumber` declared
  before `conjecture` uses it). The definition bodies are unchanged; this is an ordering
  adaptation, not a change of content.
* The atlas line `public theorem_wanted conjecture_refuted : ¬ conjecture` is not copied: its
  `Batteries.Util.ProofWanted` macro and import are dropped, and the actual theorem
  `DsBatch.P11.conjecture_refuted` replaces it.
* No mathematical gap or error was found. The refutation is exactly the one recorded in the
  atlas source record: Noel's 14-vertex graph gives `λ_2/2 ≤ 9/2 < 14/3 = λ_3/3`.
