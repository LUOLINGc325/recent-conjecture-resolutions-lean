PASS

# Fidelity audit — P02 (arXiv 2609.23291, Noel, "The Partial List Colouring Conjecture is False")

Audited against the paper `papers/2609.23291/PLCC.tex`, `TASK.md` (queue scope) and
`AGENTS.md` (frozen statements, faithful definitions, non-vacuity). Build:
`lake build DsBatch.P02.Statement` succeeds; `infra/scan.py` on
`DsBatch/P02/{Defs,Statement}.lean` returns `[]` (no forbidden tokens).

## 1. The graph `G` — faithful

`V` has exactly 14 vertices (`s1`, `s2`, and `u/v/p : Fin 4 → V`), and
`example : Fintype.card V = 14 := by decide` passes. The encoding matches the paper:

- `s1`, `s2` are the terminals; `adjB` makes them non-adjacent (`s1–s2 = false`), adjacent to
  `u i` and `v i` for every `i`, and non-adjacent to every private `p i`.
- `{u i, v i, p i}` is a triangle: `u–v`, `u–p`, `v–p` are `decide (i = j)` (true iff same `i`).
- No cross-triangle edges (`u–u`, `v–v`, `p–p` all false; `u i`–`v j`, `u i`–`p j`,
  `v i`–`p j` true iff `i = j`). The four triangles are pairwise disjoint.
- `adjB` is symmetric and loopless, so `G : SimpleGraph V` is well-formed.

Non-vacuity examples confirm the clique property (`∀ i, ∀ a ∈ T i, ∀ b ∈ T i, a ≠ b → G.Adj a b`)
and the partition (`∀ v, v ∈ allTriangles ↔ v ≠ s1 ∧ v ≠ s2`), i.e. the terminals are exactly the
vertices outside the four triangles. No edges are missing and none are added.

## 2. The 2-list assignment `L` — faithful

`L` maps to `Finset ℕ`; `example : IsListAssignment L 2` passes (every list has card 2).
The relabelling paper `1,2,3,4 ↦ 0,1,2,3` is structure-preserving exactly:

| paper        | encoded   | definition              |
|--------------|-----------|-------------------------|
| L(s1)={1,2}  | {0,1}     | `.s1 => {0,1}`          |
| L(s2)={3,4}  | {2,3}     | `.s2 => {2,3}`          |
| T1={1,3}     | {0,2}     | `listOf 0 = {0,2}`      |
| T2={1,4}     | {0,3}     | `listOf 1 = {0,3}`      |
| T3={2,3}     | {1,2}     | `listOf 2 = {1,2}`      |
| T4={2,4}     | {1,3}     | `listOf 3 = {1,3}`      |

Each triangle's three vertices share the common list (`example : ∀ i, ∀ a ∈ T i, L a = listOf i`),
and the four lists are exactly the four size-2 lists taking one colour from `L(s1)` and one from
`L(s2)`, as in the paper. The "one from s1, one from s2" pairing survives the relabelling.

## 3. List chromatic number exactly 3 — faithful

`ListChromaticNumberEq G 3 := Choosable G 3 ∧ ∀ j, j < 3 → ¬ Choosable G j`, with
`Choosable G k := ∀ L, IsListAssignment L k → ListColorable G L` and
`IsListAssignment L k := ∀ v, (L v).card = k` (lists over `ℕ`, exactly `k` colours).
This is the standard "least k such that G is k-choosable" formulation, i.e. choice number exactly
3: 3-choosable and not j-choosable for any j < 3 (j = 0, 1, 2). Faithful to "list chromatic number
equal to 3"; lists over `ℕ` as required.

## 4. "At most 9 vertices colourable from L" — faithful

`∀ (S : Finset V) (c : V → ℕ), IsPartialListColoring G L S c → S.card ≤ 9`, where
`IsPartialListColoring` requires every coloured vertex's colour to lie in its own list and adjacent
coloured vertices to differ. This is exactly "no partial proper L-colouring colours more than 9
vertices". The bound is sharp, not a vacuous upper bound: `S9`/`c9` give a genuine proper partial
L-colouring of 9 distinct vertices (verified by `decide` in
`example : IsPartialListColoring G L S9 c9`), and `example : S9.card = 9` passes. Manually
re-checked: terminals s1↦0, s2↦2 are non-adjacent and differ from every coloured non-private
neighbour; each coloured triangle contributes a valid pair with distinct colours; list membership
holds for all nine vertices.

## 5. The Partial List Colouring Conjecture — faithful

`PartialListColouringConjecture` is quantified over every finite type `W` (with `[Fintype W]` and
`[DecidableEq W]`, the latter only to make Finset membership decidable in the colouring predicate —
not an added mathematical hypothesis, and every finite type admits it), every `SimpleGraph G`, every
`k, ℓ : ℕ` with `2 ≤ k`, `1 ≤ ℓ`, `ℓ < k`, `ListChromaticNumberEq G k`, and every `ℓ`-list
assignment `L`; the conclusion is `∃ S c, IsPartialListColoring G L S c ∧ Fintype.card W * ℓ ≤ k * S.card`.
The integer form `n·ℓ ≤ k·|S|` is equivalent (since k ≥ 2 > 0) to `|S| ≥ n·ℓ/k`, matching the
paper's "at least n(ℓ/k) vertices". This is the conjecture of Albertson–Grossman–Haas verbatim.

`plcc_false_statement := ¬ PartialListColouringConjecture` is the correct corollary of Theorem 1:
the counterexample gives n = 14, k = 3, ℓ = 2, with 14·2 = 28 > 3·9 = 27, so the conjecture's
conclusion (28 ≤ 3·|S|, i.e. |S| ≥ 10) fails for this instance.

## 6. Scope — no more, no less

`counterexample_statement` is exactly the queue scope: `Fintype.card V = 14 ∧
ListChromaticNumberEq G 3 ∧ IsListAssignment L 2 ∧ (∀ S c, IsPartialListColoring G L S c →
S.card ≤ 9)`. No hypotheses added, none weakened, no conclusion assumed.
`plcc_false_statement` is exactly "the conjecture is false". `project.json` targets
`DsBatch.P02.{counterexample,plcc_false}` with `lean_type`
`DsBatch.P02.{counterexample,plcc_false}_statement` match the stubs in `Main.lean` exactly.

## 7. Non-vacuity — valid and meaningful

- Explicit object exists: `Fintype.card V = 14` and `IsListAssignment L 2` (decide).
- The "at most 9" bound is attained by the explicit 9-vertex colouring `S9`/`c9` (decide), so the
  predicate is not trivially true and the bound is not vacuous.
- `Choosable` is shown non-vacuously-false (edgeless `Fin 2` is 1-choosable) and non-vacuously-true
  (complete `Fin 2` is not 1-choosable).
- `IsPartialListColoring` is shown non-vacuous in both directions (empty colouring is valid; a colour
  outside the list is invalid).
- All `example`s are `sorry`-free and compile.

## 8. Degenerate / unused definitions

None that affect the targets. Minor note: `terminals : Finset V` (Defs.lean:103) is defined but
never referenced by any statement or example (the partition check uses `v ≠ s1 ∧ v ≠ s2` directly).
It is correct and harmless, not vacuous; only unused. Does not affect fidelity.

## Verdict

The statements and definitions are faithful to the paper. No changes required.
