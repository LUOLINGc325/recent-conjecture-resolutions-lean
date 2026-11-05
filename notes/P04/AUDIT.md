PASS

# Fidelity audit: P04 (arXiv 2608.22635)

Verdict: **PASS**. The statement `DsBatch.P04.counterexample_statement` faithfully
captures the required queue scope — the paper's smallest explicit case `k = 15` — and
the definitions match the paper. The theorem is proved with only the allowed axioms,
and the numerical data are correct.

## 1. Definitions vs the paper

All definitions live in `DsBatch/P04/Defs.lean` over `ℤ` with explicit positivity, as is
standard for these problems.

- `IsDiophantineTriple a b c` = `0<a ∧ 0<b ∧ 0<c ∧ a≠b ∧ a≠c ∧ b≠c ∧ IsSquare(a*b+1) ∧ IsSquare(a*c+1) ∧ IsSquare(b*c+1)`.
  Matches "a set {a,b,c} of distinct positive integers such that ab+1, ac+1, bc+1 are
  perfect squares" (abstract + intro). `IsSquare` on `ℤ` is exactly "∃ r, r*r = m".
- `OnCurve a b c x y` = `y^2 = (a*x+1)*(b*x+1)*(c*x+1)`. Matches eq. (1) `E_{a,b,c}`.
- `IsRootTriple a b c r s t` = positive `r,s,t` with `r^2=ab+1`, `s^2=ac+1`, `t^2=bc+1`.
  Matches the paper's `r^2=ab+1`, `s^2=ac+1`, `t^2=bc+1` (positive square roots).
- `regularExtensions a b c r s t` = `(a+b+c+2abc − 2rst, a+b+c+2abc + 2rst)`.
  First component is `d_-`, second is `d_+` — matches eq. (2) `d_± = a+b+c+2abc ± 2√(...)`.
  For `a=5,b=115`: `a+b+c+2abc = 120+1151c` and `2rst = 2·24·S·T = 48ST`, matching the
  paper's "d_± = 120 + 1151c ± 48ST".
- `DujellaConjectureAt a b c r s t` = ∀x y, `OnCurve` → `x=0 ∨ x=d_- ∨ x=d_+ ∨ ((a=1 ∨ b=1 ∨ c=1) ∧ x=-1)`.
  Matches Conjecture 1.4.5: the only integral x-coordinates are `0`, `d_-`, `d_+`, "together
  with -1 when the triple contains 1".
- `Problem48At a b c` = ∀x y, `OnCurve` → `x ≠ -1` → all three of `ax+1, bx+1, cx+1` are squares.
  Matches Problem 4.8.

No weakening, no added hypothesis, no Prop-typed data field, no `True` placeholder, no
degenerate/constant definition. The roots `r,s,t` are passed as explicit parameters to
`DujellaConjectureAt`; the statement instantiates them with the correct `24, S15, T15`.

## 2. The explicit constants (k = 15)

Definitions in `Defs.lean` match Section 4 and eq. (3.1) (`y_k = c_k x_k + 1`) of the paper
digit-for-digit:

- `c15 = 19726599787079129775103071759543738099950374011720`
- `S15 = 9931414749943516928215699`
- `T15 = 47629391928872028421837349`
- `x15 = 34307130064485443087135776973119544521652824368`
- `y15 = c15*x15 + 1`

Independently verified with Python (all hold):
- `5*115+1 = 576 = 24^2`
- `5*c15+1 = S15^2 = 98632998935395648875515358797718690499751870058601`
- `115*c15+1 = T15^2`
- `c15 = 575*x15 + 120` (so `x15 = (c15−120)/575`)
- `y15 = c15*x15 + 1 = 676763024625374553353727805340922262877605894543645958977994892519160014502019539531684733592961`
- `y15^2 = (5*x15+1)*(115*x15+1)*(c15*x15+1)` (both sides 192 digits)
- `x15 > 0`, `y15 > 0`, `x15 ≠ 0`, `x15 ≠ -1`
- `d_- = 120+1151*c15 − 48*S15*T15 = 8569332541111894343538801554602513003703076192`
- `d_+ = 120+1151*c15 + 48*S15*T15 = 45410624140523615630392927651668130503572757271903488`
  Both equal the paper's decimal values in eq. (4.x), and `0 < d_- < x15 < d_+`, so
  `x15 ∉ {0, -1, d_-, d_+}`.

## 3. `counterexample_statement` scope

```
IsDiophantineTriple 5 115 c15 ∧ IsRootTriple 5 115 c15 24 S15 T15 ∧
OnCurve 5 115 c15 x15 y15 ∧ 0 < x15 ∧ 0 < y15 ∧ x15 ≠ -1 ∧
¬ IsSquare (5*x15+1) ∧ ¬ IsSquare (115*x15+1) ∧ ¬ IsSquare (c15*x15+1) ∧
¬ Problem48At 5 115 c15 ∧ ¬ DujellaConjectureAt 5 115 c15 24 S15 T15
```

This is exactly the required scope: one explicit Diophantine triple + integral point, with
`x ≠ -1`, none of the three factors a square (Problem 4.8 answered negatively), and `x` not in
`{0, d_-, d_+}` (Conjecture 1.4.5 refuted). `¬ Problem48At` and `¬ DujellaConjectureAt` are
the genuine negations of the paper's claims; the proof in `Main.lean` derives them from the
explicit point `(x15, y15)` (for Problem 4.8: `not_square_5x15 (h x15 y15 onCurve15 …).1`; for
Dujella: case split on the four disjuncts, discharged by `x15≠0`, `x15≠d_-`, `x15≠d_+`, `x15≠-1`).
Mild redundancy: the three individual nonsquares + `OnCurve` + `x15≠-1` already imply
`¬ Problem48At`, and the same data imply `¬ DujellaConjectureAt`; this is harmless — it does
not weaken the claim, only makes the counterexample's data explicit.

## 4. Non-vacuity (`Statement.lean` examples)

All compile (the file is imported by `Main.lean`, and `lake build DsBatch` succeeds). They
are genuine kernel computations, not circular:
- `(24:ℤ)*24 = 5*115+1` — the pair is Diophantine.
- `IsDiophantineTriple 5 115 c15` — the explicit triple satisfies the hypotheses.
- `IsRootTriple 5 115 c15 24 S15 T15` — the roots satisfy `r^2=ab+1` etc.
- `OnCurve 5 115 c15 x15 y15` — the explicit point is on the curve.
- `0 < x15 ∧ 0 < y15`, `x15 ≠ -1` — positivity/excluded value.
- `¬ IsSquare (5*x15+1)` via `ZMod 7` (value 3) — nonsquare condition is satisfiable (not trivially false).
- `IsSquare (5*0+1)` — `IsSquare` is not trivially false.
- `IsDiophantineTriple 1 3 8` — the notion is non-vacuous.
- `OnCurve 1 3 8 0 1` — the curve/point notion is non-vacuous.
- `c15 = 575*x15+120` — the integrality relation of Proposition 2.1.

There is no example asserting `DujellaConjectureAt`/`Problem48At` is satisfiable for *some*
triple; that is a minor gap in "property not trivially false" coverage, not a fidelity defect,
because both are faithful universal statements and their negations are established constructively
by the explicit point.

## 5. Hygiene

- `infra/scan.py DsBatch/P04 projects/P04` → `[]` (the scanner strips comments/strings; the word
  "sorry" occurs only in a docstring comment, which is correctly not a `sorry` token).
- `lake build DsBatch` → "Build completed successfully".
- Target check: `example : DsBatch.P04.counterexample_statement := DsBatch.P04.counterexample`
  compiles, and `#print axioms DsBatch.P04.counterexample` = `[propext, Classical.choice, Quot.sound]`
  ⊆ allowed set.
- `project.json` target `{"name": "DsBatch.P04.counterexample", "lean_type": "DsBatch.P04.counterexample_statement"}`
  matches the theorem name and statement type exactly.

## 6. Independent verification of the nonsquare certificates (`Main.lean`)

- Lemma `not_isSquare_of_zmod` and `isSquare_intCast` are correct (cast of a square is a square;
  contrapositive gives the nonsquare test).
- `(5*x15+1) mod 7 = 3`; squares mod 7 are {0,1,2,4}, so 3 is a quadratic nonresidue. ✓
- `(115*x15+1) mod 7 = 5`; 5 ∉ {0,1,2,4}, so 5 is a quadratic nonresidue. ✓
- `(c15*x15+1) mod 13 = 11`; squares mod 13 are {0,1,3,4,9,10,12}, so 11 is a quadratic nonresidue. ✓
- Cross-check against the paper's own certificates: `5x15+1 ≡ 115x15+1 ≡ 10 (mod 11)` and
  `c15*x15+1 ≡ 1235 (mod 2851)` — both reproduced, consistent with the paper.

The proofs of `¬ Problem48At` and `¬ DujellaConjectureAt` use the explicit point `(x15, y15)`
with `onCurve15` and reach a contradiction as described in section 3 above.

## Minor issues (all acceptable, none blocking)

1. Redundancy in `counterexample_statement` (the negative answers follow from the explicit data) — harmless.
2. No non-vacuity example that `DujellaConjectureAt`/`Problem48At` hold for some triple — cosmetic.
3. `import Mathlib` without a `module` header produces a benign build warning (P01–P03 identical).

No MUST-FIX defects found.
