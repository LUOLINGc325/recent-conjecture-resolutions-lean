import DsBatch.P04.Defs

/-! Frozen specification for project P04. This file must stay sorry-free:
    state each target as `def <name>_statement : Prop := <type>` here and put
    the proof-carrying `theorem` in Main.lean.

    Target (queue scope, required part): one explicit Diophantine triple and integral
    point refuting Dujella's Conjecture 1.4.5 and answering Problem 4.8 negatively,
    namely the paper's smallest explicit case `k = 15` of Theorem 3.1. -/

namespace DsBatch.P04

/-! ## Target statement -/

/-- The paper's smallest explicit counterexample: `{5, 115, c_15}` is a Diophantine
triple with square roots `24`, `S_15`, `T_15`, `(x_15, y_15)` is an integral point on
`E_{5,115,c_15}` with `x_15 ≠ -1`, none of `5*x_15+1`, `115*x_15+1`, `c_15*x_15+1` is
a perfect square, and consequently both Problem 4.8 and Dujella's Conjecture 1.4.5
(of which the regular extension values `d_±` are formed from `24`, `S_15`, `T_15`)
fail for this triple. -/
def counterexample_statement : Prop :=
  IsDiophantineTriple 5 115 c15 ∧
  IsRootTriple 5 115 c15 24 S15 T15 ∧
  OnCurve 5 115 c15 x15 y15 ∧
  0 < x15 ∧ 0 < y15 ∧
  x15 ≠ -1 ∧
  ¬ IsSquare (5 * x15 + 1) ∧
  ¬ IsSquare (115 * x15 + 1) ∧
  ¬ IsSquare (c15 * x15 + 1) ∧
  ¬ Problem48At 5 115 c15 ∧
  ¬ DujellaConjectureAt 5 115 c15 24 S15 T15

/-! ## Non-vacuity checks

The paper's explicit objects exist, satisfy the hypotheses, and the properties used
in the statement are not trivial.
-/

/-- The image in `ZMod n` of an integral square is a square. -/
lemma isSquare_intCast {m : ℤ} {n : ℕ} (h : IsSquare m) : IsSquare (m : ZMod n) := by
  rcases h with ⟨k, hk⟩
  exact ⟨(k : ZMod n), by rw [hk]; push_cast; ring⟩

/-- `{5, 115}` is a Diophantine pair: `5 * 115 + 1 = 24^2`. -/
example : (24 : ℤ) * 24 = 5 * 115 + 1 := by norm_num

/-- The explicit triple `{5, 115, c_15}` is Diophantine. -/
example : IsDiophantineTriple 5 115 c15 := by
  refine ⟨by norm_num, by norm_num, by norm_num [c15], by norm_num, by norm_num [c15],
    by norm_num [c15], ?_, ?_, ?_⟩
  · exact ⟨24, by norm_num⟩
  · exact ⟨S15, by norm_num [S15, c15]⟩
  · exact ⟨T15, by norm_num [T15, c15]⟩

/-- The explicit roots `24`, `S_15`, `T_15` satisfy the root relations. -/
example : IsRootTriple 5 115 c15 24 S15 T15 := by
  refine ⟨by norm_num, by norm_num [S15], by norm_num [T15], by norm_num, ?_, ?_⟩
  · norm_num [S15, c15]
  · norm_num [T15, c15]

/-- `(x_15, y_15)` is an integral point on the curve `E_{5,115,c_15}`. -/
example : OnCurve 5 115 c15 x15 y15 := by
  norm_num [OnCurve, y15, c15, x15]

/-- The point has positive coordinates. -/
example : 0 < x15 ∧ 0 < y15 := by
  constructor <;> norm_num [y15, c15, x15]

/-- The nonsquare condition is satisfiable at the explicit point (so it is not
trivially false). -/
example : ¬ IsSquare (5 * x15 + 1) := by
  intro h
  have h7 : IsSquare ((5 * x15 + 1 : ℤ) : ZMod 7) := isSquare_intCast h
  have hval : ((5 * x15 + 1 : ℤ) : ZMod 7) = 3 := by decide
  rw [hval] at h7
  exact absurd h7 (by decide)

/-- `IsSquare` is not trivially false: `1` is a square. -/
example : IsSquare (5 * (0 : ℤ) + 1) := ⟨1, by norm_num⟩

/-- The notion of a Diophantine triple is not vacuous: `{1, 3, 8}` is a Diophantine
triple. -/
example : IsDiophantineTriple 1 3 8 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    ?_, ?_, ?_⟩
  · exact ⟨2, by norm_num⟩
  · exact ⟨3, by norm_num⟩
  · exact ⟨5, by norm_num⟩

/-- The curve and the notion of an integral point are not vacuous: `(0, 1)` lies on
`E_{1,3,8}`. -/
example : OnCurve 1 3 8 0 1 := by norm_num [OnCurve]

/-- `x_15` is the integral value `(c_15 - 120) / 575` of Proposition 2.1. -/
example : c15 = 575 * x15 + 120 := by norm_num [c15, x15]

/-- `x_15` is not the excluded value `-1`. -/
example : x15 ≠ -1 := by norm_num [x15]

end DsBatch.P04
