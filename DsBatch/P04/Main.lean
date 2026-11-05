import DsBatch.P04.Statement

/-! Proofs for project P04: the paper's smallest explicit counterexample (`k = 15`).

The arithmetic identities are checked by kernel computation (`norm_num`); the three
nonsquare statements use quadratic nonresidues modulo `7` and `13`, exactly in the
spirit of the modular certificates in the paper (which uses `11` and `2851`). -/

namespace DsBatch.P04

/-- If an integer is not a square modulo `p`, then it is not a square in `ℤ`. -/
lemma not_isSquare_of_zmod {m : ℤ} {p : ℕ} (h : ¬ IsSquare (m : ZMod p)) : ¬ IsSquare m :=
  fun hm => h (isSquare_intCast hm)

/-- `5 * x_15 + 1 ≡ 3 (mod 7)`, and `3` is a quadratic nonresidue modulo `7`. -/
lemma not_square_5x15 : ¬ IsSquare (5 * x15 + 1) := by
  apply not_isSquare_of_zmod (p := 7)
  have hval : ((5 * x15 + 1 : ℤ) : ZMod 7) = 3 := by decide
  rw [hval]
  decide

/-- `115 * x_15 + 1 ≡ 5 (mod 7)`, and `5` is a quadratic nonresidue modulo `7`. -/
lemma not_square_115x15 : ¬ IsSquare (115 * x15 + 1) := by
  apply not_isSquare_of_zmod (p := 7)
  have hval : ((115 * x15 + 1 : ℤ) : ZMod 7) = 5 := by decide
  rw [hval]
  decide

/-- `c_15 * x_15 + 1 ≡ 11 (mod 13)`, and `11` is a quadratic nonresidue modulo `13`. -/
lemma not_square_c15x15 : ¬ IsSquare (c15 * x15 + 1) := by
  apply not_isSquare_of_zmod (p := 13)
  have hval : ((c15 * x15 + 1 : ℤ) : ZMod 13) = 11 := by decide
  rw [hval]
  decide

/-- The explicit point lies on the curve `E_{5,115,c_15}`. -/
lemma onCurve15 : OnCurve 5 115 c15 x15 y15 := by
  norm_num [OnCurve, y15, c15, x15]

/-- `x_15` is not the lower regular extension value `d_-`. -/
lemma x15_ne_dMinus : x15 ≠ (regularExtensions 5 115 c15 24 S15 T15).1 := by
  norm_num [regularExtensions, c15, S15, T15, x15]

/-- `x_15` is not the upper regular extension value `d_+`. -/
lemma x15_ne_dPlus : x15 ≠ (regularExtensions 5 115 c15 24 S15 T15).2 := by
  norm_num [regularExtensions, c15, S15, T15, x15]

/-- The paper's smallest explicit counterexample. -/
theorem counterexample : counterexample_statement := by
  unfold counterexample_statement
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `{5, 115, c_15}` is a Diophantine triple
    refine ⟨by norm_num, by norm_num, by norm_num [c15], by norm_num, by norm_num [c15],
      by norm_num [c15], ?_, ?_, ?_⟩
    · exact ⟨24, by norm_num⟩
    · exact ⟨S15, by norm_num [S15, c15]⟩
    · exact ⟨T15, by norm_num [T15, c15]⟩
  · -- the roots `24, S_15, T_15` satisfy the root relations
    refine ⟨by norm_num, by norm_num [S15], by norm_num [T15], by norm_num, ?_, ?_⟩
    · norm_num [S15, c15]
    · norm_num [T15, c15]
  · -- the point lies on the curve
    exact onCurve15
  · -- `x_15 > 0`
    norm_num [x15]
  · -- `y_15 > 0`
    norm_num [y15, c15, x15]
  · -- `x_15 ≠ -1`
    norm_num [x15]
  · -- `5 * x_15 + 1` is not a square
    exact not_square_5x15
  · -- `115 * x_15 + 1` is not a square
    exact not_square_115x15
  · -- `c_15 * x_15 + 1` is not a square
    exact not_square_c15x15
  · -- Problem 4.8 fails for this triple
    intro h
    unfold Problem48At at h
    exact not_square_5x15 (h x15 y15 onCurve15 (by norm_num [x15])).1
  · -- Dujella's Conjecture 1.4.5 fails for this triple
    intro h
    unfold DujellaConjectureAt at h
    rcases h x15 y15 onCurve15 with h0 | h1 | h2 | ⟨_, hneg⟩
    · norm_num [x15] at h0
    · exact x15_ne_dMinus h1
    · exact x15_ne_dPlus h2
    · exact (by norm_num [x15] : x15 ≠ -1) hneg

end DsBatch.P04
