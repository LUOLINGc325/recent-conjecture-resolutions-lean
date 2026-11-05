import Mathlib

/-!
# P04: Counterexamples to Dujella's conjecture on integral points (arXiv 2608.22635)

Objects from A. Jurasić and M. Jurasić, *Counterexamples to Dujella's conjecture on
integral points on the elliptic curve attached to a Diophantine triple*.

A **Diophantine triple** is a set `{a,b,c}` of distinct positive integers such that
`a*b+1`, `a*c+1` and `b*c+1` are perfect squares.  To such a triple one attaches the
(elliptic) curve

`E_{a,b,c} : y^2 = (a*x+1)(b*x+1)(c*x+1)`.

If `r^2 = a*b+1`, `s^2 = a*c+1`, `t^2 = b*c+1`, the two **regular extension values**
are `d_± = a+b+c+2*a*b*c ± 2*r*s*t`.  Dujella's Conjecture 1.4.5 predicts that the
only integral `x`-coordinates on `E_{a,b,c}` are `0`, `d_-` and `d_+`, together with
`-1` when the triple contains `1`.  Problem 4.8 of Dujella's open problem list asks
the weaker question whether every integral point with `x ≠ -1` makes `a*x+1`,
`b*x+1`, `c*x+1` all perfect squares.

The paper constructs, among others, the explicit triple `{5, 115, c_15}` and the
integral point `(x_15, ±y_15)` on its curve at which none of the three factors is a
square.  The concrete data are defined at the end of this file.
-/

namespace DsBatch.P04

/-- A set `{a,b,c}` of integers is a **Diophantine triple** when its members are
distinct and positive and the three pairwise products plus one are perfect squares. -/
def IsDiophantineTriple (a b c : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    IsSquare (a * b + 1) ∧ IsSquare (a * c + 1) ∧ IsSquare (b * c + 1)

/-- `r`, `s`, `t` are the positive square roots attached to the Diophantine triple
`{a,b,c}`, i.e. `r^2 = a*b+1`, `s^2 = a*c+1`, `t^2 = b*c+1`. -/
def IsRootTriple (a b c r s t : ℤ) : Prop :=
  0 < r ∧ 0 < s ∧ 0 < t ∧ r * r = a * b + 1 ∧ s * s = a * c + 1 ∧ t * t = b * c + 1

/-- `(x, y)` is an **integral point** on the curve
`E_{a,b,c} : y^2 = (a*x+1)(b*x+1)(c*x+1)`. -/
def OnCurve (a b c x y : ℤ) : Prop :=
  y ^ 2 = (a * x + 1) * (b * x + 1) * (c * x + 1)

/-- The two **regular extension values**
`d_± = a+b+c+2*a*b*c ± 2*r*s*t`, where `r`, `s`, `t` are the square roots of
`a*b+1`, `a*c+1`, `b*c+1`.  The first component is `d_-`, the second is `d_+`. -/
def regularExtensions (a b c r s t : ℤ) : ℤ × ℤ :=
  (a + b + c + 2 * a * b * c - 2 * (r * s * t),
   a + b + c + 2 * a * b * c + 2 * (r * s * t))

/-- Dujella's Conjecture 1.4.5 for a fixed triple: every integral `x`-coordinate on
`E_{a,b,c}` is `0`, `d_-` or `d_+`, and also `-1` when `1` belongs to the triple. -/
def DujellaConjectureAt (a b c r s t : ℤ) : Prop :=
  ∀ x y : ℤ, OnCurve a b c x y →
    x = 0 ∨ x = (regularExtensions a b c r s t).1 ∨
      x = (regularExtensions a b c r s t).2 ∨ ((a = 1 ∨ b = 1 ∨ c = 1) ∧ x = -1)

/-- Problem 4.8 of Dujella's open problem list for a fixed triple: every integral
point on `E_{a,b,c}` with `x ≠ -1` makes `a*x+1`, `b*x+1`, `c*x+1` all perfect
squares. -/
def Problem48At (a b c : ℤ) : Prop :=
  ∀ x y : ℤ, OnCurve a b c x y → x ≠ -1 →
    IsSquare (a * x + 1) ∧ IsSquare (b * x + 1) ∧ IsSquare (c * x + 1)

/-! ## The paper's smallest explicit counterexample (the case `k = 15`)

The four integers below are the paper's `c_15`, `S_15`, `T_15` and `x_15`; the value
`y_15 = c_15 * x_15 + 1` is the positive ordinate of the point. -/

/-- The paper's `c_15`. -/
def c15 : ℤ := 19726599787079129775103071759543738099950374011720

/-- The paper's `S_15`, with `5 * c_15 + 1 = S_15^2`. -/
def S15 : ℤ := 9931414749943516928215699

/-- The paper's `T_15`, with `115 * c_15 + 1 = T_15^2`. -/
def T15 : ℤ := 47629391928872028421837349

/-- The paper's `x_15`, with `c_15 = 575 * x_15 + 120`. -/
def x15 : ℤ := 34307130064485443087135776973119544521652824368

/-- The paper's positive ordinate `y_15 = c_15 * x_15 + 1`. -/
def y15 : ℤ := c15 * x15 + 1

end DsBatch.P04
