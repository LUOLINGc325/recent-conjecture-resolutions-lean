import Mathlib

/-!
# P05: Unipotence of a double commutator with transvections (arXiv 2609.17006)

Formal objects from I. Chinyere, *Unipotence of a double commutator with
transvections*.

The paper works with `V = R^n`, the general linear group `GL_n(R)` of invertible
`n × n` matrices over a nonzero commutative ring with identity, and rank-one
operators `u ⊗ f : x ↦ f(x) • u`.  We model `V` as `Fin n → R` and `GL_n(R)` as
`Matrix.GeneralLinearGroup (Fin n) R` (the units of the matrix ring).  A vector
`u : Fin n → R` is a column vector and a functional `f : Fin n → R` is a row
vector; then `f(u) = ∑ i, f i * u i = f ⬝ᵥ u`, and the rank-one operator
`u ⊗ f` is the matrix `vecMulVec u f`, with entries `(u ⊗ f) i j = u i * f j`.
-/

namespace DsBatch.P05

open Matrix

/-- Definition 2.1: the rank-one matrix `u ⊗ f`, with entries
`(u ⊗ f) i j = u i * f j`.  Applied to `x : V` it is the column vector
`f(x) • u`. -/
def rankOne {n : ℕ} {R : Type*} [Mul R] (u f : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.vecMulVec u f

/-- Definition 2.3: an element `τ ∈ GL_n(R)` is a transvection if
`τ = I_n + u ⊗ f` for some `u ∈ V` and `f ∈ V^*` with `f(u) = 0` and
`u ⊗ f ≠ 0`.  In matrix terms `f(u) = f ⬝ᵥ u`, and the equality with `I_n + u ⊗ f`
is an equality of matrices.  The condition `u ⊗ f ≠ 0` forces `τ ≠ I_n`. -/
def IsTransvection {n : ℕ} {R : Type*} [CommRing R] (τ : GL (Fin n) R) : Prop :=
  ∃ u f : Fin n → R, f ⬝ᵥ u = 0 ∧ rankOne u f ≠ 0 ∧
    (τ : Matrix (Fin n) (Fin n) R) = 1 + rankOne u f

end DsBatch.P05
