import DsBatch.P05.Defs

/-! Frozen specification for project P05. This file must stay sorry-free:
    state each target as `def <name>_statement : Prop := <type>` here and put
    the proof-carrying `theorem` in Main.lean.

    Target (queue scope, required part): the main theorem of arXiv 2609.17006
    over commutative rings, as stated (Theorem 2.9 of the paper). -/

namespace DsBatch.P05

open Matrix
open scoped commutatorElement

universe u

/-- Theorem 2.9 (the paper's main theorem).  Let `R` be a nonzero commutative
ring with identity, let `n ≥ 3`, and let `σ ∈ GL_n(R)`.  Then there exist
nonidentity transvections `τ₁, τ₂ ∈ GL_n(R)` such that
`[[σ, τ₁], τ₂] = I_n`, where `[g, h] = g h g⁻¹ h⁻¹`.

The commutator `⁅⁅σ, τ₁⁆, τ₂⁆` is Mathlib's `commutatorElement`, whose convention
is exactly `g * h * g⁻¹ * h⁻¹`. -/
def main_statement : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ), 3 ≤ n →
    ∀ σ : GL (Fin n) R,
      ∃ τ₁ τ₂ : GL (Fin n) R,
        IsTransvection τ₁ ∧ IsTransvection τ₂ ∧
        τ₁ ≠ 1 ∧ τ₂ ≠ 1 ∧
        ⁅⁅σ, τ₁⁆, τ₂⁆ = 1

/-! ## Non-vacuity checks

The hypotheses are satisfiable, the notion of transvection is neither empty nor
universal, and the conclusion of the main theorem is satisfiable (for `σ = 1`).
-/

/-- The hypotheses are satisfiable: `ℤ` is a nonzero commutative ring with
identity and `n = 3 ≥ 3`. -/
example : Nontrivial ℤ ∧ (3 : ℕ) ≤ 3 := ⟨inferInstance, by norm_num⟩

/-- The first two standard basis vectors of `ℤ³`. -/
def e₀ : Fin 3 → ℤ := Pi.single 0 1

def e₁ : Fin 3 → ℤ := Pi.single 1 1

/-- `e₀ ⊗ e₁` squares to zero (since `e₁(e₀) = 0`). -/
lemma rankOne_e₀_e₁_sq : rankOne e₀ e₁ * rankOne e₀ e₁ = 0 := by
  rw [rankOne, vecMulVec_mul_vecMulVec]
  simp [e₀, e₁, dotProduct, Fin.sum_univ_three]

/-- The transvection `I₃ + e₀ ⊗ e₁` over `ℤ`. -/
def exTransvection : GL (Fin 3) ℤ where
  val := 1 + rankOne e₀ e₁
  inv := 1 - rankOne e₀ e₁
  val_inv := by
    calc (1 + rankOne e₀ e₁) * (1 - rankOne e₀ e₁)
        = (1 + rankOne e₀ e₁) * 1 - (1 + rankOne e₀ e₁) * rankOne e₀ e₁ := by
          rw [mul_sub]
      _ = (1 + rankOne e₀ e₁) - (rankOne e₀ e₁ + rankOne e₀ e₁ * rankOne e₀ e₁) := by
          rw [mul_one, add_mul, one_mul]
      _ = 1 := by rw [rankOne_e₀_e₁_sq]; noncomm_ring
  inv_val := by
    calc (1 - rankOne e₀ e₁) * (1 + rankOne e₀ e₁)
        = (1 - rankOne e₀ e₁) * 1 + (1 - rankOne e₀ e₁) * rankOne e₀ e₁ := by
          rw [mul_add]
      _ = (1 - rankOne e₀ e₁) + (rankOne e₀ e₁ - rankOne e₀ e₁ * rankOne e₀ e₁) := by
          rw [mul_one, sub_mul, one_mul]
      _ = 1 := by rw [rankOne_e₀_e₁_sq]; noncomm_ring

/-- The explicit matrix is a transvection in the sense of Definition 2.3, with
direction vector `e₀` and functional `e₁`. -/
lemma exTransvection_isTransvection : IsTransvection exTransvection := by
  refine ⟨e₀, e₁, ?_, ?_, rfl⟩
  · simp [e₀, e₁, dotProduct, Fin.sum_univ_three]
  · intro h0
    have h01 : rankOne e₀ e₁ (0 : Fin 3) (1 : Fin 3) =
        (0 : Matrix (Fin 3) (Fin 3) ℤ) (0 : Fin 3) (1 : Fin 3) := by rw [h0]
    simp [rankOne, vecMulVec_apply, e₀, e₁] at h01

/-- A transvection is not the identity (the condition `u ⊗ f ≠ 0` in
Definition 2.3). -/
lemma IsTransvection.ne_one {n : ℕ} {R : Type*} [CommRing R] {τ : GL (Fin n) R}
    (h : IsTransvection τ) : τ ≠ 1 := by
  obtain ⟨u, f, _hfu, hne, hval⟩ := h
  intro hτ
  have hmat : (τ : Matrix (Fin n) (Fin n) R) = ((1 : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
    rw [hτ]
  rw [hval] at hmat
  have h0 : rankOne u f = 0 := by
    have h1 : (1 : Matrix (Fin n) (Fin n) R) + rankOne u f = 1 + 0 := by
      simpa using hmat
    exact add_left_cancel h1
  exact hne h0

/-- `IsTransvection` is not trivially true: the identity is not a transvection. -/
example : ¬ IsTransvection (1 : GL (Fin 3) ℤ) := by
  intro h
  exact h.ne_one rfl

/-- `IsTransvection` is not trivially false: the explicit `I₃ + e₀ ⊗ e₁` is one. -/
example : IsTransvection exTransvection := exTransvection_isTransvection

/-- The conclusion of the main theorem is satisfiable: for `σ = I₃` and
`τ₁ = τ₂ = I₃ + e₀ ⊗ e₁` the double commutator equals the identity. -/
example :
    ∃ τ₁ τ₂ : GL (Fin 3) ℤ,
      IsTransvection τ₁ ∧ IsTransvection τ₂ ∧ τ₁ ≠ 1 ∧ τ₂ ≠ 1 ∧
        ⁅⁅(1 : GL (Fin 3) ℤ), τ₁⁆, τ₂⁆ = 1 :=
  ⟨exTransvection, exTransvection, exTransvection_isTransvection,
    exTransvection_isTransvection, exTransvection_isTransvection.ne_one,
    exTransvection_isTransvection.ne_one, by simp [Bracket.bracket]⟩

end DsBatch.P05
