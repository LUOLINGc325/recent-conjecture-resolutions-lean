PASS

Fidelity audit of DsBatch/P05 against the paper `papers/2609.17006/TrivTrans.tex`.

Note on numbering: the paper numbers all theorem-like environments from one shared counter
within each section (TrivTrans.tex lines 18-23). In Section 2 the objects are: rank-one
operator = Definition 2.1 (`def:rankone`, lines 104-106), transvection = Definition 2.3
(`def:transvection`, lines 126-128), unipotent = Definition 2.6 (`def:unipotent`, lines
143-145), functional lemma = Lemma 2.7 (`lem:functional`, lines 149-155), and the main
theorem = Theorem 2.9 (`\label{main}`, lines 161-163). The Lean doc-comments (and the audit
prompt) cite "Theorem 2.12", "Definition 2.6/2.7", "Lemma 2.9/2.10"; these reference numbers
are off, but they are comment-only and the definitions/theorem are transcribed by content,
so fidelity is unaffected.

1. `main_statement` (Statement.lean:24-30) matches the paper's main theorem (lines 161-163,
   restated in the abstract lines 65-68).
   - Quantifiers: `∀ R [CommRing R] [Nontrivial R], ∀ n, 3 ≤ n → ∀ σ : GL (Fin n) R` =
     "R a nonzero commutative ring with identity, n ≥ 3, σ ∈ GL_n(R)". `CommRing` is a
     unital commutative ring; `Nontrivial R` is exactly "nonzero" (0 ≠ 1). No extra
     hypothesis (no `IsDomain`, `NoZeroDivisors`, `Field`, unimodularity).
   - Conclusion: `∃ τ₁ τ₂, IsTransvection τ₁ ∧ IsTransvection τ₂ ∧ τ₁ ≠ 1 ∧ τ₂ ≠ 1 ∧
     ⁅⁅σ,τ₁⁆,τ₂⁆ = 1` = "nonidentity transvections τ₁, τ₂ with [[σ,τ₁],τ₂] = I_n".
     The `τᵢ ≠ 1` clauses are redundant (IsTransvection ⇒ ne_one is proved at
     Statement.lean:83-94) but express the paper's "nonidentity" verbatim; both τ₁ and τ₂
     are required nonidentity as in the paper.
   - Commutator convention: `⁅g,h⁆` is Mathlib `commutatorElement`, definitionally
     `g * h * g⁻¹ * h⁻¹` (verified via `#print`), identical to the paper's `[g,h]=ghg⁻¹h⁻¹`
     (line 74). No restatement of the conclusion as a hypothesis.

2. `IsTransvection` (Defs.lean:32-34) matches Definition `def:transvection` (lines 126-128):
   `∃ u f : Fin n → R, f ⬝ᵥ u = 0 ∧ rankOne u f ≠ 0 ∧ (τ : Matrix …) = 1 + rankOne u f`.
   - `u : Fin n → R` is V = R^n; the functional f ∈ V* = Hom_R(V,R) is represented by its
     coefficient row vector, evaluated by dot product (documented at Defs.lean:9-16).
   - `f ⬝ᵥ u` is `dotProduct f u = ∑ i, f i * u i` = f(u). ✓
   - `rankOne u f = Matrix.vecMulVec u f` (Defs.lean:25-26) has entries `u i * f j`, the
     rank-one operator of Definition 2.1 (`def:rankone`, lines 104-106), acting as
     `x ↦ f(x)•u`. ✓
   - `(τ : Matrix …) = 1 + rankOne u f` is τ = I_n + u⊗f with `1` = identity matrix. ✓
   - Nonidentity: `rankOne u f ≠ 0` forces τ ≠ I_n (proved in `IsTransvection.ne_one`,
     Statement.lean:83-94), and `main_statement` additionally asserts τ₁ ≠ 1 ∧ τ₂ ≠ 1. ✓

3. `GL (Fin n) R` is `Matrix.GeneralLinearGroup (Fin n) R = (Matrix (Fin n) (Fin n) R)ˣ`
   (units of the n×n matrix ring), i.e. the paper's GL_n(R) of invertible matrices
   (line 74). `V = Fin n → R` is R^n. ✓ (verified via `#print Matrix.GeneralLinearGroup`.)

4. Non-vacuity checks in Statement.lean are genuine and compile (no `True` placeholders,
   no caller-supplied `Prop` fields, no `opaque`, no `sorry`/`axiom`/`native_decide`):
   - `example : Nontrivial ℤ ∧ 3 ≤ 3` (line 40): hypotheses satisfiable.
   - `exTransvection : GL (Fin 3) ℤ` (lines 53-69): an explicit transvection over ℤ,
     `1 + e₀⊗e₁` with a real inverse and real `val_inv`/`inv_val` proofs.
   - `exTransvection_isTransvection` (lines 73-79) and `example : ¬ IsTransvection 1`
     (lines 97-99): the predicate is neither trivially true nor trivially false.
   - `example : ∃ τ₁ τ₂ … ⁅⁅1,τ₁⁆,τ₂⁆ = 1` (lines 106-112): conclusion satisfiable for σ=1.

5. No statement mismatch found: nothing stronger than the paper; commutativity is required
   (as in the paper) and no zero-divisor/unimodularity/field condition is silently assumed.

6. `main` (Main.lean:93) has type exactly `main_statement` (verified by `#check`). The proof
   introduces only the statement's hypotheses (`CommRing R`, `Nontrivial R`, `3 ≤ n`) and
   derives the three distinct indices i=0, j=1, k=2 from `3 ≤ n`; it uses the paper's
   argument (Lemma `exists_functional`, Main.lean:55-89, is the paper's Lemma 2.7). No
   extra assumption is smuggled in.

Build: `lake build DsBatch` completes successfully (exit 0).
No project file contains any forbidden token (the only grep hit is the word "sorry-free"
inside a docstring comment, not a `sorry`).
