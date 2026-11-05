import DsBatch.P05.Statement

/-! Proofs for project P05: the main theorem of arXiv 2609.17006.

The proof follows the paper.  All the linear algebra happens in the matrix ring
`Matrix (Fin n) (Fin n) R`.  The only place where commutativity and `n ≥ 3`
enter is `exists_functional` (Lemma 2.7 of the paper): two indices `j, k`
distinct from `i` are used to manufacture a nonzero row vector annihilating both
`e i` and `w`. -/

namespace DsBatch.P05

open Matrix
open scoped commutatorElement

/-- Lemma 2.5 of the paper: if `0 ≠ f` is a functional and `e i` a standard
basis vector, then `e i ⊗ f ≠ 0`.  (Here `f` is a row vector and the standard
basis vector is `Pi.single i 1`.) -/
lemma rankOne_single_ne_zero {n : ℕ} {R : Type*} [CommRing R] [Nontrivial R]
    {i : Fin n} {f : Fin n → R} (hf : f ≠ 0) :
    rankOne (Pi.single i (1 : R)) f ≠ 0 := by
  intro h
  apply hf
  funext l
  have h1 : rankOne (Pi.single i (1 : R)) f i l =
      (0 : Matrix (Fin n) (Fin n) R) i l := by rw [h]
  simpa [rankOne, vecMulVec_apply] using h1

/-- The unit `1 + A` when `A * A = 0`, with inverse `1 - A`. -/
def unitOneAdd {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (h : A * A = 0) : GL (Fin n) R where
  val := 1 + A
  inv := 1 - A
  val_inv := by
    calc (1 + A) * (1 - A) = (1 + A) * 1 - (1 + A) * A := by rw [mul_sub]
      _ = (1 + A) - (A + A * A) := by rw [mul_one, add_mul, one_mul]
      _ = 1 := by rw [h]; noncomm_ring
  inv_val := by
    calc (1 - A) * (1 + A) = (1 - A) * 1 + (1 - A) * A := by rw [mul_add]
      _ = (1 - A) + (A - A * A) := by rw [mul_one, sub_mul, one_mul]
      _ = 1 := by rw [h]; noncomm_ring

@[simp] lemma coe_unitOneAdd {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (h : A * A = 0) :
    ((unitOneAdd A h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 + A := rfl

@[simp] lemma coe_inv_unitOneAdd {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (h : A * A = 0) :
    (((unitOneAdd A h)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 - A := rfl

/-- Lemma 2.7 of the paper: for a standard basis vector `e i` and any `w`, and
for distinct indices `j, k` different from `i`, there is a nonzero functional
`f` with `f(e i) = f(w) = 0`.  Concretely, if `w j, w k` are not both zero we
take `f = w k · e j^* - w j · e k^*`; otherwise `f = e j^*`. -/
lemma exists_functional {n : ℕ} {R : Type*} [CommRing R] [Nontrivial R]
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (w : Fin n → R) :
    ∃ f : Fin n → R, f ≠ 0 ∧ f ⬝ᵥ (Pi.single i (1 : R)) = 0 ∧ f ⬝ᵥ w = 0 := by
  by_cases h : w j = 0 ∧ w k = 0
  · refine ⟨Pi.single j (1 : R), ?_, ?_, ?_⟩
    · intro hf
      have h1 : (Pi.single j (1 : R) : Fin n → R) j = (0 : Fin n → R) j := by rw [hf]
      simp at h1
    · rw [dotProduct_single_one]
      simp [Pi.single_eq_of_ne hij]
    · rw [single_one_dotProduct]
      exact h.1
  · have hwj : w j ≠ 0 ∨ w k ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h ⟨hc.1, hc.2⟩
    set f : Fin n → R := w k • Pi.single j (1 : R) - w j • Pi.single k (1 : R) with hf_def
    refine ⟨f, ?_, ?_, ?_⟩
    · intro hf
      have hj : f j = w k := by
        simp [hf_def, Pi.single_eq_of_ne hjk]
      have hk : f k = - w j := by
        simp [hf_def, Pi.single_eq_of_ne hjk.symm]
      rw [hf] at hj hk
      simp at hj hk
      rcases hwj with h' | h'
      · exact h' hk
      · exact h' hj.symm
    · rw [hf_def, sub_dotProduct, smul_dotProduct, smul_dotProduct, dotProduct_single_one,
        dotProduct_single_one]
      simp [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hik]
    · rw [hf_def, sub_dotProduct, smul_dotProduct, smul_dotProduct, single_one_dotProduct,
        single_one_dotProduct]
      ring

set_option maxHeartbeats 1000000 in
/-- Theorem 2.9 (the paper's main theorem). -/
theorem main : main_statement := by
  intro R _ _ n hn σ
  have hn0 : (0 : ℕ) < n := by omega
  have hn1 : (1 : ℕ) < n := by omega
  have hn2 : (2 : ℕ) < n := by omega
  let i : Fin n := ⟨0, hn0⟩
  let j : Fin n := ⟨1, hn1⟩
  let k : Fin n := ⟨2, hn2⟩
  have hij : i ≠ j := by
    intro h; have := congrArg Fin.val h; simp [i, j] at this
  have hik : i ≠ k := by
    intro h; have := congrArg Fin.val h; simp [i, k] at this
  have hjk : j ≠ k := by
    intro h; have := congrArg Fin.val h; simp [j, k] at this
  set σm : Matrix (Fin n) (Fin n) R := (σ : Matrix (Fin n) (Fin n) R) with hσm_def
  set σim : Matrix (Fin n) (Fin n) R :=
    ((σ⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) with hσim_def
  have hσmul : σm * σim = 1 := by
    rw [hσm_def, hσim_def, ← Units.val_mul]
    simp
  have hσmul' : σim * σm = 1 := by
    rw [hσim_def, hσm_def, ← Units.val_mul]
    simp
  set v : Fin n → R := Pi.single i (1 : R) with hv_def
  set w : Fin n → R := σm *ᵥ v with hw_def
  obtain ⟨f, hfne, hfv, hfw⟩ := exists_functional i j k hij hik hjk w
  rw [← hv_def] at hfv
  set N : Matrix (Fin n) (Fin n) R := rankOne v f with hN_def
  have hN2 : N * N = 0 := by
    rw [hN_def, rankOne, vecMulVec_mul_vecMulVec, hfv]
    simp
  have hNne : N ≠ 0 := by
    rw [hN_def]
    simpa [hv_def] using rankOne_single_ne_zero hfne
  set τ₁ : GL (Fin n) R := unitOneAdd N hN2 with hτ₁_def
  have hτ₁val : (τ₁ : Matrix (Fin n) (Fin n) R) = 1 + N := by
    rw [hτ₁_def]; rfl
  have hτ₁inv : ((τ₁⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 - N := by
    rw [hτ₁_def]; rfl
  have htransτ₁ : IsTransvection τ₁ := by
    refine ⟨v, f, hfv, ?_, ?_⟩
    · rw [← hN_def]; exact hNne
    · rw [hτ₁val, hN_def]
  have hτ₁ne : τ₁ ≠ 1 := IsTransvection.ne_one htransτ₁
  set M : Matrix (Fin n) (Fin n) R := σm * N * σim with hM_def
  have hM2 : M * M = 0 := by
    rw [hM_def]
    calc (σm * N * σim) * (σm * N * σim)
        = σm * N * (σim * σm) * N * σim := by noncomm_ring
      _ = σm * (N * N) * σim := by rw [hσmul']; noncomm_ring
      _ = 0 := by rw [hN2]; simp
  have hNσim : N * σim = rankOne v (f ᵥ* σim) := by
    rw [hN_def, rankOne, vecMulVec_mul, rankOne]
  have hM_eq : M = rankOne w (f ᵥ* σim) := by
    calc M = σm * (N * σim) := by rw [hM_def]; noncomm_ring
      _ = σm * rankOne v (f ᵥ* σim) := by rw [hNσim]
      _ = rankOne (σm *ᵥ v) (f ᵥ* σim) := by
            rw [rankOne, rankOne]
            exact mul_vecMulVec σm v (f ᵥ* σim)
      _ = rankOne w (f ᵥ* σim) := by rw [← hw_def]
  have hNσm : N * σm = rankOne v (f ᵥ* σm) := by
    rw [hN_def, rankOne, vecMulVec_mul, rankOne]
  have hNM : N * M = 0 := by
    calc N * M = (N * σm) * N * σim := by rw [hM_def]; noncomm_ring
      _ = rankOne v (f ᵥ* σm) * N * σim := by rw [hNσm]
      _ = rankOne v (f ᵥ* σm) * rankOne v f * σim := by rw [hN_def]
      _ = rankOne v (((f ᵥ* σm) ⬝ᵥ v) • f) * σim := by
            simp only [rankOne]
            rw [vecMulVec_mul_vecMulVec]
      _ = 0 := by
            have hscalar : (f ᵥ* σm) ⬝ᵥ v = 0 := by
              rw [← dotProduct_mulVec]
              rw [← hw_def]
              exact hfw
            rw [hscalar]
            simp [rankOne]
  have hMN2 : (M * N) * (M * N) = 0 := by
    calc (M * N) * (M * N) = M * (N * M) * N := by noncomm_ring
      _ = 0 := by rw [hNM]; simp
  have hAcoe : ((⁅σ, τ₁⁆ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      σm * (1 + N) * σim * (1 - N) := by
    rw [hσm_def, hσim_def, hτ₁_def]
    simp only [Bracket.bracket, Units.val_mul, coe_unitOneAdd, coe_inv_unitOneAdd]
  have hconj : σm * (1 + N) * σim = 1 + M := by
    calc σm * (1 + N) * σim = σm * σim + σm * N * σim := by noncomm_ring
      _ = 1 + σm * N * σim := by rw [hσmul]
      _ = 1 + M := by rw [hM_def]
  have hAval : ((⁅σ, τ₁⁆ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      1 + (M - N - M * N) := by
    rw [hAcoe, hconj, mul_sub, mul_one, add_mul, one_mul]
    abel
  set A : GL (Fin n) R := ⁅σ, τ₁⁆ with hA_def
  have hAval' : (A : Matrix (Fin n) (Fin n) R) = 1 + (M - N - M * N) := by
    rw [hA_def]; exact hAval
  by_cases hMN : M * N = 0
  · -- Case `MN = 0`: take `τ₂ = τ₁`.
    refine ⟨τ₁, τ₁, htransτ₁, htransτ₁, hτ₁ne, hτ₁ne, ?_⟩
    have hX1 : (M - N - M * N) * N = 0 := by
      rw [sub_mul, sub_mul, hMN, hN2]; simp
    have hX2 : N * (M - N - M * N) = 0 := by
      rw [mul_sub, mul_sub, hNM, hN2, hMN]; simp
    have hcomm_mat : (1 + (M - N - M * N)) * (1 + N) =
        (1 + N) * (1 + (M - N - M * N)) := by
      have e1 : (1 + (M - N - M * N)) * (1 + N) = 1 + (M - N - M * N) + N := by
        rw [mul_add, mul_one, add_mul, one_mul, hX1]
        abel
      have e2 : (1 + N) * (1 + (M - N - M * N)) = 1 + N + (M - N - M * N) := by
        rw [mul_add, mul_one, add_mul, one_mul, hX2]
        abel
      rw [e1, e2]
      abel
    have hcomm : A * τ₁ = τ₁ * A := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hAval', hτ₁val]
      exact hcomm_mat
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  · -- Case `MN ≠ 0`: take `τ₂ = 1 + MN`, a transvection with direction
    -- vector `σ v` and functional `f(σ⁻¹ v) · f`.
    set g : Fin n → R := ((f ᵥ* σim) ⬝ᵥ v) • f with hg_def
    have hMN_eq : M * N = rankOne w g := by
      simp only [hM_eq, hN_def, hg_def, rankOne]
      rw [vecMulVec_mul_vecMulVec]
    have hgw : g ⬝ᵥ w = 0 := by
      rw [hg_def, smul_dotProduct, hfw]
      simp
    have hneq : rankOne w g ≠ 0 := by
      rw [← hMN_eq]
      exact hMN
    set τ₂ : GL (Fin n) R := unitOneAdd (M * N) hMN2 with hτ₂_def
    have hτ₂val : (τ₂ : Matrix (Fin n) (Fin n) R) = 1 + M * N := by
      rw [hτ₂_def]; rfl
    have htransτ₂ : IsTransvection τ₂ := by
      refine ⟨w, g, hgw, hneq, ?_⟩
      rw [hτ₂val, hMN_eq]
    have hτ₂ne : τ₂ ≠ 1 := IsTransvection.ne_one htransτ₂
    refine ⟨τ₁, τ₂, htransτ₁, htransτ₂, hτ₁ne, hτ₂ne, ?_⟩
    have hX1 : (M - N - M * N) * (M * N) = 0 := by
      rw [sub_mul, sub_mul]
      have h3 : M * (M * N) = 0 := by rw [← mul_assoc, hM2, zero_mul]
      have h4 : N * (M * N) = 0 := by rw [← mul_assoc, hNM, zero_mul]
      rw [h3, h4, hMN2]; simp
    have hX2 : (M * N) * (M - N - M * N) = 0 := by
      rw [mul_sub, mul_sub]
      have h3 : (M * N) * M = 0 := by rw [mul_assoc, hNM, mul_zero]
      have h4 : (M * N) * N = 0 := by rw [mul_assoc, hN2, mul_zero]
      rw [h3, h4, hMN2]; simp
    have hcomm_mat : (1 + (M - N - M * N)) * (1 + M * N) =
        (1 + M * N) * (1 + (M - N - M * N)) := by
      have e1 : (1 + (M - N - M * N)) * (1 + M * N) =
          1 + (M - N - M * N) + M * N := by
        rw [mul_add, mul_one, add_mul, one_mul, hX1]
        abel
      have e2 : (1 + M * N) * (1 + (M - N - M * N)) =
          1 + M * N + (M - N - M * N) := by
        rw [mul_add, mul_one, add_mul, one_mul, hX2]
        abel
      rw [e1, e2]
      abel
    have hcomm : A * τ₂ = τ₂ * A := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hAval', hτ₂val]
      exact hcomm_mat
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

end DsBatch.P05
