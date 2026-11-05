import DsBatch.P07.Statement

/-! Proofs for project P07.

The paper's Theorem `thm:key31` states that `557` and `2417` (the prime factors
of `F 31`) divide exactly the same Fibonacci sums.  We prove it as follows.

* The Fibonacci sequence modulo either prime has period `124 = 4 · 31`:
  `F 124 ≡ 0` and `F 123 ≡ 1`, hence `F (n + 124) ≡ F n` by the addition
  formula, and therefore `F n ≡ F (n mod 124)`.
* This reduces the theorem to a finite check over the `124 × 124` residue
  classes, which is a kernel computation.

The second target then follows from the explicit function `swapFibPrimes`
exchanging the two primes. -/

namespace DsBatch.P07

set_option maxRecDepth 100000

/-! ### The explicit function `swapFibPrimes` -/

lemma swapFibPrimes_of_pq {N : ℕ} (hp : p ∣ N) (hq : q ∣ N) :
    swapFibPrimes N = N := by
  simp [swapFibPrimes, hp, hq]

lemma swapFibPrimes_of_p {N : ℕ} (hp : p ∣ N) (hq : ¬ q ∣ N) :
    swapFibPrimes N = q * (N / p) := by
  simp [swapFibPrimes, hp, hq]

lemma swapFibPrimes_of_q {N : ℕ} (hp : ¬ p ∣ N) (hq : q ∣ N) :
    swapFibPrimes N = p * (N / q) := by
  simp [swapFibPrimes, hp, hq]

lemma swapFibPrimes_of_none {N : ℕ} (hp : ¬ p ∣ N) (hq : ¬ q ∣ N) :
    swapFibPrimes N = N := by
  simp [swapFibPrimes, hp, hq]

/-- `swapFibPrimes` fixes every `N` on which `p` and `q` agree. -/
lemma swapFibPrimes_eq_self {N : ℕ} (h : p ∣ N ↔ q ∣ N) : swapFibPrimes N = N := by
  by_cases hp : p ∣ N
  · rw [swapFibPrimes_of_pq hp (h.mp hp)]
  · rw [swapFibPrimes_of_none hp (fun hq => hp (h.mpr hq))]

lemma swapFibPrimes_one : swapFibPrimes 1 = 1 := by
  rw [swapFibPrimes_of_none (by decide) (by decide)]

/-- `swapFibPrimes` is multiplicative: the two divisibility indicators are
additive on coprime products, and `p`, `q` are prime. -/
lemma swapFibPrimes_mul {a b : ℕ} (h : Nat.Coprime a b) :
    swapFibPrimes (a * b) = swapFibPrimes a * swapFibPrimes b := by
  have hp : Nat.Prime p := by norm_num [p]
  have hq : Nat.Prime q := by norm_num [q]
  have hpab : p ∣ a * b ↔ p ∣ a ∨ p ∣ b := hp.dvd_mul
  have hqab : q ∣ a * b ↔ q ∣ a ∨ q ∣ b := hq.dvd_mul
  have hcop : Nat.gcd a b = 1 := h
  have hpp : ¬ (p ∣ a ∧ p ∣ b) := by
    rintro ⟨h1, h2⟩
    exact hp.not_dvd_one (by rw [← hcop]; exact Nat.dvd_gcd h1 h2)
  have hqq : ¬ (q ∣ a ∧ q ∣ b) := by
    rintro ⟨h1, h2⟩
    exact hq.not_dvd_one (by rw [← hcop]; exact Nat.dvd_gcd h1 h2)
  by_cases hpa : p ∣ a
  · by_cases hqa : q ∣ a
    · -- `a` has both prime factors; then `b` has neither
      have hpb : ¬ p ∣ b := fun h' => hpp ⟨hpa, h'⟩
      have hqb : ¬ q ∣ b := fun h' => hqq ⟨hqa, h'⟩
      rw [swapFibPrimes_of_pq (by rw [hpab]; exact Or.inl hpa)
            (by rw [hqab]; exact Or.inl hqa),
        swapFibPrimes_of_pq hpa hqa, swapFibPrimes_of_none hpb hqb]
    · by_cases hpb : p ∣ b
      · exact absurd ⟨hpa, hpb⟩ hpp
      · by_cases hqb : q ∣ b
        · -- `a` is divisible by `p` only, `b` by `q` only
          rw [swapFibPrimes_of_pq (by rw [hpab]; exact Or.inl hpa)
                (by rw [hqab]; exact Or.inr hqb),
            swapFibPrimes_of_p hpa hqa, swapFibPrimes_of_q hpb hqb]
          symm
          calc q * (a / p) * (p * (b / q)) = p * (a / p) * (q * (b / q)) := by ring
            _ = a * b := by rw [Nat.mul_div_cancel' hpa, Nat.mul_div_cancel' hqb]
        · -- `a` is divisible by `p` only, `b` by neither
          rw [swapFibPrimes_of_p (by rw [hpab]; exact Or.inl hpa)
                (by rw [hqab]; simp [hqa, hqb]),
            swapFibPrimes_of_p hpa hqa, swapFibPrimes_of_none hpb hqb,
            show a * b / p = b * (a / p) by rw [mul_comm a b, Nat.mul_div_assoc b hpa]]
          ring
  · by_cases hqa : q ∣ a
    · by_cases hpb : p ∣ b
      · by_cases hqb : q ∣ b
        · exact absurd ⟨hqa, hqb⟩ hqq
        · -- `a` is divisible by `q` only, `b` by `p` only
          rw [swapFibPrimes_of_pq (by rw [hpab]; exact Or.inr hpb)
                (by rw [hqab]; exact Or.inl hqa),
            swapFibPrimes_of_q hpa hqa, swapFibPrimes_of_p hpb hqb]
          symm
          calc p * (a / q) * (q * (b / p)) = q * (a / q) * (p * (b / p)) := by ring
            _ = a * b := by rw [Nat.mul_div_cancel' hqa, Nat.mul_div_cancel' hpb]
      · by_cases hqb : q ∣ b
        · exact absurd ⟨hqa, hqb⟩ hqq
        · -- `a` is divisible by `q` only, `b` by neither
          rw [swapFibPrimes_of_q (by rw [hpab]; simp [hpa, hpb])
                (by rw [hqab]; exact Or.inl hqa),
            swapFibPrimes_of_q hpa hqa, swapFibPrimes_of_none hpb hqb,
            show a * b / q = b * (a / q) by rw [mul_comm a b, Nat.mul_div_assoc b hqa]]
          ring
    · by_cases hpb : p ∣ b
      · by_cases hqb : q ∣ b
        · -- `a` has neither prime factor, `b` has both
          rw [swapFibPrimes_of_pq (by rw [hpab]; exact Or.inr hpb)
                (by rw [hqab]; exact Or.inr hqb),
            swapFibPrimes_of_none hpa hqa, swapFibPrimes_of_pq hpb hqb]
        · -- `a` has neither prime factor, `b` is divisible by `p` only
          rw [swapFibPrimes_of_p (by rw [hpab]; exact Or.inr hpb)
                (by rw [hqab]; simp [hqa, hqb]),
            swapFibPrimes_of_none hpa hqa, swapFibPrimes_of_p hpb hqb,
            Nat.mul_div_assoc a hpb]
          ring
      · by_cases hqb : q ∣ b
        · -- `a` has neither prime factor, `b` is divisible by `q` only
          rw [swapFibPrimes_of_q (by rw [hpab]; simp [hpa, hpb])
                (by rw [hqab]; exact Or.inr hqb),
            swapFibPrimes_of_none hpa hqa, swapFibPrimes_of_q hpb hqb,
            Nat.mul_div_assoc a hqb]
          ring
        · -- neither `a` nor `b` is divisible by `p` or `q`
          rw [swapFibPrimes_of_none (by rw [hpab]; simp [hpa, hpb])
                (by rw [hqab]; simp [hqa, hqb]),
            swapFibPrimes_of_none hpa hqa, swapFibPrimes_of_none hpb hqb]

lemma swapFibPrimes_isMultiplicative : IsMultiplicative swapFibPrimes :=
  ⟨swapFibPrimes_one, fun _ _ h => swapFibPrimes_mul h⟩

/-! ### Periodicity of Fibonacci numbers modulo `p` and `q`

`F 123 ≡ 1` and `F 124 ≡ 0` modulo both primes; the Fibonacci addition formula
`F (m + n + 1) = F m * F n + F (m + 1) * F (n + 1)` then gives
`F (n + 124) ≡ F n`. -/

lemma fib_period {M : ℕ} (h0 : Nat.fib 124 % M = 0) (h1 : Nat.fib 123 % M = 1)
    (n : ℕ) : Nat.fib (n + 124) % M = Nat.fib n % M := by
  have h := Nat.fib_add 123 n
  simp only [show (123 : ℕ) + 1 = 124 by norm_num] at h
  have hn : n + 124 = 123 + n + 1 := by omega
  rw [hn, h]
  simp only [Nat.add_mod, Nat.mul_mod, h0, h1, Nat.zero_mul, Nat.one_mul, Nat.zero_mod,
    Nat.add_zero, Nat.mod_mod]

lemma fib_mod_period {M : ℕ} (h0 : Nat.fib 124 % M = 0) (h1 : Nat.fib 123 % M = 1)
    (n : ℕ) : Nat.fib n % M = Nat.fib (n % 124) % M := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < 124
    · rw [Nat.mod_eq_of_lt hn]
    · push Not at hn
      have hnm : n % 124 = (n - 124) % 124 := by omega
      rw [hnm]
      have he : n = (n - 124) + 124 := by omega
      nth_rewrite 1 [he]
      rw [fib_period h0 h1]
      exact ih (n - 124) (by omega)

/-! ### The finite check

`F n + F m` modulo either prime depends only on `n mod 124` and `m mod 124`, so
`thm:key31` follows from a check of the `124 × 124` residue classes. -/

set_option maxHeartbeats 4000000 in
lemma finite_check : ∀ i j : Fin 124,
    (557 ∣ Nat.fib i.val + Nat.fib j.val ↔ 2417 ∣ Nat.fib i.val + Nat.fib j.val) := by
  decide

/-- Theorem key31 of the paper. -/
theorem key31 : key31_statement := by
  intro n m hn hm
  have h557 : Nat.fib n % 557 = Nat.fib (n % 124) % 557 :=
    fib_mod_period (by decide) (by decide) n
  have h557m : Nat.fib m % 557 = Nat.fib (m % 124) % 557 :=
    fib_mod_period (by decide) (by decide) m
  have h2417 : Nat.fib n % 2417 = Nat.fib (n % 124) % 2417 :=
    fib_mod_period (by decide) (by decide) n
  have h2417m : Nat.fib m % 2417 = Nat.fib (m % 124) % 2417 :=
    fib_mod_period (by decide) (by decide) m
  have hdvd557 : (557 ∣ Nat.fib n + Nat.fib m) ↔
      (557 ∣ Nat.fib (n % 124) + Nat.fib (m % 124)) := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.add_mod,
      h557, h557m]
    simp
  have hdvd2417 : (2417 ∣ Nat.fib n + Nat.fib m) ↔
      (2417 ∣ Nat.fib (n % 124) + Nat.fib (m % 124)) := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.add_mod,
      h2417, h2417m]
    simp
  have hfin := finite_check ⟨n % 124, Nat.mod_lt _ (by norm_num)⟩
      ⟨m % 124, Nat.mod_lt _ (by norm_num)⟩
  exact hdvd557.trans (hfin.trans hdvd2417.symm)

/-! ### The counterexample -/

/-- For an odd prime `r`, `r ∣ 2 * n ↔ r ∣ n`. -/
lemma dvd_two_mul_iff {r : ℕ} (hr : Nat.Prime r) (h2 : ¬ r ∣ 2) (n : ℕ) :
    r ∣ 2 * n ↔ r ∣ n := by
  rw [hr.dvd_mul]
  tauto

/-- The two primes agree on individual Fibonacci numbers (apply `thm:key31` with
`m = n`, so that the sum is `2 F n`). -/
lemma fib_dvd_iff (n : ℕ) (hn : 1 ≤ n) : p ∣ F n ↔ q ∣ F n := by
  have h := key31 n n hn hn
  have hp' : 557 ∣ 2 * F n ↔ 557 ∣ F n :=
    dvd_two_mul_iff (by norm_num) (by norm_num) (F n)
  have hq' : 2417 ∣ 2 * F n ↔ 2417 ∣ F n :=
    dvd_two_mul_iff (by norm_num) (by norm_num) (F n)
  rw [show F n + F n = 2 * F n by ring] at h
  rw [hp', hq'] at h
  exact h

/-- `swapFibPrimes` fixes every Fibonacci number. -/
lemma swapFibPrimes_fib (n : ℕ) (hn : 1 ≤ n) : swapFibPrimes (F n) = F n :=
  swapFibPrimes_eq_self (fib_dvd_iff n hn)

/-- The explicit non-identity witness for `counterexample_statement`. -/
theorem counterexample : counterexample_statement := by
  refine ⟨swapFibPrimes, swapFibPrimes_isMultiplicative, ?_, ?_⟩
  · -- not the identity: it swaps `p` and `q`
    intro h
    have h557 : swapFibPrimes 557 = 2417 := by decide
    have hid := congrFun h 557
    rw [h557] at hid
    simp only [id_eq] at hid
    omega
  · -- additivity on Fibonacci sums
    intro n m hn hm
    rw [swapFibPrimes_eq_self (key31 n m hn hm),
      swapFibPrimes_fib n hn, swapFibPrimes_fib m hm]

end DsBatch.P07
