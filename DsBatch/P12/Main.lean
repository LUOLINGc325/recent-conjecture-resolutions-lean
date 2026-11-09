import DsBatch.P12.Statement

/-! Proofs for project P12 (required scope). -/

namespace DsBatch.P12

open Nat


open Nat

/-- An odd prime different from 3 is at least 5. -/
lemma five_le_of_odd_prime_ne_three {p : ℕ} (hp : Nat.Prime p) (hodd : Odd p)
    (hp3 : p ≠ 3) : 5 ≤ p := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hodd
  have hp4 : p ≠ 4 := by
    rintro rfl
    norm_num at hodd
  have h2 := hp.two_le
  omega

/-- **Lemma 3.2 (candidates).**  If `n` satisfies `φ(n) = 2 p^s` and `q` is a
prime divisor of `n`, then `q ∈ {2, 3} ∪ {q_j : 1 ≤ j ≤ s}`, where
`q_j = 2 p^j + 1`. -/
lemma prime_dvd_candidate (p s : ℕ) (hp : Nat.Prime p) (hodd : Odd p) (hp3 : p ≠ 3)
    (hs : 1 ≤ s) {n : ℕ} (hφ : Nat.totient n = 2 * p ^ s)
    {q : ℕ} (hq : Nat.Prime q) (hqn : q ∣ n) :
    q = 2 ∨ q = 3 ∨ ∃ j : ℕ, 1 ≤ j ∧ j ≤ s ∧ q = 2 * p ^ j + 1 := by
  have hp5 : 5 ≤ p := five_le_of_odd_prime_ne_three hp hodd hp3
  have hdvd : q - 1 ∣ 2 * p ^ s := by
    have h := Nat.totient_dvd_of_dvd hqn
    rwa [Nat.totient_prime hq, hφ] at h
  have hq2 : 2 ≤ q := hq.two_le
  have hqpos : 0 < q := by omega
  set d := q - 1 with hd
  have hdpos : 0 < d := by omega
  have hqd : q = d + 1 := by omega
  by_cases hpdiv : p ∣ d
  · set b := d.factorization p with hb
    have hdne : d ≠ 0 := by omega
    have hbpos : 0 < b := by
      rw [hb]
      exact Nat.Prime.factorization_pos_of_dvd hp hdne hpdiv
    have hpb : p ^ b ∣ d := by
      rw [hb]
      exact Nat.ordProj_dvd d p
    set e := d / p ^ b with he
    have hde : d = p ^ b * e := by
      rw [he]
      exact (Nat.mul_div_cancel' hpb).symm
    have h_not_p_e : ¬ p ∣ e := by
      intro hpe
      have hdvd' : p ^ (b + 1) ∣ d := by
        rw [hde, pow_succ]
        exact mul_dvd_mul_left (p ^ b) hpe
      have hnot := Nat.pow_succ_factorization_not_dvd hdne hp
      exact hnot (by rw [← hb]; exact hdvd')
    have hcop : Nat.Coprime e (p ^ s) := by
      have h1 : Nat.Coprime e p := ((hp.coprime_iff_not_dvd).mpr h_not_p_e).symm
      exact h1.pow_right s
    have hed : e ∣ d := ⟨p ^ b, by rw [hde, mul_comm]⟩
    have he_dvd : e ∣ 2 * p ^ s := hed.trans hdvd
    have he2 : e ∣ 2 := hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at he_dvd)
    have hepos : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h0 | h
      · rw [h0, mul_zero] at hde
        omega
      · exact h
    have he_cases : e = 1 ∨ e = 2 := by
      have hle : e ≤ 2 := Nat.le_of_dvd (by norm_num) he2
      omega
    rcases he_cases with he1 | he2'
    · have hd_eq : d = p ^ b := by rw [hde, he1, mul_one]
      have hq_eq : q = p ^ b + 1 := by omega
      rcases Nat.eq_zero_or_pos b with hb0 | hbpos'
      · left
        rw [hb0] at hq_eq
        simpa using hq_eq
      · exfalso
        have hpb_odd : Odd (p ^ b) := hodd.pow
        have hq_even : Even q := by
          rw [hq_eq]
          exact hpb_odd.add_one
        have hq_ne_two : q ≠ 2 := by
          intro h2q
          rw [h2q] at hq_eq
          have h1 : p ^ b = 1 := by omega
          have hb0 : b = 0 := by
            rcases Nat.eq_zero_or_pos b with h | h
            · exact h
            · have h2 : 2 ≤ p ^ b :=
              le_trans hp.two_le (by simpa using Nat.pow_le_pow_right hp.pos h)
              omega
          omega
        exact hq_ne_two (hq.even_iff.mp hq_even)
    · right; right
      have hd_eq : d = 2 * p ^ b := by rw [hde, he2', mul_comm]
      have hq_eq : q = 2 * p ^ b + 1 := by omega
      have hpb2 : p ^ b ∣ 2 * p ^ s := hpb.trans hdvd
      have hp_not_dvd_two : ¬ p ∣ 2 := by
        intro h
        have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
        omega
      have hpb_ps : p ^ b ∣ p ^ s :=
        Prime.pow_dvd_of_dvd_mul_left hp.prime b hp_not_dvd_two hpb2
      have hbs : b ≤ s := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpb_ps
      exact ⟨b, hbpos, hbs, hq_eq⟩
  · have hcop : Nat.Coprime d (p ^ s) := by
      have h1 : Nat.Coprime d p := ((hp.coprime_iff_not_dvd).mpr hpdiv).symm
      exact h1.pow_right s
    have hd2 : d ∣ 2 := hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at hdvd)
    have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hd2
    have hd_cases : d = 1 ∨ d = 2 := by omega
    rcases hd_cases with h | h
    · left; omega
    · right; left; omega



open Nat

lemma ne_zero_of_totient_eq (p s n : ℕ) (hp : Nat.Prime p)
    (hφ : Nat.totient n = 2 * p ^ s) : n ≠ 0 := by
  rintro rfl
  rw [Nat.totient_zero] at hφ
  have h1 : 1 ≤ p ^ s := Nat.one_le_pow s p hp.pos
  omega

/-- The `2`-adic exponent of a solution of `φ(n) = 2p^s` is at most `2`. -/
lemma factorization_two_le_two (p s n : ℕ) (hp : Nat.Prime p) (hodd : Odd p)
    (hφ : Nat.totient n = 2 * p ^ s) : n.factorization 2 ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ n.factorization 2 := by omega
  have hn0 : n ≠ 0 := ne_zero_of_totient_eq p s n hp hφ
  have h8 : 8 ∣ n := by
    have hpow : 2 ^ 3 ∣ 2 ^ n.factorization 2 := pow_dvd_pow 2 h3
    have h2 : 2 ^ n.factorization 2 ∣ n :=
      (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 2) hn0).mpr le_rfl
    have := hpow.trans h2
    simpa using this
  have htot : Nat.totient 8 ∣ Nat.totient n := Nat.totient_dvd_of_dvd h8
  rw [hφ] at htot
  have h8t : Nat.totient 8 = 4 := by decide
  rw [h8t] at htot
  obtain ⟨k, hk⟩ := htot
  have hp2dvd : 2 ∣ p ^ s := by
    refine ⟨k, ?_⟩
    omega
  have hp2 : 2 ∣ p := (by norm_num : Nat.Prime 2).dvd_of_dvd_pow hp2dvd
  have hpeq : p = 2 := (Nat.Prime.dvd_iff_eq hp (by norm_num)).mp hp2
  rw [hpeq] at hodd
  rcases hodd with ⟨m, hm⟩
  omega

/-- The `3`-adic exponent of a solution of `φ(n) = 2p^s` is at most `1`. -/
lemma factorization_three_le_one (p s n : ℕ) (hp : Nat.Prime p) (hp3 : p ≠ 3)
    (hφ : Nat.totient n = 2 * p ^ s) : n.factorization 3 ≤ 1 := by
  by_contra h
  have h2 : 2 ≤ n.factorization 3 := by omega
  have hn0 : n ≠ 0 := ne_zero_of_totient_eq p s n hp hφ
  have h9 : 9 ∣ n := by
    have hpow : 3 ^ 2 ∣ 3 ^ n.factorization 3 := pow_dvd_pow 3 h2
    have h3 : 3 ^ n.factorization 3 ∣ n :=
      (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 3) hn0).mpr le_rfl
    have := hpow.trans h3
    simpa using this
  have htot : Nat.totient 9 ∣ Nat.totient n := Nat.totient_dvd_of_dvd h9
  rw [hφ] at htot
  have h9t : Nat.totient 9 = 6 := by decide
  rw [h9t] at htot
  obtain ⟨k, hk⟩ := htot
  have h3dvd : 3 ∣ p ^ s := by
    refine ⟨k, ?_⟩
    omega
  have hp3d : 3 ∣ p := (by norm_num : Nat.Prime 3).dvd_of_dvd_pow h3dvd
  have hpeq : p = 3 := (Nat.Prime.dvd_iff_eq hp (by norm_num)).mp hp3d
  exact hp3 hpeq

/-- The exponent of a candidate prime `q_j = 2p^j+1` (when prime) is at most `1`. -/
lemma factorization_q_le_one (p s j n : ℕ) (hp : Nat.Prime p) (hodd : Odd p)
    (hj : 1 ≤ j) (hqj : Nat.Prime (2 * p ^ j + 1))
    (hφ : Nat.totient n = 2 * p ^ s) :
    n.factorization (2 * p ^ j + 1) ≤ 1 := by
  by_contra h
  have h2 : 2 ≤ n.factorization (2 * p ^ j + 1) := by omega
  have hn0 : n ≠ 0 := ne_zero_of_totient_eq p s n hp hφ
  have hq2dvd : (2 * p ^ j + 1) ^ 2 ∣ n := by
    have hpow : (2 * p ^ j + 1) ^ 2 ∣
        (2 * p ^ j + 1) ^ n.factorization (2 * p ^ j + 1) := pow_dvd_pow _ h2
    have hqfac : (2 * p ^ j + 1) ^ n.factorization (2 * p ^ j + 1) ∣ n :=
      (Nat.Prime.pow_dvd_iff_le_factorization hqj hn0).mpr le_rfl
    exact hpow.trans hqfac
  have htot : Nat.totient ((2 * p ^ j + 1) ^ 2) ∣ Nat.totient n :=
    Nat.totient_dvd_of_dvd hq2dvd
  rw [hφ] at htot
  have htq : Nat.totient ((2 * p ^ j + 1) ^ 2) =
      (2 * p ^ j + 1) * (2 * p ^ j) := by
    rw [Nat.totient_prime_pow hqj (by norm_num)]
    norm_num
  rw [htq] at htot
  set qq := 2 * p ^ j + 1 with hqq
  have hq_dvd : qq ∣ 2 * p ^ s := (dvd_mul_right qq (2 * p ^ j)).trans htot
  have hq_odd : Odd qq := ⟨p ^ j, by rw [hqq]⟩
  have hq_cop : Nat.Coprime qq 2 := Nat.coprime_two_right.mpr hq_odd
  have hq_pow : qq ∣ p ^ s := hq_cop.dvd_of_dvd_mul_left hq_dvd
  have hq_p : qq ∣ p := hqj.dvd_of_dvd_pow hq_pow
  have hqq_ne_one : qq ≠ 1 := by
    rw [hqq]
    have h1 : 1 ≤ p ^ j := Nat.one_le_pow j p hp.pos
    omega
  have hpq : p = qq := (Nat.Prime.dvd_iff_eq hp hqq_ne_one).mp hq_p
  have hpj : p ≤ p ^ j := by
    simpa using Nat.pow_le_pow_right hp.pos hj
  have hlt : p ^ j < p := by
    rw [hpq]
    omega
  exact (not_le.mpr hlt) hpj


open Nat

/-- **Lemma 3.1 (no `p` in a solution).**  If `p ≥ 5` is prime and `φ(n) = 2p^s`,
then `p ∤ n`. -/
lemma not_dvd_of_totient_eq (p s n : ℕ) (hp : Nat.Prime p) (hodd : Odd p) (hp3 : p ≠ 3)
    (hφ : Nat.totient n = 2 * p ^ s) : ¬ p ∣ n := by
  have hp5 : 5 ≤ p := five_le_of_odd_prime_ne_three hp hodd hp3
  intro hpdn
  have h := Nat.totient_dvd_of_dvd hpdn
  rw [Nat.totient_prime hp, hφ] at h
  have hnot : ¬ p ∣ p - 1 := by
    intro hpd
    have hp1 : 0 < p - 1 := by omega
    have hle := Nat.le_of_dvd hp1 hpd
    omega
  have hcop : Nat.Coprime (p - 1) (p ^ s) := by
    have h1 : Nat.Coprime (p - 1) p := ((hp.coprime_iff_not_dvd).mpr hnot).symm
    exact h1.pow_right s
  have h2 : p - 1 ∣ 2 := hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at h)
  have hle : p - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  omega

/-- The `p`-adic exponent of `2 p^s` is `s` (for `p ≠ 2`). -/
lemma factorization_two_mul_pow_p (p s : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    (2 * p ^ s).factorization p = s := by
  have h2 : (2 : ℕ) ≠ 0 := by norm_num
  have hps : p ^ s ≠ 0 := pow_ne_zero s hp.ne_zero
  rw [Nat.factorization_mul h2 hps, Finsupp.add_apply,
    Nat.Prime.factorization_pow hp]
  have hz : (Finsupp.single p s : ℕ →₀ ℕ) p = s := Finsupp.single_eq_same
  rw [hz]
  have h0 : (2 : ℕ).factorization p = 0 := by
    rw [Nat.factorization_eq_zero_of_not_dvd]
    intro h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
    have hp2le : 2 ≤ p := hp.two_le
    omega
  rw [h0, zero_add]

/-- The `2`-adic exponent of `2 p^s` (with `p` an odd prime) is `1`. -/
lemma factorization_two_mul_pow_two (p s : ℕ) (hp : Nat.Prime p) (hodd : Odd p) :
    (2 * p ^ s).factorization 2 = 1 := by
  have h2 : (2 : ℕ) ≠ 0 := by norm_num
  have hps : p ^ s ≠ 0 := pow_ne_zero s hp.ne_zero
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hodd
    norm_num at hodd
  rw [Nat.factorization_mul h2 hps, Finsupp.add_apply,
    Nat.Prime.factorization_pow hp]
  have hz : (Finsupp.single p s : ℕ →₀ ℕ) 2 = 0 :=
    Finsupp.single_eq_of_ne (by omega : (2:ℕ) ≠ p)
  rw [hz, add_zero]
  rw [Nat.Prime.factorization (by norm_num : Nat.Prime 2)]
  exact Finsupp.single_eq_same



open Nat

/-- For an even exponent `s`, the candidate `2 p^s + 1` is divisible by `3`
(when `p ≠ 3`). -/
lemma three_dvd_candidate_of_even (p s : ℕ) (hp : Nat.Prime p) (hp3 : p ≠ 3)
    (hse : Even s) : 3 ∣ 2 * p ^ s + 1 := by
  rw [← CharP.cast_eq_zero_iff (ZMod 3) 3]
  obtain ⟨k, rfl⟩ := hse
  push_cast
  have hp0 : ((p : ℕ) : ZMod 3) ≠ 0 := by
    intro h
    have hdvd : 3 ∣ p := (CharP.cast_eq_zero_iff (ZMod 3) 3 p).mp h
    exact hp3 ((Nat.Prime.dvd_iff_eq hp (by norm_num)).mp hdvd)
  have hsq : ∀ x : ZMod 3, x ≠ 0 → x ^ 2 = 1 := by decide
  rw [pow_add]
  have hpk0 : ((p : ℕ) : ZMod 3) ^ k ≠ 0 := pow_ne_zero k hp0
  have h2 : ((p : ℕ) : ZMod 3) ^ k * ((p : ℕ) : ZMod 3) ^ k = 1 := by
    have := hsq _ hpk0
    rwa [pow_two] at this
  rw [h2]
  decide

/-- For an even positive exponent `s`, the candidate `2 p^s + 1 > 3` is not
prime. -/
lemma not_prime_candidate_of_even (p s : ℕ) (hp : Nat.Prime p) (hodd : Odd p)
    (hp3 : p ≠ 3) (hs0 : 0 < s) (hse : Even s) : ¬ Nat.Prime (2 * p ^ s + 1) := by
  intro hq
  have hp5 : 5 ≤ p := five_le_of_odd_prime_ne_three hp hodd hp3
  have h3dvd := three_dvd_candidate_of_even p s hp hp3 hse
  have hqe : 2 * p ^ s + 1 = 3 :=
    (Nat.Prime.dvd_iff_eq hq (by norm_num : (3:ℕ) ≠ 1)).mp h3dvd
  have hps : 5 ≤ p ^ s := by
    have h1 : p ≤ p ^ s := Nat.le_self_pow (by omega : s ≠ 0) p
    omega
  omega



open Nat

/-- The `p`-adic valuation of `∏_{q | n}(q-1)` equals `s`, the exponent of `p`
in `φ(n) = 2p^s`. -/
lemma sum_factor_sub_one_factorization_p (p s n : ℕ) (hp : Nat.Prime p) (hodd : Odd p)
    (hp3 : p ≠ 3) (hs : 1 ≤ s) (hφ : Nat.totient n = 2 * p ^ s) :
    ∑ l ∈ n.primeFactors, (l - 1).factorization p = s := by
  have hp5 : 5 ≤ p := five_le_of_odd_prime_ne_three hp hodd hp3
  have hn0 : n ≠ 0 := ne_zero_of_totient_eq p s n hp hφ
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hodd
  have hpnd : ¬ p ∣ n := not_dvd_of_totient_eq p s n hp hodd hp3 hφ
  have hφfacp : (Nat.totient n).factorization p = s := by
    rw [hφ]; exact factorization_two_mul_pow_p p s hp hp2
  have hnp : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpnd
  have hident := Nat.totient_mul_prod_primeFactors n
  have hfacEq : (Nat.totient n * ∏ l ∈ n.primeFactors, l).factorization p
      = (n * ∏ l ∈ n.primeFactors, (l - 1)).factorization p := by rw [hident]
  have hA1 : Nat.totient n ≠ 0 := by rw [hφ]; positivity
  have hA2 : (∏ l ∈ n.primeFactors, l) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro l hl
    exact (Nat.mem_primeFactors.mp hl).1.ne_zero
  have hB2 : (∏ l ∈ n.primeFactors, (l - 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro l hl
    have h2 := (Nat.mem_primeFactors.mp hl).1.two_le
    omega
  rw [Nat.factorization_mul hA1 hA2, Nat.factorization_mul hn0 hB2,
      Finsupp.add_apply, Finsupp.add_apply] at hfacEq
  have hsumL : (∏ l ∈ n.primeFactors, l).factorization p
      = ∑ l ∈ n.primeFactors, (l).factorization p := by
    have h := Nat.factorization_prod (S := n.primeFactors) (g := fun l => l)
      (fun l hl => (Nat.mem_primeFactors.mp hl).1.ne_zero)
    rw [h]
    simpa using Finset.sum_apply p n.primeFactors (fun l => (l).factorization)
  have hsumR : (∏ l ∈ n.primeFactors, (l - 1)).factorization p
      = ∑ l ∈ n.primeFactors, (l - 1).factorization p := by
    have h := Nat.factorization_prod (S := n.primeFactors) (g := fun l => l - 1)
      (fun l hl => by
        have h2 := (Nat.mem_primeFactors.mp hl).1.two_le
        omega)
    rw [h]
    simpa using Finset.sum_apply p n.primeFactors (fun l => (l - 1).factorization)
  have hLzero : ∑ l ∈ n.primeFactors, (l).factorization p = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    have hlprime := (Nat.mem_primeFactors.mp hl).1
    have hlp : p ≠ l := by
      intro h
      rw [h] at hpnd
      exact hpnd (Nat.mem_primeFactors.mp hl).2.1
    rw [Nat.Prime.factorization hlprime]
    exact Finsupp.single_eq_of_ne hlp
  rw [hφfacp, hnp, hsumL, hsumR, hLzero] at hfacEq
  omega


open Nat

set_option maxHeartbeats 800000

/-- **Main structure theorem.**  If `φ(n) = 2 p^s` with `p ≥ 5` prime, `s ≥ 1`,
then `2 p^s + 1` is prime and `n ∈ {2 p^s + 1, 2 (2 p^s + 1)}`. -/
lemma key_classification (p s n : ℕ) (hp : Nat.Prime p) (hodd : Odd p) (hp3 : p ≠ 3)
    (hs : 1 ≤ s) (hφ : Nat.totient n = 2 * p ^ s) :
    Nat.Prime (2 * p ^ s + 1) ∧ (n = 2 * p ^ s + 1 ∨ n = 2 * (2 * p ^ s + 1)) := by
  have hp5 : 5 ≤ p := five_le_of_odd_prime_ne_three hp hodd hp3
  have hn0 : n ≠ 0 := ne_zero_of_totient_eq p s n hp hφ
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hodd
  have hpnd : ¬ p ∣ n := not_dvd_of_totient_eq p s n hp hodd hp3 hφ
  have hu2 : n.factorization 2 ≤ 2 := factorization_two_le_two p s n hp hodd hφ
  have he1 : n.factorization 3 ≤ 1 := factorization_three_le_one p s n hp hp3 hφ
  let Q : ℕ → ℕ := fun j => 2 * p ^ j + 1
  have hQinj : Function.Injective Q := by
    intro i j hij
    simp only [Q] at hij
    have h : p ^ i = p ^ j := by omega
    exact Nat.pow_right_injective hp.two_le h
  let T : Finset ℕ := (Finset.Icc 1 s).filter (fun j => Nat.Prime (Q j) ∧ Q j ∣ n)
  have hTmem : ∀ j, j ∈ T ↔ (1 ≤ j ∧ j ≤ s ∧ Nat.Prime (Q j) ∧ Q j ∣ n) := by
    intro j
    simp [T, Finset.mem_filter, Finset.mem_Icc, and_assoc]
  have hqT_sub : T.image Q ⊆ n.primeFactors := by
    intro l hl
    rw [Finset.mem_image] at hl
    obtain ⟨j, hjT, rfl⟩ := hl
    exact Nat.Prime.mem_primeFactors (hTmem j |>.mp hjT).2.2.1 (hTmem j |>.mp hjT).2.2.2 hn0
  have hpf_sub : n.primeFactors ⊆ insert 2 (insert 3 (T.image Q)) := by
    intro l hl
    have hlprime : Nat.Prime l := (Nat.mem_primeFactors.mp hl).1
    have hldvd : l ∣ n := (Nat.mem_primeFactors.mp hl).2.1
    rcases prime_dvd_candidate p s hp hodd hp3 hs hφ hlprime hldvd with h2 | h3 | ⟨j, hj1, hjs, hjeq⟩
    · rw [h2]; simp
    · rw [h3]; simp
    · have hjT : j ∈ T := by
        rw [hTmem]
        exact ⟨hj1, hjs, by show Nat.Prime (2 * p ^ j + 1); rw [← hjeq]; exact hlprime,
          by show 2 * p ^ j + 1 ∣ n; rw [← hjeq]; exact hldvd⟩
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_image]
      right; right
      exact ⟨j, hjT, by show Q j = l; simp [Q]; omega⟩
  have hQfacp : ∀ j, (Q j - 1).factorization p = j := by
    intro j
    have hQj : Q j - 1 = 2 * p ^ j := by simp [Q]
    rw [hQj]
    exact factorization_two_mul_pow_p p j hp hp2
  have hQfac2 : ∀ j, (Q j - 1).factorization 2 = 1 := by
    intro j
    have hQj : Q j - 1 = 2 * p ^ j := by simp [Q]
    rw [hQj]
    exact factorization_two_mul_pow_two p j hp hodd
  have hQ_ge : ∀ j ∈ T, 11 ≤ Q j := by
    intro j hj
    have hj1 : 1 ≤ j := (hTmem j |>.mp hj).1
    have h1 : p ≤ p ^ j := Nat.le_self_pow (by omega : j ≠ 0) p
    simp [Q]; omega
  have h3notimg : (3:ℕ) ∉ T.image Q := by
    rw [Finset.mem_image]
    rintro ⟨j, hjT, hj⟩
    have := hQ_ge j hjT
    omega
  -- p-adic partition
  have himg1 : ∑ l ∈ T.image Q, (l - 1).factorization p = ∑ j ∈ T, j := by
    rw [Finset.sum_image (fun i _ j _ hij => hQinj hij)]
    exact Finset.sum_congr rfl (fun j _ => hQfacp j)
  have hdiff1 : ∑ l ∈ n.primeFactors \ T.image Q, (l - 1).factorization p = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    rw [Finset.mem_sdiff] at hl
    obtain ⟨hlpf, hlimg⟩ := hl
    have h := hpf_sub hlpf
    rw [Finset.mem_insert, Finset.mem_insert] at h
    rcases h with h2 | h3 | himg
    · subst h2; simp [Nat.factorization_one]
    · subst h3
      exact Nat.factorization_eq_zero_of_not_dvd (by
        intro hd
        have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
        omega)
    · exact absurd himg hlimg
  have hR1 : ∑ l ∈ n.primeFactors, (l - 1).factorization p = ∑ j ∈ T, j := by
    have hsplit := Finset.sum_sdiff (s₁ := T.image Q) (s₂ := n.primeFactors)
      (f := fun l => (l - 1).factorization p) hqT_sub
    rw [hdiff1, himg1] at hsplit
    omega
  have hpsum := sum_factor_sub_one_factorization_p p s n hp hodd hp3 hs hφ
  have hms : ∑ j ∈ T, j = s := hR1.symm.trans hpsum
  -- 2-adic partition
  have hφfac2 : (Nat.totient n).factorization 2 = 1 := by
    rw [hφ]; exact factorization_two_mul_pow_two p s hp hodd
  have hident := Nat.totient_mul_prod_primeFactors n
  have hfacEq2 : (Nat.totient n * ∏ l ∈ n.primeFactors, l).factorization 2
      = (n * ∏ l ∈ n.primeFactors, (l - 1)).factorization 2 := by rw [hident]
  have hA1 : Nat.totient n ≠ 0 := by rw [hφ]; positivity
  have hA2 : (∏ l ∈ n.primeFactors, l) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro l hl
    exact (Nat.mem_primeFactors.mp hl).1.ne_zero
  have hB2 : (∏ l ∈ n.primeFactors, (l - 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro l hl
    have h2 := (Nat.mem_primeFactors.mp hl).1.two_le
    omega
  rw [Nat.factorization_mul hA1 hA2, Nat.factorization_mul hn0 hB2,
      Finsupp.add_apply, Finsupp.add_apply] at hfacEq2
  have hsumL2 : (∏ l ∈ n.primeFactors, l).factorization 2
      = ∑ l ∈ n.primeFactors, (l).factorization 2 := by
    have h := Nat.factorization_prod (S := n.primeFactors) (g := fun l => l)
      (fun l hl => (Nat.mem_primeFactors.mp hl).1.ne_zero)
    rw [h]
    simpa using Finset.sum_apply 2 n.primeFactors (fun l => (l).factorization)
  have hsumR2 : (∏ l ∈ n.primeFactors, (l - 1)).factorization 2
      = ∑ l ∈ n.primeFactors, (l - 1).factorization 2 := by
    have h := Nat.factorization_prod (S := n.primeFactors) (g := fun l => l - 1)
      (fun l hl => by
        have h2 := (Nat.mem_primeFactors.mp hl).1.two_le
        omega)
    rw [h]
    simpa using Finset.sum_apply 2 n.primeFactors (fun l => (l - 1).factorization)
  have hL2val : ∑ l ∈ n.primeFactors, (l).factorization 2
      = if 2 ∈ n.primeFactors then 1 else 0 := by
    have hval : ∀ l ∈ n.primeFactors, (l).factorization 2 = if l = 2 then 1 else 0 := by
      intro l hl
      rw [Nat.Prime.factorization (Nat.mem_primeFactors.mp hl).1]
      by_cases h : l = 2
      · subst h; simp
      · rw [Finsupp.single_eq_of_ne (by omega : (2:ℕ) ≠ l)]
        simp [h]
    rw [Finset.sum_congr rfl hval, Finset.sum_ite_eq' n.primeFactors 2 (fun _ => (1:ℕ))]
  have himg2 : ∑ l ∈ T.image Q, (l - 1).factorization 2 = T.card := by
    rw [Finset.sum_image (fun i _ j _ hij => hQinj hij)]
    rw [Finset.sum_congr rfl (fun j _ => hQfac2 j)]
    simp
  have hdiff2 : ∑ l ∈ n.primeFactors \ T.image Q, (l - 1).factorization 2
      = n.factorization 3 := by
    have hmem : ∀ l ∈ n.primeFactors \ T.image Q, l = 2 ∨ l = 3 := by
      intro l hl
      rw [Finset.mem_sdiff] at hl
      obtain ⟨hlpf, hlimg⟩ := hl
      have h := hpf_sub hlpf
      rw [Finset.mem_insert, Finset.mem_insert] at h
      rcases h with h2 | h3 | himg
      · exact Or.inl h2
      · exact Or.inr h3
      · exact absurd himg hlimg
    have hsum_eq : ∑ l ∈ n.primeFactors \ T.image Q, (l - 1).factorization 2
        = if (3:ℕ) ∈ n.primeFactors \ T.image Q then 1 else 0 := by
      rw [← Finset.sum_ite_eq' (n.primeFactors \ T.image Q) 3 (fun _ => (1:ℕ))]
      apply Finset.sum_congr rfl
      intro l hl
      rcases hmem l hl with h2 | h3
      · subst h2; simp [Nat.factorization_one]
      · subst h3; norm_num
    rw [hsum_eq]
    by_cases h3pf : 3 ∈ n.primeFactors
    · have h3in : 3 ∈ n.primeFactors \ T.image Q := by
        rw [Finset.mem_sdiff]; exact ⟨h3pf, h3notimg⟩
      rw [if_pos h3in]
      have hpos : 0 < n.factorization 3 :=
        Nat.Prime.factorization_pos_of_dvd (by norm_num) hn0 (Nat.mem_primeFactors.mp h3pf).2.1
      omega
    · have h3out : 3 ∉ n.primeFactors \ T.image Q := by
        rw [Finset.mem_sdiff]; intro h; exact h3pf h.1
      rw [if_neg h3out]
      have hnd : ¬ 3 ∣ n := fun hd =>
        h3pf (Nat.Prime.mem_primeFactors (by norm_num) hd hn0)
      exact (Nat.factorization_eq_zero_of_not_dvd hnd).symm
  have hR2 : ∑ l ∈ n.primeFactors, (l - 1).factorization 2
      = n.factorization 3 + T.card := by
    have hsplit := Finset.sum_sdiff (s₁ := T.image Q) (s₂ := n.primeFactors)
      (f := fun l => (l - 1).factorization 2) hqT_sub
    rw [hdiff2, himg2] at hsplit
    omega
  rw [hφfac2, hsumL2, hsumR2, hL2val, hR2] at hfacEq2
  -- hfacEq2 : 1 + (if 2 ∈ pf then 1 else 0) = n.fac 2 + (n.fac 3 + T.card)
  -- t ≥ 1
  have ht1 : 1 ≤ T.card := by
    by_contra h
    have h0 : T.card = 0 := by omega
    have hTempty : T = ∅ := Finset.card_eq_zero.mp h0
    rw [hTempty] at hms
    simp at hms
    omega
  -- derive u ∈ {0,1} and e + t = 1
  have hu01 : n.factorization 2 = 0 ∨ n.factorization 2 = 1 := by
    by_cases hu : n.factorization 2 = 0
    · exact Or.inl hu
    · have hupos : 0 < n.factorization 2 := Nat.pos_of_ne_zero hu
      have h2mem : 2 ∈ n.primeFactors := by
        rw [Nat.mem_primeFactors]
        refine ⟨by norm_num, ?_, hn0⟩
        by_contra hnd
        rw [Nat.factorization_eq_zero_of_not_dvd hnd] at hupos
        omega
      rw [if_pos h2mem] at hfacEq2
      have : n.factorization 2 = 1 := by
        by_contra hne
        have h2le : 2 ≤ n.factorization 2 := by omega
        have hge : 2 ≤ n.factorization 2 := h2le
        have : n.factorization 3 + T.card = 0 := by omega
        omega
      exact Or.inr this
  have het : n.factorization 3 + T.card = 1 := by
    by_cases hu : n.factorization 2 = 0
    · have h2not : 2 ∉ n.primeFactors := by
        intro h2pf
        have hpos := Nat.Prime.factorization_pos_of_dvd (by norm_num) hn0
          (Nat.mem_primeFactors.mp h2pf).2.1
        omega
      rw [if_neg h2not, hu] at hfacEq2
      omega
    · have hupos : 0 < n.factorization 2 := Nat.pos_of_ne_zero hu
      have h2mem : 2 ∈ n.primeFactors := by
        rw [Nat.mem_primeFactors]
        refine ⟨by norm_num, ?_, hn0⟩
        by_contra hnd
        rw [Nat.factorization_eq_zero_of_not_dvd hnd] at hupos
        omega
      rw [if_pos h2mem] at hfacEq2
      have hu1 : n.factorization 2 = 1 := by
        rcases hu01 with h | h
        · omega
        · exact h
      rw [hu1] at hfacEq2
      omega
  have ht_eq : T.card = 1 := by omega
  have he_eq : n.factorization 3 = 0 := by omega
  -- T = {s}
  obtain ⟨j0, hj0⟩ := Finset.card_eq_one.mp ht_eq
  have hsum_s : j0 = s := by
    rw [hj0] at hms
    simpa using hms
  have hT_eq : T = {s} := by
    rw [← hsum_s]
    exact hj0
  have hs_mem : s ∈ T := by rw [hT_eq]; simp
  have hs_data := (hTmem s).mp hs_mem
  have hqprime : Nat.Prime (2 * p ^ s + 1) := by
    have := hs_data.2.2.1
    simpa [Q] using this
  have hqdvd : Q s ∣ n := hs_data.2.2.2
  have hqfac : n.factorization (Q s) = 1 := by
    have hle : n.factorization (Q s) ≤ 1 := factorization_q_le_one p s s n hp hodd hs hqprime hφ
    have hpos : 0 < n.factorization (Q s) :=
      Nat.Prime.factorization_pos_of_dvd hqprime hn0 hqdvd
    omega
  -- support ⊆ {2, Q s}
  have hsupp : n.primeFactors ⊆ ({2, Q s} : Finset ℕ) := by
    intro l hl
    have h := hpf_sub hl
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_image] at h
    rcases h with h2 | h3 | ⟨j, hjT, hjeq⟩
    · rw [h2]; simp
    · exfalso
      have h3pf : (3:ℕ) ∈ n.primeFactors := by rw [← h3]; exact hl
      have hpos := Nat.Prime.factorization_pos_of_dvd (by norm_num) hn0
        (Nat.mem_primeFactors.mp h3pf).2.1
      rw [he_eq] at hpos
      omega
    · have hj : j = s := by
        have hmem : j ∈ ({s} : Finset ℕ) := by rw [← hT_eq]; exact hjT
        simpa using hmem
      subst hj
      rw [← hjeq]
      simp
  have hq_ne_two : Q s ≠ 2 := by
    have : 11 ≤ Q s := hQ_ge s hs_mem
    omega
  have hn_split : n = 2 ^ (n.factorization 2) * Q s := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
    rw [Finsupp.prod_of_support_subset (f := n.factorization)
      (s := ({2, Q s} : Finset ℕ)) hsupp (fun x k => x ^ k) (fun i _ => pow_zero i)]
    rw [Finset.prod_pair (by omega : (2:ℕ) ≠ Q s)]
    rw [hqfac, pow_one]
  constructor
  · exact hqprime
  · rcases hu01 with hu0 | hu1
    · left
      rw [hn_split, hu0]
      simp [Q]
    · right
      rw [hn_split, hu1]
      norm_num [Q]

/-! ## The three frozen targets -/

/-- Proposition 3.5 (Master formula). -/
theorem master_formula : master_formula_statement := by
  intro p s hp hodd hp3 hs
  have hp5 : 5 ≤ p := five_le_of_odd_prime_ne_three hp hodd hp3
  constructor
  · intro hq
    ext n
    constructor
    · intro hn
      have hφ : Nat.totient n = 2 * p ^ s := hn
      obtain ⟨-, hcase⟩ := key_classification p s n hp hodd hp3 hs hφ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hcase with h | h
      · exact Or.inl h
      · exact Or.inr h
    · intro hn
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
      rcases hn with h | h
      · rw [h]
        show Nat.totient (2 * p ^ s + 1) = 2 * p ^ s
        rw [Nat.totient_prime hq]
        omega
      · rw [h]
        show Nat.totient (2 * (2 * p ^ s + 1)) = 2 * p ^ s
        have hqodd : Odd (2 * p ^ s + 1) := ⟨p ^ s, by ring⟩
        have hcop : Nat.Coprime 2 (2 * p ^ s + 1) :=
          (Nat.coprime_two_right.mpr hqodd).symm
        rw [Nat.totient_mul hcop, Nat.totient_two, Nat.totient_prime hq]
        omega
  · intro hq
    ext n
    constructor
    · intro hn
      have hφ : Nat.totient n = 2 * p ^ s := hn
      obtain ⟨hqp, -⟩ := key_classification p s n hp hodd hp3 hs hφ
      exact hq hqp
    · intro hn
      simp at hn

/-- Theorem 3.7 (even): `X_{2p^s} = ∅` for even `s`. -/
theorem even_case : even_statement := by
  intro p s hp hodd hp3 hs0 hse
  have hs : 1 ≤ s := hs0
  have hnp := not_prime_candidate_of_even p s hp hodd hp3 hs0 hse
  ext n
  constructor
  · intro hn
    have hφ : Nat.totient n = 2 * p ^ s := hn
    obtain ⟨hqp, -⟩ := key_classification p s n hp hodd hp3 hs hφ
    exact absurd hqp hnp
  · intro hn
    simp at hn

/-- Theorem 3.8 (odd): the master formula at odd `s`. -/
theorem odd_case : odd_statement := by
  intro p s hp hodd hp3 hs0 hso
  have hs : 1 ≤ s := hs0
  have hp5 : 5 ≤ p := five_le_of_odd_prime_ne_three hp hodd hp3
  constructor
  · intro hq
    ext n
    constructor
    · intro hn
      have hφ : Nat.totient n = 2 * p ^ s := hn
      obtain ⟨-, hcase⟩ := key_classification p s n hp hodd hp3 hs hφ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hcase with h | h
      · exact Or.inl h
      · exact Or.inr h
    · intro hn
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
      rcases hn with h | h
      · rw [h]
        show Nat.totient (2 * p ^ s + 1) = 2 * p ^ s
        rw [Nat.totient_prime hq]
        omega
      · rw [h]
        show Nat.totient (2 * (2 * p ^ s + 1)) = 2 * p ^ s
        have hqodd : Odd (2 * p ^ s + 1) := ⟨p ^ s, by ring⟩
        have hcop : Nat.Coprime 2 (2 * p ^ s + 1) :=
          (Nat.coprime_two_right.mpr hqodd).symm
        rw [Nat.totient_mul hcop, Nat.totient_two, Nat.totient_prime hq]
        omega
  · intro hq
    ext n
    constructor
    · intro hn
      have hφ : Nat.totient n = 2 * p ^ s := hn
      obtain ⟨hqp, -⟩ := key_classification p s n hp hodd hp3 hs hφ
      exact hq hqp
    · intro hn
      simp at hn

end DsBatch.P12
