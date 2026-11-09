import Mathlib

/-!
# P14 — The abstract counting lemma

This file isolates the Cauchy–Frobenius (Burnside) counting argument used in
the proof of Theorem `thMain` of arXiv 2610.03151.

Given a finite group `H` acting on a finite type `X`, if for every nonidentity
`h : H` the centralizer `C_H(h)` has order dividing the number of fixed points
of `h` on `X`, then `|H|` divides `|X|`.

The proof is the one in the paper: Burnside's lemma expresses
`∑ h, |Fix(h)|` as a multiple of `|H|`; grouping the sum by conjugacy classes,
every nonidentity class contributes a multiple of `|H|` because its size is
`|H| / |C_H(h)|` and `|C_H(h)|` divides the corresponding fixed-point count.
Hence the identity class, whose contribution is `|X|`, also contributes a
multiple of `|H|`.
-/

namespace DsBatch.P14

open MulAction
open scoped BigOperators

/-- Conjugating the acting element does not change the number of fixed points. -/
theorem card_fixedBy_of_eq_conj {H X : Type*} [Group H] [MulAction H X] [Fintype X]
    {g h : H} (c : H) (hc : c * g * c⁻¹ = h) :
    Nat.card (MulAction.fixedBy X g) = Nat.card (MulAction.fixedBy X h) := by
  show (MulAction.fixedBy X g).ncard = (MulAction.fixedBy X h).ncard
  rw [← hc, ← MulAction.smul_fixedBy (α := X) g c, Set.ncard_smul_set]

/-- **Counting lemma.**  If `|C_H(h)|` divides `|Fix_X(h)|` for every
`h ≠ 1`, then `|H|` divides `|X|`. -/
theorem card_dvd_card_of_centralizer_card_dvd_fixedBy
    {H X : Type*} [Group H] [Fintype H] [MulAction H X] [Fintype X]
    (hdiv : ∀ h : H, h ≠ 1 →
      Nat.card (MulAction.stabilizer (ConjAct H) h) ∣
        Nat.card (MulAction.fixedBy X h)) :
    Nat.card H ∣ Nat.card X := by
  classical
  suffices hmain : Fintype.card H ∣ Fintype.card X by
    simpa using hmain
  let fiber : ConjClasses H → Finset H := fun c => Finset.univ.filter (fun h => ConjClasses.mk h = c)
  let F : ConjClasses H → ℕ := fun c => ∑ h ∈ fiber c, Fintype.card (MulAction.fixedBy X h)
  have hburn : (∑ h : H, Fintype.card (MulAction.fixedBy X h)) =
      Fintype.card (Quotient (MulAction.orbitRel H X)) * Fintype.card H :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H X
  have hdvd_total : Fintype.card H ∣ (∑ h : H, Fintype.card (MulAction.fixedBy X h)) := by
    rw [hburn]
    exact Nat.dvd_mul_left (Fintype.card H) (Fintype.card (Quotient (MulAction.orbitRel H X)))
  have hfiber_dvd : ∀ c : ConjClasses H, c ≠ (1 : ConjClasses H) → Fintype.card H ∣ F c := by
    intro c hc
    dsimp [F, fiber]
    let r : H := Quotient.out c
    have hrepr : ConjClasses.mk r = c := Quotient.out_eq c
    have hrne : r ≠ 1 := by
      intro h
      apply hc
      rw [← hrepr, h]
      exact ConjClasses.one_eq_mk_one.symm
    have hf : (Finset.univ.filter (fun h : H => ConjClasses.mk h = c)) = c.carrier.toFinset := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
      rw [ConjClasses.mem_carrier_iff_mk_eq]
    have hconst : ∀ h ∈ (Finset.univ.filter (fun h : H => ConjClasses.mk h = c)),
        Fintype.card (MulAction.fixedBy X h) = Fintype.card (MulAction.fixedBy X r) := by
      intro h hh
      have hmk : ConjClasses.mk h = c := (Finset.mem_filter.mp hh).2
      have hconj : ConjClasses.mk h = ConjClasses.mk r := by
        rw [hmk, hrepr]
      have hisconj : IsConj h r := (ConjClasses.mk_eq_mk_iff_isConj).mp hconj
      rcases (isConj_iff.mp hisconj) with ⟨g, hg⟩
      have hcard : Nat.card (MulAction.fixedBy X h) = Nat.card (MulAction.fixedBy X r) :=
        card_fixedBy_of_eq_conj (H := H) (X := X) g hg
      simpa using hcard
    have hsum_const :
        (∑ h ∈ (Finset.univ.filter (fun h : H => ConjClasses.mk h = c)),
          Fintype.card (MulAction.fixedBy X h))
        = (Finset.univ.filter (fun h : H => ConjClasses.mk h = c)).card * Fintype.card (MulAction.fixedBy X r) := by
      rw [Finset.sum_congr rfl hconst]
      rw [Finset.sum_const, nsmul_eq_mul]
      rfl
    have hfiber_card : (Finset.univ.filter (fun h : H => ConjClasses.mk h = c)).card = Fintype.card c.carrier := by
      rw [hf]
      rw [Set.toFinset_card]
    have hcardcarrier : Fintype.card c.carrier = Fintype.card H / Fintype.card (MulAction.stabilizer (ConjAct H) r) := by
      rw [← hrepr]
      exact ConjClasses.card_carrier (G := H) r
    have hdvd_fix : Fintype.card (MulAction.stabilizer (ConjAct H) r) ∣ Fintype.card (MulAction.fixedBy X r) := by
      simpa using hdiv r hrne
    have hdvd_group : Fintype.card (MulAction.stabilizer (ConjAct H) r) ∣ Fintype.card H := by
      have hsub : Nat.card (MulAction.stabilizer (ConjAct H) r) ∣ Nat.card H :=
        Subgroup.card_subgroup_dvd_card (MulAction.stabilizer (ConjAct H) r)
      simpa using hsub
    have hkey : Fintype.card H ∣
        (Fintype.card H / Fintype.card (MulAction.stabilizer (ConjAct H) r)) * Fintype.card (MulAction.fixedBy X r) := by
      let m := Fintype.card (MulAction.stabilizer (ConjAct H) r)
      let n := Fintype.card H
      let f := Fintype.card (MulAction.fixedBy X r)
      have hm_f : m ∣ f := hdvd_fix
      have hm_n : m ∣ n := hdvd_group
      change n ∣ (n / m) * f
      rw [show f = m * (f / m) from (Nat.mul_div_cancel' hm_f).symm]
      rw [← mul_assoc, show (n / m) * m = n from Nat.div_mul_cancel hm_n]
      exact Nat.dvd_mul_right n (f / m)
    rw [hsum_const, hfiber_card, hcardcarrier]
    exact hkey
  have hdecomp : (∑ c : ConjClasses H, F c) = ∑ h : H, Fintype.card (MulAction.fixedBy X h) := by
    dsimp [F, fiber]
    exact Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset H))
      (t := (Finset.univ : Finset (ConjClasses H)))
      (g := ConjClasses.mk)
      (fun i hi => Finset.mem_univ (ConjClasses.mk i))
      (fun h => Fintype.card (MulAction.fixedBy X h))
  have hF1 : F (1 : ConjClasses H) = Fintype.card X := by
    dsimp [F, fiber]
    have hfilter : (Finset.univ.filter (fun h : H => ConjClasses.mk h = (1 : ConjClasses H)) : Finset H) = {1} := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and]
      rw [ConjClasses.one_eq_mk_one, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left]
    rw [hfilter]
    simp
  have hsplit : F (1 : ConjClasses H) + (∑ c ∈ (Finset.univ.erase (1 : ConjClasses H)), F c) =
      ∑ c : ConjClasses H, F c := by
    exact Finset.add_sum_erase (s := (Finset.univ : Finset (ConjClasses H))) (f := F)
      (a := (1 : ConjClasses H)) (h := Finset.mem_univ (1 : ConjClasses H))
  have htail_dvd : Fintype.card H ∣ ∑ c ∈ (Finset.univ.erase (1 : ConjClasses H)), F c := by
    exact Finset.dvd_sum (s := (Finset.univ.erase (1 : ConjClasses H))) (a := Fintype.card H) (f := F)
      (fun c hc => by
        have hcne : c ≠ 1 := (Finset.mem_erase.mp hc).1
        exact hfiber_dvd c hcne)
  have htotal' : Fintype.card H ∣ ∑ c : ConjClasses H, F c := by
    rw [hdecomp]
    exact hdvd_total
  have hdiff : Fintype.card H ∣ (∑ c : ConjClasses H, F c) - (∑ c ∈ (Finset.univ.erase (1 : ConjClasses H)), F c) := by
    exact Nat.dvd_sub htotal' htail_dvd
  have hdiff_eq : (∑ c : ConjClasses H, F c) - (∑ c ∈ (Finset.univ.erase (1 : ConjClasses H)), F c) =
      F (1 : ConjClasses H) := by
    rw [← hsplit]
    exact Nat.add_sub_cancel_right (F (1 : ConjClasses H)) (∑ c ∈ (Finset.univ.erase (1 : ConjClasses H)), F c)
  rw [hdiff_eq] at hdiff
  rwa [hF1] at hdiff

/-- **Counting lemma**, stated with the centralizer instead of the stabilizer
under `ConjAct`. -/
theorem card_dvd_card_of_centralizer_card_dvd_fixedBy'
    {H X : Type*} [Group H] [Fintype H] [MulAction H X] [Fintype X]
    (hdiv : ∀ h : H, h ≠ 1 →
      Nat.card ↥(Subgroup.centralizer ({h} : Set H)) ∣
        Nat.card (MulAction.fixedBy X h)) :
    Nat.card H ∣ Nat.card X := by
  refine card_dvd_card_of_centralizer_card_dvd_fixedBy (H := H) (X := X) ?_
  intro h hh
  have hstab : MulAction.stabilizer (ConjAct H) h =
      Subgroup.centralizer ({h} : Set (ConjAct H)) := by
    have hh := ConjAct.stabilizer_eq_centralizer (G := H) h
    rw [show (ConjAct.toConjAct h : ConjAct H) = h from rfl] at hh
    exact hh
  rw [hstab]
  exact hdiv h hh

end DsBatch.P14
