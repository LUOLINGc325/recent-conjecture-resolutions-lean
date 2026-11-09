import DsBatch.P14.Basic
import DsBatch.P14.Counting
import DsBatch.P14.Claim
import DsBatch.P14.Coset

/-!
# P14 — Proof of the main theorem

We formalise the proof of Theorem `thMain` of arXiv 2610.03151 by induction on
`|K|`, following the paper: choose a maximal admissible normal subgroup `T` of
`K`, use the maximality claim `(H/T) ∩ Z(K/T) = 1`, and apply the abstract
Cauchy–Frobenius counting lemma to the action of `H/T` on the set of `T`-cosets
contained in the solubilizer.
-/

namespace DsBatch.P14

open scoped Pointwise
open MulAction

universe u

variable {G : Type u} [Group G]

/-- `threeGen` with the trivial subgroup is the closure of `{x, a}`. -/
lemma threeGen_bot {x : G} {K : Subgroup G} (a : K) :
    threeGen x (a : G) (⊥ : Subgroup K) = Subgroup.closure ({x, (a : G)} : Set G) := by
  rw [threeGen, Subgroup.map_bot, Subgroup.coe_bot, Subgroup.closure_union_one]

/-- If `⟨x, a, T⟩` is soluble, then `a * t` still belongs to the solubilizer,
for every `t ∈ T`. -/
lemma mul_mem_solubilizerIn_of_solvable {x : G} {K : Subgroup G}
    (T : Subgroup K) {a : K} (hsol : Group.IsSolvable (threeGen x (a : G) T))
    {t : K} (ht : t ∈ T) : a * t ∈ solubilizerIn x K := by
  have hle : Subgroup.closure ({x, ((a * t : K) : G)} : Set G) ≤
      threeGen x (a : G) T := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_insert_iff] at hy
    rcases hy with hyx | hya
    · rw [hyx]
      exact x_mem_threeGen
    · rw [Set.mem_singleton_iff] at hya
      rw [hya]
      have h : ((a * t : K) : G) = (a : G) * (t : G) := by simp
      rw [h]
      exact Subgroup.mul_mem _ a_mem_threeGen (coe_mem_threeGen_of_mem ht)
  haveI := hsol
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

/-- Auxiliary induction statement: for a subgroup `K` of cardinality `n`, the
normalizer inside `K` has order dividing the solubilizer inside `K`. -/
private theorem main_aux (x : G) [Finite G] :
    ∀ n : ℕ, ∀ K : Subgroup G, Nat.card ↥K = n →
      Nat.card ↥((normalizerOf x).subgroupOf K) ∣ Nat.card ↥(solubilizerIn x K) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K hK
    classical
    let H : Subgroup K := (normalizerOf x).subgroupOf K
    let A : Set K := solubilizerIn x K
    -- the admissible subgroups
    let Good : Subgroup K → Prop := fun T =>
      T ≤ H ∧
      (∀ k : K, ∀ t ∈ T, k * t * k⁻¹ ∈ T) ∧
      (∀ h : H, ∀ t ∈ T, (h : K) * t * (h : K)⁻¹ ∈ T) ∧
      (∀ a : K, a ∈ A → Group.IsSolvable (threeGen x (a : G) T))
    have hgood_bot : Good ⊥ := by
      refine ⟨bot_le, ?_, ?_, ?_⟩
      · intro k t ht
        rw [Subgroup.mem_bot] at ht
        subst ht
        simp
      · intro h t ht
        rw [Subgroup.mem_bot] at ht
        subst ht
        simp
      · intro a ha
        rw [threeGen_bot]
        exact ha
    have hfin : {T : Subgroup K | Good T}.Finite :=
      Set.finite_univ.subset (Set.subset_univ _)
    obtain ⟨T, hTgood, hTmax⟩ :=
      Set.Finite.exists_maximal hfin ⟨⊥, hgood_bot⟩
    obtain ⟨hTH, hTnormK, hTnormH, hTsol⟩ := hTgood
    haveI hTnormal : T.Normal := ⟨fun n hn k => hTnormK k n hn⟩
    -- the maximality claim
    have hclaim : H.map (QuotientGroup.mk' T) ⊓ Subgroup.center (K ⧸ T) = ⊥ := by
      apply claim_center_inf (x := x) (A := A) (H := H) (T := T)
      · intro h
        exact h.2
      · exact hTH
      · exact hTnormH
      · exact hTsol
      · intro T' hTT' hT'H hT'normK hT'normH hT'sol
        exact hTmax (y := T') ⟨hT'H, hT'normK, hT'normH, hT'sol⟩ hTT'
    -- `A` is a union of right `T`-cosets
    have hAunion : ∀ a ∈ A, ∀ t : K, t ∈ T → a * t ∈ A := by
      intro a ha t ht
      exact mul_mem_solubilizerIn_of_solvable T (hTsol a ha) ht
    -- cardinality of `H` in terms of `T` and `H/T`
    have hHcard : Nat.card ↥H =
        Nat.card ↥T * Nat.card ↥(H.map (QuotientGroup.mk' T)) :=
      card_eq_card_mul_card_map (G := K) (T := T) (H := H) hTH
    -- the quotient
    let Hbar : Subgroup (K ⧸ T) := H.map (QuotientGroup.mk' T)
    let Abar : Set (K ⧸ T) := QuotientGroup.mk' T '' A
    have hHbar_eq : Hbar = H.map (QuotientGroup.mk' T) := rfl
    -- conjugation action of `Hbar` on the quotient group
    haveI hQact : MulAction Hbar (K ⧸ T) :=
      { smul g q := (g : K ⧸ T) * q * (g : K ⧸ T)⁻¹
        one_smul q := by
          show ((1 : Hbar) : K ⧸ T) * q * ((1 : Hbar) : K ⧸ T)⁻¹ = q
          simp
        mul_smul g1 g2 q := by
          show ((g1 * g2 : Hbar) : K ⧸ T) * q * ((g1 * g2 : Hbar) : K ⧸ T)⁻¹ =
            (g1 : K ⧸ T) * ((g2 : K ⧸ T) * q * (g2 : K ⧸ T)⁻¹) * (g1 : K ⧸ T)⁻¹
          rw [Subgroup.coe_mul, mul_inv_rev]
          group }
    -- the set of `T`-cosets inside `A` is invariant
    have hAbar_smul : ∀ g : Hbar, ∀ q ∈ Abar,
        (g : K ⧸ T) * q * (g : K ⧸ T)⁻¹ ∈ Abar := by
      intro g q hq
      obtain ⟨a, haA, rfl⟩ := hq
      obtain ⟨h, hhH, hh⟩ := Subgroup.mem_map.mp g.2
      refine ⟨(h : K) * a * (h : K)⁻¹, ?_, ?_⟩
      · exact solubilizerIn_conj_mem (K := K) hhH haA
      · rw [map_mul, map_mul, map_inv, hh]
    let actA : MulAction Hbar Abar :=
      { smul g q := ⟨(g : K ⧸ T) * (q : K ⧸ T) * (g : K ⧸ T)⁻¹,
          hAbar_smul g q q.2⟩
        one_smul q := by
          apply Subtype.ext
          show ((1 : Hbar) : K ⧸ T) * (q : K ⧸ T) * ((1 : Hbar) : K ⧸ T)⁻¹ = (q : K ⧸ T)
          simp
        mul_smul g1 g2 q := by
          apply Subtype.ext
          show ((g1 * g2 : Hbar) : K ⧸ T) * (q : K ⧸ T) *
              ((g1 * g2 : Hbar) : K ⧸ T)⁻¹ =
            (g1 : K ⧸ T) * ((g2 : K ⧸ T) * (q : K ⧸ T) * (g2 : K ⧸ T)⁻¹) *
              (g1 : K ⧸ T)⁻¹
          rw [Subgroup.coe_mul, mul_inv_rev]
          group }
    letI hAbaract : MulAction Hbar Abar := actA
    have hsmul_apply : ∀ (g : Hbar) (q : Abar),
        ((g • q : Abar) : K ⧸ T) =
          (g : K ⧸ T) * (q : K ⧸ T) * (g : K ⧸ T)⁻¹ := fun g q => rfl
    -- the counting hypothesis
    have hcount : ∀ g : Hbar, g ≠ 1 →
        Nat.card ↥(Subgroup.centralizer ({g} : Set Hbar)) ∣
          Nat.card ↥(MulAction.fixedBy Abar g) := by
      intro g hg
      classical
      -- the centralizer of `g` in the quotient, its preimage `LK` in `K`, and the
      -- corresponding subgroup `L` of `G` (to which the induction hypothesis applies)
      let C : Subgroup (K ⧸ T) := Subgroup.centralizer ({(g : K ⧸ T)} : Set (K ⧸ T))
      let LK : Subgroup K := Subgroup.comap (QuotientGroup.mk' T) C
      let L : Subgroup G := LK.map K.subtype
      have hLle : L ≤ K := by
        intro y hy
        obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
        exact k.2
      have hTLK : T ≤ LK := by
        intro t ht
        change QuotientGroup.mk' T t ∈ C
        have h1 : QuotientGroup.mk' T t = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact ht
        rw [h1]
        exact C.one_mem
      -- `LK` is proper, otherwise `g` would be central in `K ⧸ T`
      have hLKne : LK ≠ ⊤ := by
        intro hLKtop
        have hcenter : (g : K ⧸ T) ∈ Subgroup.center (K ⧸ T) := by
          rw [Subgroup.mem_center_iff]
          intro q
          obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective T q
          have hkL : k ∈ LK := by
            rw [hLKtop]
            exact Subgroup.mem_top k
          have hkC : QuotientGroup.mk' T k ∈ C := hkL
          exact (Subgroup.mem_centralizer_iff.mp hkC (g : K ⧸ T) (by simp)).symm
        have hmem : (g : K ⧸ T) ∈ H.map (QuotientGroup.mk' T) ⊓
            Subgroup.center (K ⧸ T) := ⟨g.2, hcenter⟩
        rw [hclaim] at hmem
        have h1 : (g : K ⧸ T) = 1 := by simpa using hmem
        exact hg (Subtype.ext h1)
      have hLKcard : Nat.card ↥LK < Nat.card ↥K := by
        have h1 := Subgroup.card_lt_of_lt
          (lt_of_le_of_ne le_top hLKne : LK < (⊤ : Subgroup ↥K))
        rwa [Nat.card_congr (Subgroup.topEquiv (G := ↥K)).toEquiv] at h1
      have hcardL : Nat.card ↥L < Nat.card ↥K := by
        rw [show Nat.card ↥L = Nat.card ↥LK from
          (Nat.card_congr (Subgroup.equivMapOfInjective LK K.subtype
            (Subgroup.subtype_injective K)).toEquiv).symm]
        exact hLKcard
      have ihL := ih (Nat.card ↥L) (by rw [← hK]; exact hcardL) L rfl
      -- cardinal of the normalizer inside `L`, expressed in `K`
      have hNLcard : Nat.card ↥((normalizerOf x).subgroupOf L) = Nat.card ↥(H ⊓ LK) := by
        have h1 : Nat.card ↥((normalizerOf x).subgroupOf L) =
            Nat.card ↥(normalizerOf x ⊓ L) := by
          rw [← Subgroup.inf_subgroupOf_right (normalizerOf x) L]
          exact Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (inf_le_right : normalizerOf x ⊓ L ≤ L)).toEquiv
        have h2 : Nat.card ↥(normalizerOf x ⊓ L) = Nat.card ↥(H ⊓ LK) := by
          have hmap : (H ⊓ LK).map K.subtype = normalizerOf x ⊓ L := by
            rw [Subgroup.map_inf H LK K.subtype (Subgroup.subtype_injective K)]
            have hHmap : H.map K.subtype = normalizerOf x ⊓ K :=
              Subgroup.subgroupOf_map_subtype (normalizerOf x) K
            rw [hHmap]
            rw [inf_assoc, inf_eq_right.mpr hLle]
          rw [← hmap]
          exact (Nat.card_congr (Subgroup.equivMapOfInjective (H ⊓ LK) K.subtype
            (Subgroup.subtype_injective K)).toEquiv).symm
        rw [h1, h2]
      -- the elements of `LK` whose `(x, ·)`-group is soluble
      let AK : Set ↥LK :=
        {l : ↥LK | Group.IsSolvable (Subgroup.closure ({x, ((l : K) : G)} : Set G))}
      -- cardinal of the solubilizer inside `L`, expressed in `K`
      have hALeq : Nat.card ↥(solubilizerIn x L) = Nat.card ↥(A ∩ (LK : Set K)) := by
        have h1 : Nat.card ↥(solubilizerIn x L) = Nat.card ↥AK := by
          let e : ↥LK ≃* ↥L :=
            Subgroup.equivMapOfInjective LK K.subtype (Subgroup.subtype_injective K)
          have hiff : ∀ k : ↥LK, (k ∈ AK) ↔ (e k ∈ solubilizerIn x L) := fun k => Iff.rfl
          exact (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv hiff)).symm
        have h2 : Nat.card ↥AK = Nat.card ↥(A ∩ (LK : Set K)) := by
          refine Nat.card_congr
            { toFun := fun l => ⟨(l : K), ?_, ?_⟩
              invFun := fun k => ⟨⟨(k : K), k.2.2⟩, ?_⟩
              left_inv := fun l => rfl
              right_inv := fun k => rfl }
          · exact l.2
          · exact (l : LK).2
          · exact k.2.1
        rw [h1, h2]
      -- `A ∩ LK` is a union of right `T`-cosets
      have hS : ∀ s ∈ A ∩ (LK : Set K), ∀ t : K, t ∈ T →
          s * t ∈ A ∩ (LK : Set K) := by
        intro s hs t ht
        exact ⟨hAunion s hs.1 t ht, LK.mul_mem hs.2 (hTLK ht)⟩
      let Q : Set (K ⧸ T) := QuotientGroup.mk' T '' (A ∩ (LK : Set K))
      have hALcard : Nat.card ↥(A ∩ (LK : Set K)) = Nat.card ↥T * Nat.card ↥Q :=
        card_eq_card_mul_card_image (G := K) (T := T) (S := A ∩ (LK : Set K)) hS
      have hQsub : Q ⊆ Abar := by
        rintro q ⟨a, ⟨haA, haL⟩, rfl⟩
        exact ⟨a, haA, rfl⟩
      -- the image of `H ⊓ LK` in the quotient is `Hbar ⊓ C`
      have hHLmap : (H ⊓ LK).map (QuotientGroup.mk' T) = Hbar ⊓ C := by
        apply le_antisymm
        · intro q hq
          obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hq
          exact Subgroup.mem_inf.mpr
            ⟨Subgroup.mem_map.mpr ⟨k, hk.1, rfl⟩, Subgroup.mem_comap.mp hk.2⟩
        · intro q hq
          obtain ⟨hqH, hqC⟩ := Subgroup.mem_inf.mp hq
          obtain ⟨k, hkH, rfl⟩ := Subgroup.mem_map.mp hqH
          exact Subgroup.mem_map.mpr ⟨k, ⟨hkH, Subgroup.mem_comap.mpr hqC⟩, rfl⟩
      have hHLcard : Nat.card ↥(H ⊓ LK) = Nat.card ↥T * Nat.card ↥(Hbar ⊓ C) := by
        rw [← hHLmap]
        exact card_eq_card_mul_card_map (G := K) (T := T) (H := H ⊓ LK)
          (le_inf hTH hTLK)
      -- the fixed points of `g` on `A/T` are exactly the quotients of `A ∩ LK`
      have hfixQ : MulAction.fixedBy Abar g = {q : Abar | (q : K ⧸ T) ∈ Q} := by
        ext q
        rw [MulAction.mem_fixedBy]
        constructor
        · intro hq
          have hq' : (g : K ⧸ T) * (q : K ⧸ T) * (g : K ⧸ T)⁻¹ = (q : K ⧸ T) := by
            have hval := congrArg (fun z : Abar => (z : K ⧸ T)) hq
            rwa [hsmul_apply g q] at hval
          have hcomm : (g : K ⧸ T) * (q : K ⧸ T) = (q : K ⧸ T) * (g : K ⧸ T) := by
            calc (g : K ⧸ T) * (q : K ⧸ T)
                = ((g : K ⧸ T) * (q : K ⧸ T) * (g : K ⧸ T)⁻¹) * (g : K ⧸ T) := by
                  group
              _ = (q : K ⧸ T) * (g : K ⧸ T) := by rw [hq']
          obtain ⟨a, haA, hqa⟩ := q.2
          change (q : K ⧸ T) ∈ Q
          rw [← hqa]
          rw [← hqa] at hcomm
          refine ⟨a, ⟨haA, ?_⟩, rfl⟩
          change QuotientGroup.mk' T a ∈ C
          exact Subgroup.mem_centralizer_iff.mpr (fun z hz => by
            rw [Set.mem_singleton_iff] at hz
            rw [hz]
            exact hcomm)
        · intro hq
          obtain ⟨a, ⟨haA, haL⟩, hqa⟩ := hq
          have hqeq : q = ⟨QuotientGroup.mk' T a, hQsub ⟨a, ⟨haA, haL⟩, rfl⟩⟩ :=
            Subtype.ext hqa.symm
          rw [hqeq]
          have hcomm : (g : K ⧸ T) * (QuotientGroup.mk' T a) =
              (QuotientGroup.mk' T a) * (g : K ⧸ T) :=
            Subgroup.mem_centralizer_iff.mp (show QuotientGroup.mk' T a ∈ C from haL)
              (g : K ⧸ T) (by simp)
          apply Subtype.ext
          rw [hsmul_apply]
          show (g : K ⧸ T) * (QuotientGroup.mk' T a) * (g : K ⧸ T)⁻¹ = QuotientGroup.mk' T a
          rw [hcomm]
          group
      have hfixcard : Nat.card ↥(MulAction.fixedBy Abar g) = Nat.card ↥Q := by
        rw [hfixQ]
        exact Nat.card_congr
          { toFun := fun q => ⟨(q.1 : K ⧸ T), q.2⟩
            invFun := fun z => ⟨⟨(z : K ⧸ T), hQsub z.2⟩, z.2⟩
            left_inv := fun q => rfl
            right_inv := fun z => rfl }
      -- the centralizer of `g` inside `Hbar` is `Hbar ⊓ C`
      have hcentcard : Nat.card ↥(Subgroup.centralizer ({g} : Set Hbar)) =
          Nat.card ↥(Hbar ⊓ C) := by
        have h1 : Subgroup.centralizer ({g} : Set Hbar) = C.subgroupOf Hbar := by
          ext h
          have hleft : h ∈ Subgroup.centralizer ({g} : Set Hbar) ↔
              ((g : K ⧸ T) * (h : K ⧸ T) = (h : K ⧸ T) * (g : K ⧸ T)) := by
            rw [Subgroup.mem_centralizer_iff]
            simp only [Set.mem_singleton_iff, forall_eq]
            constructor
            · intro hh
              have hval := congrArg (fun z : Hbar => (z : K ⧸ T)) hh
              simpa only [Subgroup.coe_mul] using hval
            · intro hh
              apply Subtype.ext
              simpa only [Subgroup.coe_mul] using hh
          have hright : h ∈ C.subgroupOf Hbar ↔
              ((g : K ⧸ T) * (h : K ⧸ T) = (h : K ⧸ T) * (g : K ⧸ T)) := by
            rw [Subgroup.mem_subgroupOf]
            change (h : K ⧸ T) ∈ Subgroup.centralizer ({(g : K ⧸ T)} : Set (K ⧸ T)) ↔
              ((g : K ⧸ T) * (h : K ⧸ T) = (h : K ⧸ T) * (g : K ⧸ T))
            rw [Subgroup.mem_centralizer_iff]
            simp only [Set.mem_singleton_iff, forall_eq]
          exact hleft.trans hright.symm
        rw [h1]
        have h2 : C.subgroupOf Hbar = (Hbar ⊓ C).subgroupOf Hbar :=
          (Subgroup.inf_subgroupOf_left C Hbar).symm
        rw [h2]
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (inf_le_left : Hbar ⊓ C ≤ Hbar)).toEquiv
      -- combine with the induction hypothesis
      have hdvd1 : Nat.card ↥(H ⊓ LK) ∣ Nat.card ↥(A ∩ (LK : Set K)) := by
        rw [← hNLcard, ← hALeq]
        exact ihL
      rw [hHLcard, hALcard] at hdvd1
      have hTpos : 0 < Nat.card ↥T := Nat.card_pos
      have hdvd2 : Nat.card ↥(Hbar ⊓ C) ∣ Nat.card ↥Q :=
        (Nat.mul_dvd_mul_iff_left hTpos).mp hdvd1
      rw [hcentcard, hfixcard]
      exact hdvd2
    haveI : Fintype ↥Hbar := Fintype.ofFinite _
    haveI : Fintype ↥Abar := Fintype.ofFinite _
    have hdvd : Nat.card ↥Hbar ∣ Nat.card ↥Abar :=
      card_dvd_card_of_centralizer_card_dvd_fixedBy' (H := Hbar) (X := Abar) hcount
    -- cardinality of `A` in terms of `T` and `A/T`
    have hAcard : Nat.card ↥A = Nat.card ↥T * Nat.card ↥Abar :=
      card_eq_card_mul_card_image (G := K) (T := T) (S := A) hAunion
    rw [hHcard, hAcard]
    exact Nat.mul_dvd_mul_left (Nat.card ↥T) hdvd

/-- The main theorem, for a general finite group. -/
theorem main_of_finite (x : G) [Finite G] (K : Subgroup G) :
    Nat.card ↥(normalizerOf x ⊓ K) ∣ Nat.card ↥(solubilizerIn x K) := by
  have hmain := main_aux (x := x) (Nat.card ↥K) K rfl
  have hcard : Nat.card ↥(normalizerOf x ⊓ K) =
      Nat.card ↥((normalizerOf x).subgroupOf K) := by
    rw [← Subgroup.inf_subgroupOf_right (normalizerOf x) K]
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_right)).toEquiv).symm
  rwa [hcard]

end DsBatch.P14
