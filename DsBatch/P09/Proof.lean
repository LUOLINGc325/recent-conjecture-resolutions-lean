import DsBatch.P09.Cert

/-!
# P09 — proof lemmas

Everything needed to derive the five targets from the kernel computations in
`DsBatch/P09/Cert.lean`.
-/

namespace DsBatch.P09

open SimpleGraph

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

variable {n : Nat}

/-! ## Correctness of the subset enumeration -/

/-- Every call of `go` that returns `true` and that has reached its fuel bound
certifies `chk` on the union of the accumulated set with any `k`-element set of
indices `≥ i`. -/
lemma go_spec (chk : Finset (Fin n) → Bool) :
    ∀ fuel i k (s : Finset (Fin n)), go chk fuel i k s = true → i + fuel = n →
      ∀ t : Finset (Fin n), t.card = k → (∀ x ∈ t, i ≤ (x : Nat)) →
        (∀ x, x ∈ s → x ∈ t → False) → chk (s ∪ t) = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro i k s hgo hinv t hcard hge hdisj
    have hin : i = n := by omega
    by_cases hk : k = 0
    · subst hk
      simp only [go] at hgo
      have ht : t = ∅ := Finset.card_eq_zero.mp hcard
      subst ht
      simpa using hgo
    · have ht : t = ∅ := by
        ext x
        simp only [Finset.notMem_empty, iff_false]
        intro hx
        have h1 : i ≤ (x : Nat) := hge x hx
        have h2 : (x : Nat) < n := x.isLt
        omega
      have hc : t.card = 0 := by simp [ht]
      omega
  | succ fuel ih =>
    intro i k s hgo hinv t hcard hge hdisj
    by_cases hk : k = 0
    · subst hk
      simp only [go] at hgo
      have ht : t = ∅ := Finset.card_eq_zero.mp hcard
      subst ht
      simpa using hgo
    · by_cases hi : i < n
      · have hgo' : (go chk fuel (i + 1) (k - 1) (insert ⟨i, hi⟩ s) &&
            go chk fuel (i + 1) k s) = true := by
          simpa only [go, if_neg hk, dif_pos hi] using hgo
        rw [Bool.and_eq_true] at hgo'
        obtain ⟨hgo1, hgo2⟩ := hgo'
        by_cases hmem : (⟨i, hi⟩ : Fin n) ∈ t
        · have hcard' : (t.erase ⟨i, hi⟩).card = k - 1 := by
            rw [Finset.card_erase_of_mem hmem, hcard]
          have hge' : ∀ x ∈ t.erase ⟨i, hi⟩, (i + 1) ≤ (x : Nat) := by
            intro x hx
            have hx' : x ∈ t := Finset.mem_of_mem_erase hx
            have hne : x ≠ ⟨i, hi⟩ := Finset.ne_of_mem_erase hx
            have h1 : i ≤ (x : Nat) := hge x hx'
            have h2 : (x : Nat) ≠ i := fun h2' => hne (Fin.ext h2')
            omega
          have hdisj' : ∀ x, x ∈ insert ⟨i, hi⟩ s → x ∈ t.erase ⟨i, hi⟩ → False := by
            intro x hx1 hx2
            have hxt : x ∈ t := Finset.mem_of_mem_erase hx2
            rcases Finset.mem_insert.mp hx1 with rfl | hxs
            · exact absurd hx2 (by simp)
            · exact hdisj x hxs hxt
          have hinv' : (i + 1) + fuel = n := by omega
          have hres := ih (i + 1) (k - 1) (insert ⟨i, hi⟩ s) hgo1 hinv'
            (t.erase ⟨i, hi⟩) hcard' hge' hdisj'
          have hset : insert ⟨i, hi⟩ s ∪ t.erase ⟨i, hi⟩ = s ∪ t := by
            have ht_eq : t = insert ⟨i, hi⟩ (t.erase ⟨i, hi⟩) :=
              (Finset.insert_erase hmem).symm
            conv_rhs => rw [ht_eq]
            ext x
            simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
            tauto
          rwa [hset] at hres
        · have hge' : ∀ x ∈ t, (i + 1) ≤ (x : Nat) := by
            intro x hx
            have h1 : i ≤ (x : Nat) := hge x hx
            have h2 : (x : Nat) ≠ i := by
              intro h2'
              exact hmem (by rw [show (⟨i, hi⟩ : Fin n) = x from (Fin.ext h2').symm]; exact hx)
            omega
          have hinv' : (i + 1) + fuel = n := by omega
          exact ih (i + 1) k s hgo2 hinv' t hcard hge' hdisj
      · have hle : n ≤ i := by omega
        have ht : t = ∅ := by
          ext x
          simp only [Finset.notMem_empty, iff_false]
          intro hx
          have h1 : i ≤ (x : Nat) := hge x hx
          have h2 : (x : Nat) < n := x.isLt
          omega
        have hc : t.card = 0 := by simp [ht]
        omega

/-! ## Bitmask lemmas -/

lemma bmask_lt (l : List (Fin 27)) : bmask l < 2 ^ 27 := by
  induction l with
  | nil => simp [bmask]
  | cons a l ih =>
    have h1 : (1 <<< (a : Nat)) < 2 ^ 27 := by
      rw [Nat.one_shiftLeft]
      exact Nat.pow_lt_pow_right (by decide) a.isLt
    change (bmask l ||| (1 <<< (a : Nat))) < 2 ^ 27
    exact Nat.or_lt_two_pow ih h1

lemma bmask_testBit (l : List (Fin 27)) (i : Fin 27) :
    (bmask l).testBit (i : Nat) = true ↔ i ∈ l := by
  induction l with
  | nil => simp [bmask]
  | cons a l ih =>
    change ((bmask l) ||| (1 <<< (a : Nat))).testBit (i : Nat) = true ↔ i ∈ a :: l
    rw [Nat.testBit_lor, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_iff, ih, List.mem_cons, Fin.val_inj]
    tauto

lemma mfoldr_testBit (m : Multiset (Fin 27)) (i : Fin 27) :
    (m.foldr (fun (j : Fin 27) m => m ||| (1 <<< (j : Nat))) 0).testBit (i : Nat) = true ↔
      i ∈ m := by
  induction m using Quot.inductionOn with
  | h l =>
    change (bmask l).testBit (i : Nat) = true ↔ i ∈ (l : Multiset (Fin 27))
    rw [bmask_testBit, Multiset.mem_coe]

lemma maskOf_testBit (s : Finset (Fin 27)) (i : Fin 27) :
    (maskOf s).testBit (i : Nat) = true ↔ i ∈ s := by
  have h := mfoldr_testBit s.val i
  simpa [maskOf, Finset.mem_val] using h

/-- If the bitmask of `l` is not covered by the bitmask of `s`, then `l` has an
element outside `s`. -/
lemma exists_not_mem_of_mask_ne {l : List (Fin 27)} {s : Finset (Fin 27)}
    (h : bmask l &&& maskOf s ≠ bmask l) : ∃ j ∈ l, j ∉ s := by
  by_contra hc
  have hc' : ∀ j : Fin 27, j ∈ l → j ∈ s := by
    intro j hj
    by_contra hjs
    exact hc ⟨j, hj, hjs⟩
  apply h
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_land]
  by_cases hn : n < 27
  · cases hb : (bmask l).testBit n with
    | false => simp [hb]
    | true =>
      have hi : (⟨n, hn⟩ : Fin 27) ∈ l := (bmask_testBit l ⟨n, hn⟩).mp hb
      have hs : (⟨n, hn⟩ : Fin 27) ∈ s := hc' _ hi
      have hm : (maskOf s).testBit n = true := (maskOf_testBit s ⟨n, hn⟩).mpr hs
      simp [hm]
  · have hlt : bmask l < 2 ^ n :=
      lt_of_lt_of_le (bmask_lt l) (Nat.pow_le_pow_right (by decide) (by omega : 27 ≤ n))
    have hb : (bmask l).testBit n = false := Nat.testBit_lt_two_pow hlt
    simp [hb]

/-! ## Consequences of the two kernel checks -/

lemma chk_of_card_four (J : Finset (Fin 27)) (hJ : J.card = 4) : chk J = true := by
  have h := go_spec chk 27 0 4 (∅ : Finset (Fin 27)) check4 (by decide) J hJ
    (by simp) (by simp)
  simpa using h

lemma notDom_of_card_five {t : Finset V} (ht : t.card = 5) : notDomB t = true := by
  have h := go_spec notDomB 18 0 5 (∅ : Finset V) check5 (by decide) t ht
    (by simp) (by simp)
  simpa using h

/-- No 5-element set of vertices dominates `G`. -/
lemma not_dominates_of_card_five {t : Finset V} (ht : t.card = 5) : ¬ Dominates G t := by
  have h : notDomB t = true := notDom_of_card_five ht
  have hdom : dominatesB t = false := by
    simp only [notDomB] at h
    simpa using h
  have hP : ¬ ∀ v : V, v ∈ t ∨ ∃ u ∈ t, (nb v).testBit u := of_decide_eq_false hdom
  intro hD
  apply hP
  intro v
  rcases hD v with hv | ⟨u, hu, hadj⟩
  · exact Or.inl hv
  · exact Or.inr ⟨u, hu, (nb_spec v u).mp hadj⟩

/-! ## Certificate extraction -/

lemma cert_ok_spec {c : Cert} (h : certOk c = true) :
    c.D.card = 6 ∧
    (∀ v : V, v ∈ c.D ∨ ∃ u ∈ c.D, G.Adj v u) ∧
    (∀ p ∈ c.bundles, p.1 ∉ c.D ∧
      ∀ j : Fin 27, j ∈ p.2 ↔ ∃ u ∈ c.D, eOf j = s(p.1, u)) ∧
    (∀ x : V, x ∉ c.D → ∃ p ∈ c.bundles, p.1 = x) := by
  simp only [certOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨by simpa using h1, by simpa using h2, ?_, by simpa using h4⟩
  intro p hp
  have hp' := List.all_eq_true.mp h3 p hp
  simp only [Bool.and_eq_true] at hp'
  exact ⟨by simpa using hp'.1, by simpa using hp'.2⟩

/-- From `chk s` extract a certificate set that survives `s`, together with all
the data recorded for it. -/
lemma chk_spec {s : Finset (Fin 27)} (h : chk s = true) :
    ∃ c ∈ certs, c.D.card = 6 ∧
      (∀ p ∈ c.bundles, p.1 ∉ c.D ∧
        ∀ j : Fin 27, j ∈ p.2 ↔ ∃ u ∈ c.D, eOf j = s(p.1, u)) ∧
      (∀ x : V, x ∉ c.D → ∃ p ∈ c.bundles, p.1 = x) ∧
      (∀ p ∈ c.bundles, ∃ j ∈ p.2, j ∉ s) := by
  simp only [chk] at h
  obtain ⟨c, hc, hcb⟩ := List.any_eq_true.mp h
  have hok := List.all_eq_true.mp certs_ok c hc
  obtain ⟨hcard, _hdom, hb, hcov⟩ := cert_ok_spec hok
  refine ⟨c, hc, hcard, hb, hcov, ?_⟩
  intro p hp
  have hp' := List.all_eq_true.mp hcb p hp
  have hpne : bmask p.2 &&& maskOf s ≠ bmask p.2 := bne_iff_ne.mp hp'
  exact exists_not_mem_of_mask_ne hpne

/-! ## Domination transfer -/

/-- If `I` is the index set of the edge set `F` and `I` has at most four
elements, then some 6-set of vertices dominates `G − F`. -/
lemma exists_dominating_six (F : Finset (Sym2 V)) (I : Finset (Fin 27))
    (hI : ∀ j : Fin 27, j ∈ I ↔ eOf j ∈ F) (hIcard : I.card ≤ 4) :
    ∃ D : Finset V, D.card = 6 ∧ Dominates (G.deleteEdges (F : Set (Sym2 V))) D := by
  obtain ⟨J, hIJ, hJcard⟩ :=
    Finset.exists_superset_card_eq hIcard (by decide : 4 ≤ Fintype.card (Fin 27))
  have hchk : chk J = true := chk_of_card_four J hJcard
  obtain ⟨c, _hc, hD6, hb, hcov, hsurv⟩ := chk_spec hchk
  refine ⟨c.D, hD6, ?_⟩
  intro x
  by_cases hx : x ∈ c.D
  · exact Or.inl hx
  · right
    obtain ⟨p, hp, hpx⟩ := hcov x hx
    obtain ⟨j, hj, hjs⟩ := hsurv p hp
    obtain ⟨_hpxnot, hspec⟩ := hb p hp
    rw [hpx] at hspec
    obtain ⟨u, hu, huje⟩ := (hspec j).mp hj
    refine ⟨u, hu, ?_⟩
    rw [SimpleGraph.deleteEdges_adj]
    constructor
    · rw [← SimpleGraph.mem_edgeSet, ← huje]
      exact eOf_mem j
    · intro hmemF
      have hjI : j ∈ I := (hI j).mpr (by rwa [← huje] at hmemF)
      exact hjs (hIJ hjI)

/-- Deleting edges cannot decrease the domination number. -/
lemma dominationNumber_le_of_le {H K : SimpleGraph V} (h : K ≤ H) :
    dominationNumber H ≤ dominationNumber K := by
  have hne : {m : ℕ | ∃ D : Finset V, D.card = m ∧ Dominates K D}.Nonempty :=
    ⟨_, Finset.univ, rfl, fun v => Or.inl (Finset.mem_univ v)⟩
  obtain ⟨D, hDcard, hDdom⟩ := Nat.sInf_mem hne
  apply Nat.sInf_le
  refine ⟨D, hDcard, ?_⟩
  intro v
  rcases hDdom v with hv | ⟨u, hu, hadj⟩
  · exact Or.inl hv
  · exact Or.inr ⟨u, hu, h hadj⟩

/-- Enlarging a dominating set preserves domination. -/
lemma dominates_mono {D t : Finset V} (h : D ⊆ t) (hD : Dominates G D) :
    Dominates G t := by
  intro v
  rcases hD v with hv | ⟨u, hu, hadj⟩
  · exact Or.inl (h hv)
  · exact Or.inr ⟨u, h hu, hadj⟩

/-! ## The graph is the edgeless graph after deleting everything -/

lemma dominationNumber_bot : dominationNumber (⊥ : SimpleGraph V) = 18 := by
  have hne : {m : ℕ | ∃ D : Finset V, D.card = m ∧ Dominates (⊥ : SimpleGraph V) D}.Nonempty :=
    ⟨_, Finset.univ, rfl, fun v => Or.inl (Finset.mem_univ v)⟩
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨Finset.univ, rfl, fun v => Or.inl (Finset.mem_univ v)⟩
  · obtain ⟨D, hDcard, hDdom⟩ := Nat.sInf_mem hne
    have hD : D = Finset.univ := by
      ext v
      simp only [Finset.mem_univ, iff_true]
      rcases hDdom v with hv | ⟨u, _hu, hadj⟩
      · exact hv
      · exact absurd hadj (by simpa using (bot_adj v u).mp)
    rw [hD] at hDcard
    change 18 ≤ sInf {m : ℕ | ∃ D : Finset V, D.card = m ∧ Dominates (⊥ : SimpleGraph V) D}
    rw [← hDcard, Finset.card_univ]
    simp [V]

/-- Some edge set strictly increases the domination number: deleting all edges
leaves the edgeless graph, whose domination number is `18 > 6`. -/
lemma exists_edge_set_increases (hγ : dominationNumber G = 6) :
    ∃ F : Finset (Sym2 V), (∀ e ∈ F, e ∈ G.edgeSet) ∧
      dominationNumber (G.deleteEdges (F : Set (Sym2 V))) > dominationNumber G := by
  refine ⟨G.edgeFinset, ?_, ?_⟩
  · intro e he
    rwa [SimpleGraph.mem_edgeFinset] at he
  · have hbot : G.deleteEdges ((G.edgeFinset : Finset (Sym2 V)) : Set (Sym2 V)) = ⊥ := by
      rw [SimpleGraph.deleteEdges_eq_bot]
      intro e he
      simpa using he
    rw [hbot, dominationNumber_bot, hγ]
    omega

/-! ## Structural facts: degree and bipartition -/

lemma ncard_neighborSet_three : ∀ v : V, (G.neighborSet v).ncard = 3 := by
  intro v
  rw [← SimpleGraph.coe_neighborFinset (G := G) v, Set.ncard_coe_finset,
    SimpleGraph.neighborFinset_eq_filter]
  fin_cases v <;> decide

lemma maxDegree_three : maxDegree G = 3 := by
  have h : ∀ v : V, (G.neighborSet v).ncard = 3 := ncard_neighborSet_three
  simp only [maxDegree, h]
  exact Finset.sup_const Finset.univ_nonempty 3

/-- A 2-colouring of `G` (the bipartition `X` / `Y` of the paper). -/
def bip : V → Fin 2 :=
  fun v => if v.val ∈ [0, 1, 4, 5, 7, 9, 13, 15, 17] then 0 else 1

lemma bip_ok : ∀ v w : V, G.Adj v w → bip v ≠ bip w := by
  decide

end DsBatch.P09
