import DsBatch.P15.Statement

/-! Proofs for project P15. Target stubs start as `:= by sorry` and are
    replaced by proofs; this file is not frozen. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open Finset

namespace DsBatch.P15

/-! ## General degree bounds for induced weights

Lemma 3.1 of the paper: for a vertex of degree `d`, the induced weight lies
between `1 + … + d = d(d+1)/2` and `(m-d+1) + … + m = d(2m-d+1)/2`. -/

/-- The sum of the `d` smallest positive integers is at most the sum of any
`d` positive distinct integers. -/
lemma range_sum_le_finset_sum (t : Finset ℕ) (hpos : ∀ x ∈ t, 0 < x) :
    (∑ i ∈ Finset.range t.card, (i + 1)) ≤ ∑ x ∈ t, x := by
  classical
  rcases Nat.eq_zero_or_pos t.card with h0 | hposd
  · have ht : t = ∅ := Finset.card_eq_zero.mp h0
    simp [ht]
  · obtain ⟨d, hd⟩ : ∃ d, t.card = d + 1 := ⟨t.card - 1, by omega⟩
    let e := t.orderEmbOfFin (k := d + 1) hd
    have hmem : ∀ i : Fin (d+1), e i ∈ t := fun i => Finset.orderEmbOfFin_mem t hd i
    have hsum : ∑ i : Fin (d+1), e i = ∑ x ∈ t, x := by
      conv_rhs => rw [← Finset.map_orderEmbOfFin_univ t hd]
      rw [Finset.sum_map]
      rfl
    have key : ∀ i : Fin (d+1), (i : ℕ) + 1 ≤ e i := by
      intro i
      induction i using Fin.induction with
      | zero => exact hpos _ (hmem 0)
      | succ j ih =>
          have hmono : e j.castSucc < e j.succ := e.strictMono (Fin.castSucc_lt_succ)
          have h2 : (e j.castSucc : ℕ) + 1 ≤ e j.succ := hmono
          have hj : ((j.castSucc : Fin (d+1)) : ℕ) = (j : ℕ) := rfl
          rw [Fin.val_succ]
          omega
    have hterm : ∑ i : Fin (d+1), ((i : ℕ) + 1) ≤ ∑ i : Fin (d+1), e i :=
      Finset.sum_le_sum (fun i _ => key i)
    have hrange : ∑ i : Fin (d+1), ((i : ℕ) + 1) = ∑ i ∈ Finset.range (d+1), (i + 1) :=
      Fin.sum_univ_eq_sum_range (fun i => i + 1) (d+1)
    rw [hd]
    calc ∑ i ∈ Finset.range (d + 1), (i + 1) = ∑ i : Fin (d+1), ((i:ℕ) + 1) := hrange.symm
      _ ≤ ∑ i : Fin (d+1), e i := hterm
      _ = ∑ x ∈ t, x := hsum

/-- The sum of any `d` distinct integers bounded by `m` is at most
`m + (m-1) + … + (m-d+1)`. -/
lemma finset_sum_le_range_sum_aux (n : ℕ) : ∀ (t : Finset ℕ), t.card = n → ∀ m,
    (∀ x ∈ t, x ≤ m) → (∑ x ∈ t, x) ≤ ∑ i ∈ Finset.range t.card, (m - i) := by
  induction n with
  | zero =>
      intro t ht m hle
      have ht0 : t = ∅ := Finset.card_eq_zero.mp ht
      simp [ht0]
  | succ n ih =>
      intro t ht m hle
      have hne : t.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        rw [h, Finset.card_empty] at ht
        omega
      set M := t.max' hne with hM
      have hmem : M ∈ t := Finset.max'_mem t hne
      have hMle : M ≤ m := hle M hmem
      have hle' : ∀ x ∈ t.erase M, x ≤ m - 1 := by
        intro x hx
        have hx' : x ∈ t := Finset.mem_of_mem_erase hx
        have hne' : x ≠ M := Finset.ne_of_mem_erase hx
        have hleM : x ≤ M := Finset.le_max' t x hx'
        omega
      have hcard : (t.erase M).card = n := by
        rw [Finset.card_erase_of_mem hmem, ht]
        omega
      have ih' := ih (t.erase M) hcard (m - 1) hle'
      have hsplit : (∑ x ∈ t, x) = M + ∑ x ∈ t.erase M, x := by
        rw [← Finset.sum_erase_add t (fun x => x) hmem]
        omega
      have hrange : (∑ i ∈ Finset.range t.card, (m - i))
          = m + ∑ i ∈ Finset.range (t.card - 1), ((m - 1) - i) := by
        rw [ht]
        rw [Finset.sum_range_succ' (fun i => m - i)]
        have hsub : n + 1 - 1 = n := by omega
        rw [hsub]
        simp only [Nat.sub_zero]
        have hsum_eq : (∑ k ∈ Finset.range n, (m - (k + 1)))
            = ∑ i ∈ Finset.range n, ((m - 1) - i) := by
          apply Finset.sum_congr rfl
          intro i hi
          omega
        rw [hsum_eq]
        omega
      rw [hsplit, hrange]
      rw [hcard] at ih'
      have hsub2 : t.card - 1 = n := by omega
      rw [hsub2]
      omega

lemma finset_sum_le_range_sum (t : Finset ℕ) (m : ℕ) (hle : ∀ x ∈ t, x ≤ m) :
    (∑ x ∈ t, x) ≤ ∑ i ∈ Finset.range t.card, (m - i) :=
  finset_sum_le_range_sum_aux t.card t rfl m hle

lemma range_sum_le_sum_of_inj {α : Type*} (s : Finset α) (g : α → ℕ)
    (hinj : ∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) (hpos : ∀ x ∈ s, 0 < g x) :
    (∑ i ∈ Finset.range s.card, (i + 1)) ≤ ∑ x ∈ s, g x := by
  classical
  have hcard : (s.image g).card = s.card :=
    Finset.card_image_of_injOn hinj
  have hsum : (∑ x ∈ s, g x) = ∑ y ∈ s.image g, y :=
    (Finset.sum_image (f := fun y => y) (g := g) hinj).symm
  rw [hsum]
  have hmain := range_sum_le_finset_sum (s.image g) ?_
  · rwa [hcard] at hmain
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact hpos x hx

lemma sum_le_range_sum_of_le {α : Type*} (s : Finset α) (g : α → ℕ) (m : ℕ)
    (hinj : ∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) (hle : ∀ x ∈ s, g x ≤ m) :
    (∑ x ∈ s, g x) ≤ ∑ i ∈ Finset.range s.card, (m - i) := by
  classical
  have hcard : (s.image g).card = s.card :=
    Finset.card_image_of_injOn hinj
  have hsum : (∑ x ∈ s, g x) = ∑ y ∈ s.image g, y :=
    (Finset.sum_image (f := fun y => y) (g := g) hinj).symm
  rw [hsum]
  have hmain := finset_sum_le_range_sum (s.image g) m ?_
  · rwa [hcard] at hmain
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact hle x hx

/-- Lower bound of Lemma 3.1: `L_m(d) ≤ f⁺(v)` where `d = d(v)`. -/
lemma inducedWeight_lower {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : Labeling G) (v : V) :
    (∑ i ∈ Finset.range (G.degree v), (i + 1)) ≤ inducedWeight G L v := by
  classical
  let s := G.incidenceFinset v
  let g : {e // e ∈ s} → ℕ := fun e =>
    edgeLabel G L ⟨e.1, G.mem_edgeFinset.mp (G.incidenceFinset_subset v e.2)⟩
  have hg_eq : inducedWeight G L v = ∑ e ∈ s.attach, g e := rfl
  rw [hg_eq]
  have hcard : s.attach.card = G.degree v := by
    rw [Finset.card_attach]
    exact SimpleGraph.card_incidenceFinset_eq_degree G v
  rw [← hcard]
  apply range_sum_le_sum_of_inj
  · intro e _ e' _ h
    apply Subtype.ext
    have hv : (L ⟨e.1, G.mem_edgeFinset.mp (G.incidenceFinset_subset v e.2)⟩).val
        = (L ⟨e'.1, G.mem_edgeFinset.mp (G.incidenceFinset_subset v e'.2)⟩).val := by
      have := h
      simp only [g, edgeLabel] at this
      omega
    have heq : L ⟨e.1, G.mem_edgeFinset.mp (G.incidenceFinset_subset v e.2)⟩
        = L ⟨e'.1, G.mem_edgeFinset.mp (G.incidenceFinset_subset v e'.2)⟩ := Fin.ext hv
    have := L.injective heq
    simpa using congrArg Subtype.val this
  · intro e _
    simp only [g, edgeLabel]
    have := (L ⟨e.1, G.mem_edgeFinset.mp (G.incidenceFinset_subset v e.2)⟩).isLt
    omega

/-- Upper bound of Lemma 3.1: `f⁺(v) ≤ U_m(d)` where `d = d(v)`. -/
lemma inducedWeight_upper {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : Labeling G) (v : V) :
    inducedWeight G L v ≤
      ∑ i ∈ Finset.range (G.degree v), (Fintype.card G.edgeSet - i) := by
  classical
  let s := G.incidenceFinset v
  let g : {e // e ∈ s} → ℕ := fun e =>
    edgeLabel G L ⟨e.1, G.mem_edgeFinset.mp (G.incidenceFinset_subset v e.2)⟩
  have hg_eq : inducedWeight G L v = ∑ e ∈ s.attach, g e := rfl
  rw [hg_eq]
  have hcard : s.attach.card = G.degree v := by
    rw [Finset.card_attach]
    exact SimpleGraph.card_incidenceFinset_eq_degree G v
  rw [← hcard]
  apply sum_le_range_sum_of_le _ _ (Fintype.card G.edgeSet)
  · intro e _ e' _ h
    apply Subtype.ext
    have hv : (L ⟨e.1, G.mem_edgeFinset.mp (G.incidenceFinset_subset v e.2)⟩).val
        = (L ⟨e'.1, G.mem_edgeFinset.mp (G.incidenceFinset_subset v e'.2)⟩).val := by
      have := h
      simp only [g, edgeLabel] at this
      omega
    have heq : L ⟨e.1, G.mem_edgeFinset.mp (G.incidenceFinset_subset v e.2)⟩
        = L ⟨e'.1, G.mem_edgeFinset.mp (G.incidenceFinset_subset v e'.2)⟩ := Fin.ext hv
    have := L.injective heq
    simpa using congrArg Subtype.val this
  · intro e _
    simp only [g, edgeLabel]
    have := (L ⟨e.1, G.mem_edgeFinset.mp (G.incidenceFinset_subset v e.2)⟩).isLt
    omega

/-! ## The concrete caterpillar `T₃` -/

lemma cardV3 : Fintype.card V3 = 43 := by decide

lemma cardE3 : Fintype.card T3.edgeSet = 42 := by decide

lemma degA : T3.degree vA = 9 := by decide

lemma degB : T3.degree vB = 9 := by decide

lemma degC : T3.degree vC = 26 := by decide

lemma leafCount_T3 : leafCount T3 = 40 := by decide

/-- Every leaf of `T₃` has degree one. -/
lemma degree_leaf (i : Fin 3) (j : Fin (shape3 i)) :
    T3.degree (Sum.inr ⟨i, j⟩) = 1 := by
  fin_cases i <;> fin_cases j <;> decide

/-- The unique edge incident with the leaf `(i,j)` of `T₃`. -/
lemma incidence_leaf (i : Fin 3) (j : Fin (shape3 i)) :
    T3.incidenceFinset (Sum.inr ⟨i, j⟩) = {s(Sum.inl i, Sum.inr ⟨i, j⟩)} := by
  fin_cases i <;> fin_cases j <;> decide

/-- The pendant edge carrying the leaf `(i,j)`. -/
def pendantEdge (i : Fin 3) (j : Fin (shape3 i)) : T3.edgeSet :=
  ⟨s(Sum.inl i, Sum.inr ⟨i, j⟩),
    T3.mem_edgeFinset.mp (T3.incidenceFinset_subset (Sum.inr ⟨i, j⟩) (by
      rw [incidence_leaf]
      exact Finset.mem_singleton_self _))⟩

/-- The weight of a leaf of `T₃` is the label of its pendant edge. -/
lemma weight_leaf (L : Labeling T3) (i : Fin 3) (j : Fin (shape3 i)) :
    inducedWeight T3 L (Sum.inr ⟨i, j⟩) = edgeLabel T3 L (pendantEdge i j) := by
  classical
  have hmem : s(Sum.inl i, Sum.inr ⟨i, j⟩) ∈ T3.incidenceFinset (Sum.inr ⟨i, j⟩) := by
    rw [incidence_leaf]
    exact Finset.mem_singleton_self _
  have hcard : #(T3.incidenceFinset (Sum.inr ⟨i, j⟩)) ≤ 1 := by
    rw [SimpleGraph.card_incidenceFinset_eq_degree (G := T3) (v := Sum.inr ⟨i, j⟩),
      degree_leaf i j]
  unfold inducedWeight
  refine Finset.sum_eq_single
    (⟨s(Sum.inl i, Sum.inr ⟨i, j⟩), hmem⟩ :
      {x // x ∈ T3.incidenceFinset (Sum.inr ⟨i, j⟩)}) ?_ ?_
  · intro b hb hne
    exfalso
    apply hne
    exact Subtype.ext (Finset.card_le_one.mp hcard b.1 b.2 _ hmem)
  · intro hcon
    exact absurd (Finset.mem_attach _ _) hcon

/-- Every leaf weight of `T₃` is at most `|E(T₃)| = 42`. -/
lemma leaf_weight_le (L : Labeling T3) (i : Fin 3) (j : Fin (shape3 i)) :
    inducedWeight T3 L (Sum.inr ⟨i, j⟩) ≤ 42 := by
  have h := inducedWeight_upper T3 L (Sum.inr ⟨i, j⟩)
  rw [degree_leaf i j, cardE3] at h
  have h42 : (∑ k ∈ Finset.range 1, (42 - k)) = 42 := by decide
  rwa [h42] at h

/-- `I₄₂(9) = [45, 342]`: bounds on the weight of `a`. -/
lemma weight_bounds_A (L : Labeling T3) :
    45 ≤ inducedWeight T3 L vA ∧ inducedWeight T3 L vA ≤ 342 := by
  constructor
  · have h := inducedWeight_lower T3 L vA
    rw [degA] at h
    have h45 : (∑ i ∈ Finset.range 9, (i + 1)) = 45 := by decide
    rwa [h45] at h
  · have h := inducedWeight_upper T3 L vA
    rw [degA, cardE3] at h
    have h342 : (∑ i ∈ Finset.range 9, (42 - i)) = 342 := by decide
    rwa [h342] at h

/-- `I₄₂(9) = [45, 342]`: bounds on the weight of `b`. -/
lemma weight_bounds_B (L : Labeling T3) :
    45 ≤ inducedWeight T3 L vB ∧ inducedWeight T3 L vB ≤ 342 := by
  constructor
  · have h := inducedWeight_lower T3 L vB
    rw [degB] at h
    have h45 : (∑ i ∈ Finset.range 9, (i + 1)) = 45 := by decide
    rwa [h45] at h
  · have h := inducedWeight_upper T3 L vB
    rw [degB, cardE3] at h
    have h342 : (∑ i ∈ Finset.range 9, (42 - i)) = 342 := by decide
    rwa [h342] at h

/-- `I₄₂(26) = [351, 767]`: bounds on the weight of `c`. -/
lemma weight_bounds_C (L : Labeling T3) :
    351 ≤ inducedWeight T3 L vC ∧ inducedWeight T3 L vC ≤ 767 := by
  constructor
  · have h := inducedWeight_lower T3 L vC
    rw [degC] at h
    have h351 : (∑ i ∈ Finset.range 26, (i + 1)) = 351 := by decide
    rwa [h351] at h
  · have h := inducedWeight_upper T3 L vC
    rw [degC, cardE3] at h
    have h767 : (∑ i ∈ Finset.range 26, (42 - i)) = 767 := by decide
    rwa [h767] at h

/-- Distinct leaves of `T₃` receive distinct weights. -/
lemma weight_leaf_ne (L : Labeling T3) {i i' : Fin 3} {j : Fin (shape3 i)}
    {j' : Fin (shape3 i')}
    (hne : (⟨i, j⟩ : Σ i, Fin (shape3 i)) ≠ ⟨i', j'⟩) :
    inducedWeight T3 L (Sum.inr ⟨i, j⟩) ≠ inducedWeight T3 L (Sum.inr ⟨i', j'⟩) := by
  rw [weight_leaf, weight_leaf]
  intro h
  have hval : (L (pendantEdge i j)).val = (L (pendantEdge i' j')).val := by
    simp only [edgeLabel] at h
    omega
  have heq : L (pendantEdge i j) = L (pendantEdge i' j') := Fin.ext hval
  have hedge : s(Sum.inl i, Sum.inr (⟨i, j⟩ : Σ k, Fin (shape3 k)))
      = s(Sum.inl i', Sum.inr (⟨i', j'⟩ : Σ k, Fin (shape3 k))) :=
    congrArg Subtype.val (L.injective heq)
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hj : (⟨i, j⟩ : Σ i, Fin (shape3 i)) = ⟨i', j'⟩ := by injection h2
    exact hne hj
  · cases h1

/-- Under any local antimagic labelling of `T₃`, the induced weights of all
43 vertices are pairwise distinct.  This formalizes the separation argument
of Theorem 4.1: `I₄₂(9) = [45,342]` and `I₄₂(26) = [351,767]` lie above
`|E(T₃)| = 42` and are disjoint, `a` and `b` are adjacent, and leaves have
pairwise distinct weights at most 42. -/
lemma weights_injective (L : Labeling T3) (hL : IsLocalAntimagic T3 L) :
    Function.Injective (inducedWeight T3 L) := by
  intro u v huv
  obtain ⟨hA1, hA2⟩ := weight_bounds_A L
  obtain ⟨hB1, hB2⟩ := weight_bounds_B L
  obtain ⟨hC1, hC2⟩ := weight_bounds_C L
  rcases u with i | ⟨i, j⟩
  · rcases v with i' | ⟨i', j'⟩
    · fin_cases i
      · fin_cases i'
        · rfl
        · exact absurd huv (hL vA vB (by decide))
        · have huv' : inducedWeight T3 L vA = inducedWeight T3 L vC := huv
          omega
      · fin_cases i'
        · exact absurd huv (hL vB vA (by decide))
        · rfl
        · have huv' : inducedWeight T3 L vB = inducedWeight T3 L vC := huv
          omega
      · fin_cases i'
        · have huv' : inducedWeight T3 L vC = inducedWeight T3 L vA := huv
          omega
        · have huv' : inducedWeight T3 L vC = inducedWeight T3 L vB := huv
          omega
        · rfl
    · fin_cases i
      · have huv' : inducedWeight T3 L vA = inducedWeight T3 L (Sum.inr ⟨i', j'⟩) := huv
        have h42 := leaf_weight_le L i' j'
        omega
      · have huv' : inducedWeight T3 L vB = inducedWeight T3 L (Sum.inr ⟨i', j'⟩) := huv
        have h42 := leaf_weight_le L i' j'
        omega
      · have huv' : inducedWeight T3 L vC = inducedWeight T3 L (Sum.inr ⟨i', j'⟩) := huv
        have h42 := leaf_weight_le L i' j'
        omega
  · rcases v with i' | ⟨i', j'⟩
    · fin_cases i'
      · have huv' : inducedWeight T3 L (Sum.inr ⟨i, j⟩) = inducedWeight T3 L vA := huv
        have h42 := leaf_weight_le L i j
        omega
      · have huv' : inducedWeight T3 L (Sum.inr ⟨i, j⟩) = inducedWeight T3 L vB := huv
        have h42 := leaf_weight_le L i j
        omega
      · have huv' : inducedWeight T3 L (Sum.inr ⟨i, j⟩) = inducedWeight T3 L vC := huv
        have h42 := leaf_weight_le L i j
        omega
    · by_contra h
      exact weight_leaf_ne L (fun hs => h (by rw [hs])) huv

lemma weightImage_card (L : Labeling T3) (hL : IsLocalAntimagic T3 L) :
    (weightImage T3 L).card = 43 := by
  unfold weightImage
  rw [Finset.card_image_of_injective _ (weights_injective L hL)]
  rw [Finset.card_univ, cardV3]

/-! ## `T₃` is a caterpillar -/

lemma t3_reachable_A : ∀ w : V3, T3.Reachable vA w := by
  intro w
  rcases w with i | ⟨i, j⟩
  · fin_cases i
    · exact SimpleGraph.Reachable.refl vA
    · exact SimpleGraph.Adj.reachable (by decide : T3.Adj vA vB)
    · exact (SimpleGraph.Adj.reachable (by decide : T3.Adj vA vB)).trans
        (SimpleGraph.Adj.reachable (by decide : T3.Adj vB vC))
  · have hstep : T3.Adj (Sum.inl i) (Sum.inr ⟨i, j⟩) := rfl
    have hbase : T3.Reachable vA (Sum.inl i) := by
      fin_cases i
      · exact SimpleGraph.Reachable.refl vA
      · exact SimpleGraph.Adj.reachable (by decide : T3.Adj vA vB)
      · exact (SimpleGraph.Adj.reachable (by decide : T3.Adj vA vB)).trans
          (SimpleGraph.Adj.reachable (by decide : T3.Adj vB vC))
    exact hbase.trans (SimpleGraph.Adj.reachable hstep)

lemma t3_connected : T3.Connected :=
  (SimpleGraph.connected_iff_exists_forall_reachable T3).mpr ⟨vA, t3_reachable_A⟩

lemma t3_isTree : T3.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · exact t3_connected
  · have h1 : Nat.card T3.edgeSet = 42 := by
      rw [Nat.card_eq_fintype_card, cardE3]
    have h2 : Nat.card V3 = 43 := by
      rw [Nat.card_eq_fintype_card, cardV3]
    omega

lemma t3_isCaterpillar : IsCaterpillar T3 := by
  refine ⟨t3_isTree, 3, fun i => Sum.inl i, ?_, ?_, ?_, ?_⟩
  · intro i j h
    exact Sum.inl_injective h
  · intro i
    fin_cases i <;> decide
  · intro x hx
    rcases x with i | ⟨i, j⟩
    · exact ⟨i, rfl⟩
    · exact absurd (degree_leaf i j) hx
  · intro i j
    rfl

/-! ## The local antimagic chromatic number of `T₃` -/

lemma chiLa_T3 : chiLa T3 = 43 := by
  unfold chiLa
  have hmem : 43 ∈ {k : ℕ | ∃ L : Labeling T3, IsLocalAntimagic T3 L ∧
      (weightImage T3 L).card = k} :=
    ⟨t3Labeling, t3Labeling_isLocalAntimagic, rfl⟩
  have hnonempty : {k : ℕ | ∃ L : Labeling T3, IsLocalAntimagic T3 L ∧
      (weightImage T3 L).card = k}.Nonempty := ⟨43, hmem⟩
  have hle : sInf {k : ℕ | ∃ L : Labeling T3, IsLocalAntimagic T3 L ∧
      (weightImage T3 L).card = k} ≤ 43 := Nat.sInf_le hmem
  obtain ⟨L, hL, hcard⟩ := Nat.sInf_mem hnonempty
  have h43 : (weightImage T3 L).card = 43 := weightImage_card L hL
  omega

/-! ## Targets -/

theorem t3_caterpillar : t3_caterpillar_statement := by
  unfold t3_caterpillar_statement
  exact ⟨t3_isCaterpillar, cardV3, cardE3, leafCount_T3, degA, degB, degC⟩

theorem t3_weight_separation : t3_weight_separation_statement := by
  unfold t3_weight_separation_statement
  intro L hL
  exact weightImage_card L hL

theorem t3_chiLa : t3_chiLa_statement := by
  unfold t3_chiLa_statement
  exact ⟨chiLa_T3, by rw [chiLa_T3, leafCount_T3]⟩

theorem leaf_conjecture_false : leaf_conjecture_false_statement := by
  unfold leaf_conjecture_false_statement LeafConjecture
  intro h
  have hle : chiLa T3 ≤ leafCount T3 + 2 := h V3 T3 t3_isTree (by decide)
  rw [chiLa_T3, leafCount_T3] at hle
  omega

end DsBatch.P15
