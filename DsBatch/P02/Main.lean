import DsBatch.P02.Statement

namespace DsBatch.P02

open Finset

/-! ### Elementary cardinality lemmas -/

lemma card_sdiff_singleton_ge (s : Finset ℕ) (x : ℕ) : s.card - 1 ≤ (s \ {x}).card := by
  rw [Finset.card_sdiff]
  have h : (({x} : Finset ℕ) ∩ s).card ≤ 1 := by
    calc (({x} : Finset ℕ) ∩ s).card ≤ ({x} : Finset ℕ).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = 1 := by simp
  omega

lemma card_sdiff_pair_ge (s : Finset ℕ) (x y : ℕ) (h : ¬ (x ∈ s ∧ y ∈ s)) :
    s.card - 1 ≤ (s \ {x, y}).card := by
  rw [Finset.card_sdiff]
  have h1 : (({x, y} : Finset ℕ) ∩ s).card ≤ 1 := by
    by_contra hle
    have h2 : 2 ≤ (({x, y} : Finset ℕ) ∩ s).card := by omega
    by_cases hxy : x = y
    · subst hxy
      have hc : (({x, x} : Finset ℕ) ∩ s).card ≤ 1 := by
        calc (({x, x} : Finset ℕ) ∩ s).card ≤ ({x, x} : Finset ℕ).card :=
              Finset.card_le_card Finset.inter_subset_left
          _ = 1 := by simp
      omega
    · have hcard : ({x, y} : Finset ℕ).card = 2 := by simp [hxy]
      have heq : ({x, y} : Finset ℕ) ∩ s = {x, y} :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
      have hx : x ∈ s := by
        have hx' : x ∈ ({x, y} : Finset ℕ) ∩ s := by rw [heq]; simp
        exact Finset.mem_of_mem_inter_right hx'
      have hy : y ∈ s := by
        have hy' : y ∈ ({x, y} : Finset ℕ) ∩ s := by rw [heq]; simp
        exact Finset.mem_of_mem_inter_right hy'
      exact h ⟨hx, hy⟩
  omega

lemma mul_le_two_of_add_le_three {a b : ℕ} (h : a + b ≤ 3) : a * b ≤ 2 := by
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;> omega

/-- Three lists of sizes at least 1, 2, 3 admit pairwise distinct representatives. -/
lemma exists_pairwise_distinct {A B C : Finset ℕ} (hA : 1 ≤ A.card) (hB : 2 ≤ B.card)
    (hC : 3 ≤ C.card) :
    ∃ x ∈ A, ∃ y ∈ B, ∃ z ∈ C, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
  have hBpos : 0 < (B \ {x}).card := by
    have h := card_sdiff_singleton_ge B x
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hBpos
  have hyB : y ∈ B := (Finset.mem_sdiff.mp hy).1
  have hyx : y ≠ x := by simpa using (Finset.mem_sdiff.mp hy).2
  have hCpos : 0 < ((C \ {x}) \ {y}).card := by
    have h1 := card_sdiff_singleton_ge C x
    have h2 := card_sdiff_singleton_ge (C \ {x}) y
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hCpos
  have hzCx : z ∈ C \ {x} := (Finset.mem_sdiff.mp hz).1
  have hzy : z ≠ y := by simpa using (Finset.mem_sdiff.mp hz).2
  have hzC : z ∈ C := (Finset.mem_sdiff.mp hzCx).1
  have hzx : z ≠ x := by simpa using (Finset.mem_sdiff.mp hzCx).2
  exact ⟨x, hx, y, hyB, z, hzC, hyx.symm, hzx.symm, hzy.symm⟩

/-! ### Structural facts about the graph and the explicit lists -/

lemma listOf_card (i : Fin 4) : (listOf i).card = 2 := by
  fin_cases i <;> decide

lemma L_two (v : V) : (L v).card = 2 := by
  cases v with
  | s1 => simp [L]
  | s2 => simp [L]
  | u i => exact listOf_card i
  | v i => exact listOf_card i
  | p i => exact listOf_card i

lemma adj_u_v (i : Fin 4) : G.Adj (V.u i) (V.v i) := by simp [G_adj, adjB]
lemma adj_u_p (i : Fin 4) : G.Adj (V.u i) (V.p i) := by simp [G_adj, adjB]
lemma adj_v_p (i : Fin 4) : G.Adj (V.v i) (V.p i) := by simp [G_adj, adjB]
lemma adj_s1_u (i : Fin 4) : G.Adj V.s1 (V.u i) := by simp [G_adj, adjB]
lemma adj_s1_v (i : Fin 4) : G.Adj V.s1 (V.v i) := by simp [G_adj, adjB]
lemma adj_s2_u (i : Fin 4) : G.Adj V.s2 (V.u i) := by simp [G_adj, adjB]
lemma adj_s2_v (i : Fin 4) : G.Adj V.s2 (V.v i) := by simp [G_adj, adjB]

/-- A triangle with a common list of size 2 contributes at most two coloured vertices. -/
lemma triangle_card_le_two (S : Finset V) (c : V → ℕ)
    (h : IsPartialListColoring G L S c) (i : Fin 4) : (S ∩ T i).card ≤ 2 := by
  by_contra hle
  have hge : 3 ≤ (S ∩ T i).card := by omega
  have hcardT : (T i).card = 3 := by simp [T]
  have heq : S ∩ T i = T i :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  have hu : V.u i ∈ S := by
    have h' : V.u i ∈ S ∩ T i := by rw [heq]; simp [T]
    exact Finset.mem_of_mem_inter_left h'
  have hv : V.v i ∈ S := by
    have h' : V.v i ∈ S ∩ T i := by rw [heq]; simp [T]
    exact Finset.mem_of_mem_inter_left h'
  have hp : V.p i ∈ S := by
    have h' : V.p i ∈ S ∩ T i := by rw [heq]; simp [T]
    exact Finset.mem_of_mem_inter_left h'
  have hmu : c (V.u i) ∈ L (V.u i) := h.1 _ hu
  have hmv : c (V.v i) ∈ L (V.v i) := h.1 _ hv
  have hmp : c (V.p i) ∈ L (V.p i) := h.1 _ hp
  have hLuv : L (V.u i) = L (V.v i) := rfl
  have hLvp : L (V.v i) = L (V.p i) := rfl
  have hd1 : c (V.u i) ≠ c (V.v i) := h.2 _ hu _ hv (adj_u_v i)
  have hd2 : c (V.u i) ≠ c (V.p i) := h.2 _ hu _ hp (adj_u_p i)
  have hd3 : c (V.v i) ≠ c (V.p i) := h.2 _ hv _ hp (adj_v_p i)
  have hset : ({c (V.u i), c (V.v i), c (V.p i)} : Finset ℕ) ⊆ L (V.u i) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hmu
    · rw [hLuv]; exact hmv
    · rw [hLuv, hLvp]; exact hmp
  have hc3 : ({c (V.u i), c (V.v i), c (V.p i)} : Finset ℕ).card = 3 := by
    simp [hd1, hd2, hd3]
  have h3 : 3 ≤ (L (V.u i)).card := by
    calc 3 = _ := hc3.symm
      _ ≤ _ := Finset.card_le_card hset
  have := L_two (V.u i)
  omega

/-- The four triangles contain exactly the non-terminal vertices. -/
lemma terminals_union_allTriangles : terminals ∪ allTriangles = (Finset.univ : Finset V) := by
  ext w
  cases w with
  | s1 => simp [terminals]
  | s2 => simp [terminals]
  | u i =>
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [T]⟩)
  | v i =>
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [T]⟩)
  | p i =>
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp [T]⟩)

lemma disjoint_terminals_allTriangles : Disjoint terminals allTriangles := by
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  simp only [terminals, Finset.mem_insert, Finset.mem_singleton] at hw1
  obtain ⟨i, -, hwi⟩ := Finset.mem_biUnion.mp hw2
  rcases hw1 with rfl | rfl <;> simp [T] at hwi

lemma partition_card (S : Finset V) :
    S.card = (S ∩ terminals).card + (S ∩ allTriangles).card := by
  have hdisj : Disjoint (S ∩ terminals) (S ∩ allTriangles) :=
    disjoint_terminals_allTriangles.mono Finset.inter_subset_right Finset.inter_subset_right
  have hEq : S = (S ∩ terminals) ∪ (S ∩ allTriangles) := by
    rw [← Finset.inter_union_distrib_left, terminals_union_allTriangles, Finset.inter_univ]
  conv_lhs => rw [hEq]
  exact Finset.card_union_of_disjoint hdisj

lemma inter_allTriangles_eq (S : Finset V) :
    S ∩ allTriangles = (Finset.univ : Finset (Fin 4)).biUnion (fun i => S ∩ T i) := by
  ext w
  simp only [allTriangles, Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hwS, i, hwi⟩
    exact ⟨i, hwS, hwi⟩
  · rintro ⟨i, hwS, hwi⟩
    exact ⟨hwS, i, hwi⟩

lemma card_allTriangles_le (S : Finset V) (h : ∀ i, (S ∩ T i).card ≤ 2) :
    (S ∩ allTriangles).card ≤ 8 := by
  rw [inter_allTriangles_eq S]
  calc ((Finset.univ : Finset (Fin 4)).biUnion (fun i => S ∩ T i)).card
      ≤ ∑ i : Fin 4, (S ∩ T i).card := Finset.card_biUnion_le
    _ ≤ ∑ i : Fin 4, 2 := Finset.sum_le_sum (fun i _ => h i)
    _ = 8 := by simp

/-- If both terminals are coloured and triangle `T i` carries their two colours as its list,
then at most one vertex of `T i` can be coloured. -/
lemma special_triangle_bound (S : Finset V) (c : V → ℕ)
    (h : IsPartialListColoring G L S c) (h1 : V.s1 ∈ S) (h2 : V.s2 ∈ S) (i : Fin 4)
    (hlist : L (V.u i) = {c V.s1, c V.s2}) : (S ∩ T i).card ≤ 1 := by
  have hu : V.u i ∉ S := by
    intro huS
    have hineq : c (V.u i) ∈ L (V.u i) := h.1 _ huS
    rw [hlist] at hineq
    have hne1 : c (V.u i) ≠ c V.s1 := h.2 _ huS _ h1 (adj_s1_u i).symm
    have hne2 : c (V.u i) ≠ c V.s2 := h.2 _ huS _ h2 (adj_s2_u i).symm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hineq
    rcases hineq with h' | h'
    · exact hne1 h'
    · exact hne2 h'
  have hv : V.v i ∉ S := by
    intro hvS
    have hineq : c (V.v i) ∈ L (V.v i) := h.1 _ hvS
    have hlist' : L (V.v i) = {c V.s1, c V.s2} := hlist
    rw [hlist'] at hineq
    have hne1 : c (V.v i) ≠ c V.s1 := h.2 _ hvS _ h1 (adj_s1_v i).symm
    have hne2 : c (V.v i) ≠ c V.s2 := h.2 _ hvS _ h2 (adj_s2_v i).symm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hineq
    rcases hineq with h' | h'
    · exact hne1 h'
    · exact hne2 h'
  calc (S ∩ T i).card ≤ ({V.p i} : Finset V).card := by
        apply Finset.card_le_card
        intro w hw
        obtain ⟨hwS, hwi⟩ := Finset.mem_inter.mp hw
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at hwi ⊢
        rcases hwi with rfl | rfl | rfl
        · exact absurd hwS hu
        · exact absurd hwS hv
        · simp
    _ = 1 := by simp

/-- The 2-list assignment `L` admits no partial proper colouring of more than nine vertices. -/
theorem nine_bound (S : Finset V) (c : V → ℕ) (h : IsPartialListColoring G L S c) :
    S.card ≤ 9 := by
  have htri : ∀ i : Fin 4, (S ∩ T i).card ≤ 2 := fun i => triangle_card_le_two S c h i
  have hcard := partition_card S
  by_cases hboth : V.s1 ∈ S ∧ V.s2 ∈ S
  · have hU : (S ∩ terminals).card = 2 := by
      have heq : S ∩ terminals = terminals := by
        ext w
        simp only [Finset.mem_inter, terminals, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨-, h'⟩; exact h'
        · rintro (rfl | rfl)
          · exact ⟨hboth.1, Or.inl rfl⟩
          · exact ⟨hboth.2, Or.inr rfl⟩
      rw [heq]; simp [terminals]
    have ha : c V.s1 = 0 ∨ c V.s1 = 1 := by
      have h' := h.1 _ hboth.1
      simpa [L] using h'
    have hb : c V.s2 = 2 ∨ c V.s2 = 3 := by
      have h' := h.1 _ hboth.2
      simpa [L] using h'
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · -- terminal colours 0 and 2: triangle `T 0` collapses to `{p 0}`
      have hspec : (S ∩ T 0).card ≤ 1 := by
        apply special_triangle_bound S c h hboth.1 hboth.2 0
        rw [ha, hb]; decide
      have hAl : (S ∩ allTriangles).card ≤ 7 := by
        rw [inter_allTriangles_eq S]
        calc ((Finset.univ : Finset (Fin 4)).biUnion (fun i => S ∩ T i)).card
            ≤ ∑ i : Fin 4, (S ∩ T i).card := Finset.card_biUnion_le
          _ ≤ ∑ i : Fin 4, (if i = (0 : Fin 4) then 1 else 2) := by
              apply Finset.sum_le_sum
              intro i _
              by_cases hi : i = (0 : Fin 4)
              · subst hi; simpa using hspec
              · simp [hi]; exact htri i
          _ = 7 := by decide
      omega
    · -- terminal colours 0 and 3: triangle `T 1`
      have hspec : (S ∩ T 1).card ≤ 1 := by
        apply special_triangle_bound S c h hboth.1 hboth.2 1
        rw [ha, hb]; decide
      have hAl : (S ∩ allTriangles).card ≤ 7 := by
        rw [inter_allTriangles_eq S]
        calc ((Finset.univ : Finset (Fin 4)).biUnion (fun i => S ∩ T i)).card
            ≤ ∑ i : Fin 4, (S ∩ T i).card := Finset.card_biUnion_le
          _ ≤ ∑ i : Fin 4, (if i = (1 : Fin 4) then 1 else 2) := by
              apply Finset.sum_le_sum
              intro i _
              by_cases hi : i = (1 : Fin 4)
              · subst hi; simpa using hspec
              · simp [hi]; exact htri i
          _ = 7 := by decide
      omega
    · -- terminal colours 1 and 2: triangle `T 2`
      have hspec : (S ∩ T 2).card ≤ 1 := by
        apply special_triangle_bound S c h hboth.1 hboth.2 2
        rw [ha, hb]; decide
      have hAl : (S ∩ allTriangles).card ≤ 7 := by
        rw [inter_allTriangles_eq S]
        calc ((Finset.univ : Finset (Fin 4)).biUnion (fun i => S ∩ T i)).card
            ≤ ∑ i : Fin 4, (S ∩ T i).card := Finset.card_biUnion_le
          _ ≤ ∑ i : Fin 4, (if i = (2 : Fin 4) then 1 else 2) := by
              apply Finset.sum_le_sum
              intro i _
              by_cases hi : i = (2 : Fin 4)
              · subst hi; simpa using hspec
              · simp [hi]; exact htri i
          _ = 7 := by decide
      omega
    · -- terminal colours 1 and 3: triangle `T 3`
      have hspec : (S ∩ T 3).card ≤ 1 := by
        apply special_triangle_bound S c h hboth.1 hboth.2 3
        rw [ha, hb]; decide
      have hAl : (S ∩ allTriangles).card ≤ 7 := by
        rw [inter_allTriangles_eq S]
        calc ((Finset.univ : Finset (Fin 4)).biUnion (fun i => S ∩ T i)).card
            ≤ ∑ i : Fin 4, (S ∩ T i).card := Finset.card_biUnion_le
          _ ≤ ∑ i : Fin 4, (if i = (3 : Fin 4) then 1 else 2) := by
              apply Finset.sum_le_sum
              intro i _
              by_cases hi : i = (3 : Fin 4)
              · subst hi; simpa using hspec
              · simp [hi]; exact htri i
          _ = 7 := by decide
      omega
  · have hU1 : (S ∩ terminals).card ≤ 1 := by
      by_cases h1 : V.s1 ∈ S
      · have h2 : V.s2 ∉ S := fun h2 => hboth ⟨h1, h2⟩
        have hsub : S ∩ terminals ⊆ {V.s1} := by
          intro w hw
          obtain ⟨hwS, hwt⟩ := Finset.mem_inter.mp hw
          simp only [terminals, Finset.mem_insert, Finset.mem_singleton] at hwt ⊢
          rcases hwt with rfl | rfl
          · simp
          · exact absurd hwS h2
        calc (S ∩ terminals).card ≤ ({V.s1} : Finset V).card := Finset.card_le_card hsub
          _ = 1 := by simp
      · have hsub : S ∩ terminals ⊆ {V.s2} := by
          intro w hw
          obtain ⟨hwS, hwt⟩ := Finset.mem_inter.mp hw
          simp only [terminals, Finset.mem_insert, Finset.mem_singleton] at hwt ⊢
          rcases hwt with rfl | rfl
          · exact absurd hwS h1
          · simp
        calc (S ∩ terminals).card ≤ ({V.s2} : Finset V).card := Finset.card_le_card hsub
          _ = 1 := by simp
    have hAl : (S ∩ allTriangles).card ≤ 8 := card_allTriangles_le S htri
    omega

lemma card_sdiff_pair_ge' (s : Finset ℕ) (x y : ℕ) : s.card - 2 ≤ (s \ {x, y}).card := by
  rw [Finset.card_sdiff]
  have h : (({x, y} : Finset ℕ) ∩ s).card ≤ 2 := by
    calc (({x, y} : Finset ℕ) ∩ s).card ≤ ({x, y} : Finset ℕ).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ ≤ 2 := by
          rcases eq_or_ne x y with h | h
          · subst h; simp
          · simp [h]
  omega

/-- `G` is 3-choosable: the paper's case analysis on `L(s_1) ∩ L(s_2)`. -/
theorem choosable_three : Choosable G 3 := by
  intro L' hL'
  by_cases hcase : (L' V.s1 ∩ L' V.s2).Nonempty
  · -- Case 1: the two terminal lists intersect.
    obtain ⟨x, hx⟩ := hcase
    have hx1 : x ∈ L' V.s1 := Finset.mem_of_mem_inter_left hx
    have hx2 : x ∈ L' V.s2 := Finset.mem_of_mem_inter_right hx
    have htri : ∀ i : Fin 4, ∃ a b e : ℕ,
        a ∈ L' (V.u i) \ {x} ∧ b ∈ L' (V.v i) \ {x} ∧ e ∈ L' (V.p i) ∧
        a ≠ b ∧ a ≠ e ∧ b ≠ e := by
      intro i
      obtain ⟨a, ha, b, hb, e, he, h1, h2, h3⟩ :=
        exists_pairwise_distinct (A := L' (V.u i) \ {x}) (B := L' (V.v i) \ {x})
          (C := L' (V.p i))
          (by have h := card_sdiff_singleton_ge (L' (V.u i)) x
              have h2 := hL' (V.u i)
              omega)
          (by have h := card_sdiff_singleton_ge (L' (V.v i)) x
              have h2 := hL' (V.v i)
              omega)
          (by have h := hL' (V.p i); omega)
      exact ⟨a, b, e, ha, hb, he, h1, h2, h3⟩
    choose ca cb cp hca hcb hcp hne1 hne2 hne3 using htri
    have hx_ca : ∀ i : Fin 4, x ≠ ca i := fun i => by
      have h : ca i ≠ x := by simpa using (Finset.mem_sdiff.mp (hca i)).2
      exact h.symm
    have hx_cb : ∀ i : Fin 4, x ≠ cb i := fun i => by
      have h : cb i ≠ x := by simpa using (Finset.mem_sdiff.mp (hcb i)).2
      exact h.symm
    have hcb_ca : ∀ i : Fin 4, cb i ≠ ca i := fun i => (hne1 i).symm
    have hcp_ca : ∀ i : Fin 4, cp i ≠ ca i := fun i => (hne2 i).symm
    have hcp_cb : ∀ i : Fin 4, cp i ≠ cb i := fun i => (hne3 i).symm
    refine ⟨fun w => match w with
      | .s1 => x
      | .s2 => x
      | .u i => ca i
      | .v i => cb i
      | .p i => cp i, ?_, ?_⟩
    · intro w
      cases w with
      | s1 => exact hx1
      | s2 => exact hx2
      | u i => exact (Finset.mem_sdiff.mp (hca i)).1
      | v i => exact (Finset.mem_sdiff.mp (hcb i)).1
      | p i => exact hcp i
    · intro a b hab
      cases a <;> cases b <;> simp_all [G_adj, adjB]
  · -- Case 2: the two terminal lists are disjoint.
    have hdisj : Disjoint (L' V.s1) (L' V.s2) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact Finset.not_nonempty_iff_eq_empty.mp hcase
    let P : Fin 4 → Finset (ℕ × ℕ) := fun i =>
      (L' (V.u i) ∩ L' V.s1) ×ˢ (L' (V.u i) ∩ L' V.s2)
    have hPle : ∀ i : Fin 4, (P i).card ≤ 2 := by
      intro i
      have hPcard : (P i).card =
          (L' (V.u i) ∩ L' V.s1).card * (L' (V.u i) ∩ L' V.s2).card := by
        simp [P, Finset.card_product]
      rw [hPcard]
      apply mul_le_two_of_add_le_three
      have hd : Disjoint (L' (V.u i) ∩ L' V.s1) (L' (V.u i) ∩ L' V.s2) :=
        hdisj.mono Finset.inter_subset_right Finset.inter_subset_right
      have hunion : ((L' (V.u i) ∩ L' V.s1) ∪ (L' (V.u i) ∩ L' V.s2)).card =
          (L' (V.u i) ∩ L' V.s1).card + (L' (V.u i) ∩ L' V.s2).card :=
        Finset.card_union_of_disjoint hd
      have hsub : ((L' (V.u i) ∩ L' V.s1) ∪ (L' (V.u i) ∩ L' V.s2)) ⊆ L' (V.u i) := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact (Finset.mem_inter.mp hw).1
        · exact (Finset.mem_inter.mp hw).1
      have h3 := Finset.card_le_card hsub
      rw [hL' (V.u i)] at h3
      omega
    have hUnion_le : ((Finset.univ : Finset (Fin 4)).biUnion P).card ≤ 8 := by
      calc ((Finset.univ : Finset (Fin 4)).biUnion P).card
          ≤ ∑ i : Fin 4, (P i).card := Finset.card_biUnion_le
        _ ≤ ∑ i : Fin 4, 2 := Finset.sum_le_sum (fun i _ => hPle i)
        _ = 8 := by simp
    have hQcard : (L' V.s1 ×ˢ L' V.s2).card = 9 := by
      rw [Finset.card_product, hL' V.s1, hL' V.s2]
    have hnotsub : ¬ (L' V.s1 ×ˢ L' V.s2) ⊆ (Finset.univ : Finset (Fin 4)).biUnion P := by
      intro hsub
      have h1 := Finset.card_le_card hsub
      omega
    obtain ⟨p, hpQ, hpR⟩ := Finset.not_subset.mp hnotsub
    have hp1 : p.1 ∈ L' V.s1 := (Finset.mem_product.mp hpQ).1
    have hp2 : p.2 ∈ L' V.s2 := (Finset.mem_product.mp hpQ).2
    have hpNot : ∀ i : Fin 4, ¬ (p.1 ∈ L' (V.u i) ∧ p.2 ∈ L' (V.u i)) := by
      intro i hcon
      exact hpR (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by
        rw [Finset.mem_product]
        exact ⟨Finset.mem_inter.mpr ⟨hcon.1, hp1⟩, Finset.mem_inter.mpr ⟨hcon.2, hp2⟩⟩⟩)
    have htri : ∀ i : Fin 4, ∃ a b e : ℕ,
        a ∈ L' (V.u i) \ {p.1, p.2} ∧ b ∈ L' (V.v i) \ {p.1, p.2} ∧
        e ∈ L' (V.p i) ∧ a ≠ b ∧ a ≠ e ∧ b ≠ e := by
      intro i
      have hv1 : 1 ≤ (L' (V.v i) \ {p.1, p.2}).card := by
        have h := card_sdiff_pair_ge' (L' (V.v i)) p.1 p.2
        have h2 := hL' (V.v i)
        omega
      have hu2 : 2 ≤ (L' (V.u i) \ {p.1, p.2}).card := by
        have h := card_sdiff_pair_ge (L' (V.u i)) p.1 p.2 (hpNot i)
        have h2 := hL' (V.u i)
        omega
      obtain ⟨xv, hxv, xu, hxu, z, hz, h1, h2, h3⟩ :=
        exists_pairwise_distinct (A := L' (V.v i) \ {p.1, p.2})
          (B := L' (V.u i) \ {p.1, p.2}) (C := L' (V.p i)) hv1 hu2
          (by have h := hL' (V.p i); omega)
      exact ⟨xu, xv, z, hxu, hxv, hz, h1.symm, h3, h2⟩
    choose cu cv cp hcu hcv hcp hne1 hne2 hne3 using htri
    have hp_cu1 : ∀ i : Fin 4, p.1 ≠ cu i := fun i => by
      intro hh
      have h := (Finset.mem_sdiff.mp (hcu i)).2
      exact h (by rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inl hh.symm)
    have hp_cu2 : ∀ i : Fin 4, p.2 ≠ cu i := fun i => by
      intro hh
      have h := (Finset.mem_sdiff.mp (hcu i)).2
      exact h (by rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr hh.symm)
    have hp_cv1 : ∀ i : Fin 4, p.1 ≠ cv i := fun i => by
      intro hh
      have h := (Finset.mem_sdiff.mp (hcv i)).2
      exact h (by rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inl hh.symm)
    have hp_cv2 : ∀ i : Fin 4, p.2 ≠ cv i := fun i => by
      intro hh
      have h := (Finset.mem_sdiff.mp (hcv i)).2
      exact h (by rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr hh.symm)
    have hcv_cu : ∀ i : Fin 4, cv i ≠ cu i := fun i => (hne1 i).symm
    have hcp_cu : ∀ i : Fin 4, cp i ≠ cu i := fun i => (hne2 i).symm
    have hcp_cv : ∀ i : Fin 4, cp i ≠ cv i := fun i => (hne3 i).symm
    refine ⟨fun w => match w with
      | .s1 => p.1
      | .s2 => p.2
      | .u i => cu i
      | .v i => cv i
      | .p i => cp i, ?_, ?_⟩
    · intro w
      cases w with
      | s1 => exact hp1
      | s2 => exact hp2
      | u i => exact (Finset.mem_sdiff.mp (hcu i)).1
      | v i => exact (Finset.mem_sdiff.mp (hcv i)).1
      | p i => exact hcp i
    · intro a b hab
      cases a <;> cases b <;> simp_all [G_adj, adjB]


/-- `G` is not 2-choosable: the paper's 2-list assignment `L` has no full proper colouring,
since at most 9 of the 14 vertices can be coloured from `L`. -/
theorem not_choosable_two : ¬ Choosable G 2 := by
  intro h
  have hL : IsListAssignment L 2 := by unfold IsListAssignment; decide
  obtain ⟨c, hc1, hc2⟩ := h L hL
  have hls : IsPartialListColoring G L (Finset.univ : Finset V) c := by
    refine ⟨?_, ?_⟩
    · intro v _
      exact hc1 v
    · intro u _ v _ huv
      exact hc2 u v huv
  have h9 := nine_bound (Finset.univ : Finset V) c hls
  have h14 : (Finset.univ : Finset V).card = 14 := by decide
  omega

/-- `G` is not 1-choosable: the constant 1-list assignment with list `{0}` admits no proper
colouring, since `G` has an edge. -/
theorem not_choosable_one : ¬ Choosable G 1 := by
  intro h
  have hL : IsListAssignment (fun _ : V => ({0} : Finset ℕ)) 1 := by
    intro v; simp
  obtain ⟨c, hc1, hc2⟩ := h (fun _ => {0}) hL
  have h0 : c (V.u 0) = 0 := by simpa using hc1 (V.u 0)
  have h1 : c (V.v 0) = 0 := by simpa using hc1 (V.v 0)
  exact hc2 (V.u 0) (V.v 0) (by decide) (by simp [h0, h1])

/-- `G` is not 0-choosable: every vertex has an empty list, so no vertex can be coloured. -/
theorem not_choosable_zero : ¬ Choosable G 0 := by
  intro h
  have hL : IsListAssignment (fun _ : V => (∅ : Finset ℕ)) 0 := fun v => by simp
  obtain ⟨c, hc1, hc2⟩ := h (fun _ => ∅) hL
  have hmem : c V.s1 ∈ (∅ : Finset ℕ) := hc1 V.s1
  exact absurd hmem (by simp)

/-- The paper's Theorem 1: the 14-vertex graph `G` has list chromatic number exactly 3, the
2-list assignment `L` admits no partial proper colouring of more than 9 vertices. -/
theorem counterexample : counterexample_statement := by
  refine ⟨by decide, ⟨choosable_three, ?_⟩, by unfold IsListAssignment; decide, nine_bound⟩
  intro j hj
  interval_cases j
  · exact not_choosable_zero
  · exact not_choosable_one
  · exact not_choosable_two

/-- The Partial List Colouring Conjecture is false. -/
theorem plcc_false : plcc_false_statement := by
  have hce := counterexample
  unfold counterexample_statement at hce
  obtain ⟨h14, hchoice, hL2, hbound⟩ := hce
  unfold plcc_false_statement PartialListColouringConjecture
  intro h
  obtain ⟨S, c, hcol, hineq⟩ :=
    h V G 3 2 (by norm_num) (by norm_num) (by norm_num) hchoice L hL2
  have h9 := hbound S c hcol
  omega

end DsBatch.P02
