import DsBatch.P10.Defs

/-!
# P10 — Proofs

The paper's argument that the list assignment `Lstar` of Section 2 admits no proper
total colouring:

* Lemma 1 (`k23_same_colour`): in every total colouring of `K_{2,3}` with four
  colours, the two vertices on the side of size two receive the same colour;
* hence the two private vertices `a_i`, `b_i` of every block `B_i` receive the
  same colour `s i`, and `s i ≠ i`;
* every cross edge between `B_i` and `B_j` receives a colour in
  `S_i ∩ S_j`, where `S_i = {i, s i}`;
* the four sets `S_1, …, S_4` have a common colour `t`, and the cross edge whose
  list omits `t` cannot be coloured.

Everything here is a proof of the frozen statements in `Statement.lean`; the
definitions live in `Defs.lean`.
-/

namespace DsBatch.P10

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ## Elementary incidence facts -/

lemma elAdj_vv {u w : V} (h : G.Adj u w) : elAdj (Sum.inl u) (Sum.inl w) := h

lemma elAdj_ve {u : V} {e : E} (h : eLeft e = u ∨ eRight e = u) :
    elAdj (Sum.inl u) (Sum.inr e) := h

lemma elAdj_ev {u : V} {e : E} (h : eLeft e = u ∨ eRight e = u) :
    elAdj (Sum.inr e) (Sum.inl u) := h

lemma elAdj_ee {e f : E} (hne : e ≠ f)
    (h : eLeft e = eLeft f ∨ eLeft e = eRight f ∨
      eRight e = eLeft f ∨ eRight e = eRight f) :
    elAdj (Sum.inr e) (Sum.inr f) := ⟨hne, h⟩

/-- `v_{i,j}` is adjacent to `a_i`. -/
lemma adj_term_va (i j : Fin 4) (h : i ≠ j) : G.Adj (vt i j h) (va i) :=
  G.adj_symm ((adj_va_term i ⟨(i, j), h⟩).mpr rfl)

/-- `v_{i,j}` is adjacent to `b_i`. -/
lemma adj_term_vb (i j : Fin 4) (h : i ≠ j) : G.Adj (vt i j h) (vb i) :=
  G.adj_symm ((adj_vb_term i ⟨(i, j), h⟩).mpr rfl)

lemma incid_eA_va (i j : Fin 4) (h : i ≠ j) : elAdj (Sum.inr (eA i j h)) (Sum.inl (va i)) :=
  Or.inl (eA_left i j h)

lemma incid_eA_term (i j : Fin 4) (h : i ≠ j) : elAdj (Sum.inr (eA i j h)) (Sum.inl (vt i j h)) :=
  Or.inr (eA_right i j h)

lemma incid_eB_vb (i j : Fin 4) (h : i ≠ j) : elAdj (Sum.inr (eB i j h)) (Sum.inl (vb i)) :=
  Or.inl (eB_left i j h)

lemma incid_eB_term (i j : Fin 4) (h : i ≠ j) : elAdj (Sum.inr (eB i j h)) (Sum.inl (vt i j h)) :=
  Or.inr (eB_right i j h)

lemma incid_eA_term' (i j : Fin 4) (h : i ≠ j) :
    elAdj (Sum.inl (vt i j h)) (Sum.inr (eA i j h)) :=
  Or.inr (eA_right i j h)

lemma incid_eB_term' (i j : Fin 4) (h : i ≠ j) :
    elAdj (Sum.inl (vt i j h)) (Sum.inr (eB i j h)) :=
  Or.inr (eB_right i j h)

lemma incid_cross_term (i j : Fin 4) (h : i ≠ j) :
    elAdj (Sum.inl (vt i j h)) (Sum.inr (crossE i j h)) :=
  crossE_inc_left i j h

lemma edges_eA_eB (i j : Fin 4) (h : i ≠ j) :
    elAdj (Sum.inr (eA i j h)) (Sum.inr (eB i j h)) := by
  refine elAdj_ee (by simp [eA, eB]) (Or.inr (Or.inr (Or.inr ?_)))
  rw [eA_right, eB_right]

lemma cross_share_eA (i j : Fin 4) (h : i ≠ j) :
    elAdj (Sum.inr (crossE i j h)) (Sum.inr (eA i j h)) := by
  refine elAdj_ee (by simp [crossE, eA]) ?_
  rcases crossE_inc_left i j h with hl | hr
  · exact Or.inr (Or.inl (hl.trans (eA_right i j h).symm))
  · exact Or.inr (Or.inr (Or.inr (hr.trans (eA_right i j h).symm)))

lemma cross_share_eB (i j : Fin 4) (h : i ≠ j) :
    elAdj (Sum.inr (crossE i j h)) (Sum.inr (eB i j h)) := by
  refine elAdj_ee (by simp [crossE, eB]) ?_
  rcases crossE_inc_left i j h with hl | hr
  · exact Or.inr (Or.inl (hl.trans (eB_right i j h).symm))
  · exact Or.inr (Or.inr (Or.inr (hr.trans (eB_right i j h).symm)))

/-! ## Lemma 1: total colourings of `K_{2,3}` -/

/-- **Lemma 1 of the paper.** In every proper total colouring of `K_{2,3}` whose
colours lie in a set `P` of four colours, the two vertices `a`, `b` on the side
of the bipartition of size two receive the same colour.

The `K_{2,3}` is presented by the colours `ca`, `cb` of `a`, `b`, the colours
`u k` of the three vertices on the other side and the colours `ea k`, `eb k` of
the edges from `a` and `b` to the `k`-th such vertex. -/
lemma k23_same_colour {α : Type} [DecidableEq α]
    (P : Finset α) (hP : P.card = 4)
    (ca cb : α) (u ea eb : Fin 3 → α)
    (hca : ca ∈ P) (hcb : cb ∈ P)
    (hu : ∀ k, u k ∈ P) (heaP : ∀ k, ea k ∈ P) (hebP : ∀ k, eb k ∈ P)
    (hua : ∀ k, u k ≠ ca) (hub : ∀ k, u k ≠ cb)
    (heaa : ∀ k, ea k ≠ ca) (heau : ∀ k, ea k ≠ u k)
    (hebb : ∀ k, eb k ≠ cb) (hebu : ∀ k, eb k ≠ u k)
    (heaeb : ∀ k, ea k ≠ eb k)
    (heainj : Function.Injective ea) (hebinj : Function.Injective eb) :
    ca = cb := by
  by_contra hne
  have hne' : ca ≠ cb := hne
  have hcb' : cb ∈ P.erase ca := Finset.mem_erase.mpr ⟨Ne.symm hne', hcb⟩
  have hQcard : ((P.erase ca).erase cb).card = 2 := by
    rw [Finset.card_erase_of_mem hcb', Finset.card_erase_of_mem hca, hP]
  have huQ : ∀ k, u k ∈ (P.erase ca).erase cb := fun k =>
    Finset.mem_erase.mpr ⟨hub k, Finset.mem_erase.mpr ⟨hua k, hu k⟩⟩
  obtain ⟨i, -, j, -, hij, huij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := (Finset.univ : Finset (Fin 3))) (t := (P.erase ca).erase cb)
      (f := u) (by rw [hQcard]; simp) (fun x _ => huQ x)
  set x := u i with hxdef
  have hxj : u j = x := huij.symm
  have hxQ : x ∈ (P.erase ca).erase cb := hxdef ▸ huQ i
  have hxP : x ∈ P.erase ca := Finset.mem_of_mem_erase hxQ
  have hxP' : x ∈ P := Finset.mem_of_mem_erase hxP
  have hxca : x ≠ ca := Finset.ne_of_mem_erase hxP
  have hxcb : x ≠ cb := Finset.ne_of_mem_erase hxQ
  obtain ⟨m, hmi, hmj⟩ : ∃ m : Fin 3, m ≠ i ∧ m ≠ j := by
    have hsub : ({i, j} : Finset (Fin 3)) ⊂ Finset.univ := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_univ _, ?_⟩
      intro h
      have h1 : ({i, j} : Finset (Fin 3)).card = 3 := by rw [h]; simp
      have h2 : ({i, j} : Finset (Fin 3)).card = 2 := by simp [hij]
      omega
    obtain ⟨m, -, hm⟩ := Finset.exists_of_ssubset hsub
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    exact ⟨m, hm.1, hm.2⟩
  have hea_mem : ∀ k : Fin 3, ea k ∈ P.erase ca := fun k =>
    Finset.mem_erase.mpr ⟨heaa k, heaP k⟩
  have hmem : x ∈ ({ea i, ea j, ea m} : Finset α) := by
    by_contra hnot
    have hsub : ({x, ea i, ea j, ea m} : Finset α) ⊆ P.erase ca := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hxP
      · exact hea_mem i
      · exact hea_mem j
      · exact hea_mem m
    have hxi : x ∉ ({ea i, ea j, ea m} : Finset α) := hnot
    have heij : ea i ≠ ea j := fun h => hij (heainj h)
    have heim : ea i ≠ ea m := fun h => hmi (heainj h).symm
    have hejm : ea j ≠ ea m := fun h => hmj (heainj h).symm
    have h2 : ea i ∉ ({ea j, ea m} : Finset α) := by simp [heij, heim]
    have h3 : ea j ∉ ({ea m} : Finset α) := by simp [hejm]
    have hcard4 : ({x, ea i, ea j, ea m} : Finset α).card = 4 := by
      rw [Finset.card_insert_of_notMem hxi, Finset.card_insert_of_notMem h2,
        Finset.card_insert_of_notMem h3, Finset.card_singleton]
    have hcardP : (P.erase ca).card = 3 := by
      rw [Finset.card_erase_of_mem hca, hP]
    have := Finset.card_le_card hsub
    omega
  have heam : ea m = x := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · exact (heau i (h.symm.trans hxdef)).elim
    · exact (heau j (h.symm.trans hxj.symm)).elim
    · exact h.symm
  have heb_mem : ∀ k : Fin 3, eb k ∈ P.erase cb := fun k =>
    Finset.mem_erase.mpr ⟨hebb k, hebP k⟩
  have hmemb : x ∈ ({eb i, eb j, eb m} : Finset α) := by
    by_contra hnot
    have hsub : ({x, eb i, eb j, eb m} : Finset α) ⊆ P.erase cb := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact Finset.mem_erase.mpr ⟨hxcb, hxP'⟩
      · exact heb_mem i
      · exact heb_mem j
      · exact heb_mem m
    have hxi : x ∉ ({eb i, eb j, eb m} : Finset α) := hnot
    have heij : eb i ≠ eb j := fun h => hij (hebinj h)
    have heim : eb i ≠ eb m := fun h => hmi (hebinj h).symm
    have hejm : eb j ≠ eb m := fun h => hmj (hebinj h).symm
    have h2 : eb i ∉ ({eb j, eb m} : Finset α) := by simp [heij, heim]
    have h3 : eb j ∉ ({eb m} : Finset α) := by simp [hejm]
    have hcard4 : ({x, eb i, eb j, eb m} : Finset α).card = 4 := by
      rw [Finset.card_insert_of_notMem hxi, Finset.card_insert_of_notMem h2,
        Finset.card_insert_of_notMem h3, Finset.card_singleton]
    have hcardP : (P.erase cb).card = 3 := by
      rw [Finset.card_erase_of_mem hcb, hP]
    have := Finset.card_le_card hsub
    omega
  have hebm : eb m = x := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmemb
    rcases hmemb with h | h | h
    · exact (hebu i (h.symm.trans hxdef)).elim
    · exact (hebu j (h.symm.trans hxj.symm)).elim
    · exact h.symm
  exact heaeb m (heam.trans hebm.symm)

/-! ## Private vertices of a block have the same colour -/

/-- In any proper total colouring drawn from the lists `Lstar`, the two private
vertices `a_i` and `b_i` of a block receive the same colour.  This is the
paper's application of Lemma 1 to the block `B_i`: its colours are drawn from
the five colours with `i` deleted. -/
lemma block_eq (c : El → Fin 5) (hproper : ProperTotalColoring c)
    (hmem : ∀ x : El, c x ∈ Lstar x) (i : Fin 4) :
    c (Sum.inl (va i)) = c (Sum.inl (vb i)) := by
  have hP : (Finset.univ.erase (Fin.castSucc i)).card = 4 := by simp
  have hvaP : c (Sum.inl (va i)) ∈ Finset.univ.erase (Fin.castSucc i) := by
    simpa [Lstar, vBlock, va] using hmem (Sum.inl (va i))
  have hvbP : c (Sum.inl (vb i)) ∈ Finset.univ.erase (Fin.castSucc i) := by
    simpa [Lstar, vBlock, vb] using hmem (Sum.inl (vb i))
  let u : Fin 3 → Fin 5 :=
    fun k => c (Sum.inl (vt i (i.succAbove k) (Fin.succAbove_ne i k).symm))
  let ea : Fin 3 → Fin 5 :=
    fun k => c (Sum.inr (eA i (i.succAbove k) (Fin.succAbove_ne i k).symm))
  let eb : Fin 3 → Fin 5 :=
    fun k => c (Sum.inr (eB i (i.succAbove k) (Fin.succAbove_ne i k).symm))
  have huP : ∀ k, u k ∈ Finset.univ.erase (Fin.castSucc i) := fun k => by
    dsimp only [u]
    simpa [Lstar, vBlock, vt] using
      hmem (Sum.inl (vt i (i.succAbove k) (Fin.succAbove_ne i k).symm))
  have heaP : ∀ k, ea k ∈ Finset.univ.erase (Fin.castSucc i) := fun k => by
    dsimp only [ea]
    simpa [Lstar, eBlock, eA] using
      hmem (Sum.inr (eA i (i.succAbove k) (Fin.succAbove_ne i k).symm))
  have hebP : ∀ k, eb k ∈ Finset.univ.erase (Fin.castSucc i) := fun k => by
    dsimp only [eb]
    simpa [Lstar, eBlock, eB] using
      hmem (Sum.inr (eB i (i.succAbove k) (Fin.succAbove_ne i k).symm))
  have hua : ∀ k, u k ≠ c (Sum.inl (va i)) := fun k => by
    have h := hproper
      (Sum.inl (vt i (i.succAbove k) (Fin.succAbove_ne i k).symm)) (Sum.inl (va i))
      (elAdj_vv (adj_term_va i (i.succAbove k) (Fin.succAbove_ne i k).symm))
    simpa [u] using h
  have hub : ∀ k, u k ≠ c (Sum.inl (vb i)) := fun k => by
    have h := hproper
      (Sum.inl (vt i (i.succAbove k) (Fin.succAbove_ne i k).symm)) (Sum.inl (vb i))
      (elAdj_vv (adj_term_vb i (i.succAbove k) (Fin.succAbove_ne i k).symm))
    simpa [u] using h
  have heaa : ∀ k, ea k ≠ c (Sum.inl (va i)) := fun k => by
    have h := hproper
      (Sum.inr (eA i (i.succAbove k) (Fin.succAbove_ne i k).symm)) (Sum.inl (va i))
      (incid_eA_va i (i.succAbove k) (Fin.succAbove_ne i k).symm)
    simpa [ea] using h
  have heau : ∀ k, ea k ≠ u k := fun k => by
    have h := hproper
      (Sum.inr (eA i (i.succAbove k) (Fin.succAbove_ne i k).symm))
      (Sum.inl (vt i (i.succAbove k) (Fin.succAbove_ne i k).symm))
      (incid_eA_term i (i.succAbove k) (Fin.succAbove_ne i k).symm)
    simpa [ea, u] using h
  have hebb : ∀ k, eb k ≠ c (Sum.inl (vb i)) := fun k => by
    have h := hproper
      (Sum.inr (eB i (i.succAbove k) (Fin.succAbove_ne i k).symm)) (Sum.inl (vb i))
      (incid_eB_vb i (i.succAbove k) (Fin.succAbove_ne i k).symm)
    simpa [eb] using h
  have hebu : ∀ k, eb k ≠ u k := fun k => by
    have h := hproper
      (Sum.inr (eB i (i.succAbove k) (Fin.succAbove_ne i k).symm))
      (Sum.inl (vt i (i.succAbove k) (Fin.succAbove_ne i k).symm))
      (incid_eB_term i (i.succAbove k) (Fin.succAbove_ne i k).symm)
    simpa [eb, u] using h
  have heaeb : ∀ k, ea k ≠ eb k := fun k => by
    have h := hproper
      (Sum.inr (eA i (i.succAbove k) (Fin.succAbove_ne i k).symm))
      (Sum.inr (eB i (i.succAbove k) (Fin.succAbove_ne i k).symm))
      (edges_eA_eB i (i.succAbove k) (Fin.succAbove_ne i k).symm)
    simpa [ea, eb] using h
  have heainj : Function.Injective ea := by
    intro k l hkl
    by_contra hne
    have hne' : i.succAbove k ≠ i.succAbove l :=
      fun h => hne (Fin.succAbove_right_injective h)
    have hdist : eA i (i.succAbove k) (Fin.succAbove_ne i k).symm ≠
        eA i (i.succAbove l) (Fin.succAbove_ne i l).symm := by
      simp [eA, hne']
    have hadj : elAdj
        (Sum.inr (eA i (i.succAbove k) (Fin.succAbove_ne i k).symm))
        (Sum.inr (eA i (i.succAbove l) (Fin.succAbove_ne i l).symm)) :=
      elAdj_ee hdist (Or.inl (by rw [eA_left, eA_left]))
    exact hproper _ _ hadj hkl
  have hebinj : Function.Injective eb := by
    intro k l hkl
    by_contra hne
    have hne' : i.succAbove k ≠ i.succAbove l :=
      fun h => hne (Fin.succAbove_right_injective h)
    have hdist : eB i (i.succAbove k) (Fin.succAbove_ne i k).symm ≠
        eB i (i.succAbove l) (Fin.succAbove_ne i l).symm := by
      simp [eB, hne']
    have hadj : elAdj
        (Sum.inr (eB i (i.succAbove k) (Fin.succAbove_ne i k).symm))
        (Sum.inr (eB i (i.succAbove l) (Fin.succAbove_ne i l).symm)) :=
      elAdj_ee hdist (Or.inl (by rw [eB_left, eB_left]))
    exact hproper _ _ hadj hkl
  exact k23_same_colour (Finset.univ.erase (Fin.castSucc i)) hP
    (c (Sum.inl (va i))) (c (Sum.inl (vb i))) u ea eb
    hvaP hvbP huP heaP hebP hua hub heaa heau hebb hebu heaeb heainj hebinj

/-! ## The sets `S_i = {i, s_i}` -/

/-- The set `S_i = {i, s_i}` of the paper, where `s_i` is the common colour of
`a_i` and `b_i`. -/
def Sset (c : El → Fin 5) (i : Fin 4) : Finset (Fin 5) :=
  {Fin.castSucc i, c (Sum.inl (va i))}

/-- A counting fact: if three distinct colours `y1, y2, y3` of a set `P` of four
colours all differ from a colour `s ∈ P`, and `P` is the set of five colours
with `i` removed, then any colour `x` differing from all three lies in `{i, s}`.

This is the paper's observation that a cross edge receives a colour in
`S_i ∩ S_j`: the colours of `v_{i,j}`, `a_i v_{i,j}` and `b_i v_{i,j}` are three
distinct colours of the four available to `B_i` other than `s_i`, so the fourth
colour outside `{i, s_i}` is impossible for the cross edge. -/
lemma mem_pair_of_three {α : Type} [DecidableEq α] [Fintype α]
    (P : Finset α) (i s y1 y2 y3 x : α)
    (hP : P = Finset.univ.erase i) (hPcard : P.card = 4)
    (hs : s ∈ P) (hy1 : y1 ∈ P) (hy2 : y2 ∈ P) (hy3 : y3 ∈ P)
    (hs1 : y1 ≠ s) (hs2 : y2 ≠ s) (hs3 : y3 ≠ s)
    (h12 : y1 ≠ y2) (h13 : y1 ≠ y3) (h23 : y2 ≠ y3)
    (hx1 : x ≠ y1) (hx2 : x ≠ y2) (hx3 : x ≠ y3) :
    x ∈ ({i, s} : Finset α) := by
  have hcErase : (P.erase s).card = 3 := by
    rw [Finset.card_erase_of_mem hs, hPcard]
  have hc3 : ({y1, y2, y3} : Finset α).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
      Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
  have hsub : ({y1, y2, y3} : Finset α) ⊆ P.erase s := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hs1, hy1⟩
    · exact Finset.mem_erase.mpr ⟨hs2, hy2⟩
    · exact Finset.mem_erase.mpr ⟨hs3, hy3⟩
  have hset : ({y1, y2, y3} : Finset α) = P.erase s :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcErase, hc3])
  by_contra hx
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  obtain ⟨hxi, hxs⟩ := hx
  have hxP : x ∈ P := by
    rw [hP]
    exact Finset.mem_erase.mpr ⟨hxi, Finset.mem_univ x⟩
  have hxPs : x ∈ P.erase s := Finset.mem_erase.mpr ⟨hxs, hxP⟩
  rw [← hset] at hxPs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxPs
  rcases hxPs with h | h | h
  · exact hx1 h
  · exact hx2 h
  · exact hx3 h

/-- A cross edge between `B_i` and `B_j` receives a colour in `S_i`. -/
lemma cross_mem_Sset (c : El → Fin 5) (hproper : ProperTotalColoring c)
    (hmem : ∀ x : El, c x ∈ Lstar x)
    (hblock : ∀ i, c (Sum.inl (vb i)) = c (Sum.inl (va i)))
    (i j : Fin 4) (h : i ≠ j) :
    c (Sum.inr (crossE i j h)) ∈ Sset c i := by
  have hPcard : (Finset.univ.erase (Fin.castSucc i) : Finset (Fin 5)).card = 4 := by simp
  have hs : c (Sum.inl (va i)) ∈ (Finset.univ.erase (Fin.castSucc i) : Finset (Fin 5)) := by
    simpa [Lstar, vBlock, va] using hmem (Sum.inl (va i))
  have hy1 : c (Sum.inl (vt i j h)) ∈
      (Finset.univ.erase (Fin.castSucc i) : Finset (Fin 5)) := by
    simpa [Lstar, vBlock, vt] using hmem (Sum.inl (vt i j h))
  have hy2 : c (Sum.inr (eA i j h)) ∈
      (Finset.univ.erase (Fin.castSucc i) : Finset (Fin 5)) := by
    simpa [Lstar, eBlock, eA] using hmem (Sum.inr (eA i j h))
  have hy3 : c (Sum.inr (eB i j h)) ∈
      (Finset.univ.erase (Fin.castSucc i) : Finset (Fin 5)) := by
    simpa [Lstar, eBlock, eB] using hmem (Sum.inr (eB i j h))
  have hs1 : c (Sum.inl (vt i j h)) ≠ c (Sum.inl (va i)) :=
    hproper _ _ (elAdj_vv (adj_term_va i j h))
  have hs2 : c (Sum.inr (eA i j h)) ≠ c (Sum.inl (va i)) :=
    hproper _ _ (incid_eA_va i j h)
  have hs3 : c (Sum.inr (eB i j h)) ≠ c (Sum.inl (va i)) := by
    have hh := hproper _ _ (incid_eB_vb i j h)
    rwa [hblock i] at hh
  have h12 : c (Sum.inl (vt i j h)) ≠ c (Sum.inr (eA i j h)) :=
    hproper _ _ (incid_eA_term' i j h)
  have h13 : c (Sum.inl (vt i j h)) ≠ c (Sum.inr (eB i j h)) :=
    hproper _ _ (incid_eB_term' i j h)
  have h23 : c (Sum.inr (eA i j h)) ≠ c (Sum.inr (eB i j h)) :=
    hproper _ _ (edges_eA_eB i j h)
  have hx1 : c (Sum.inr (crossE i j h)) ≠ c (Sum.inl (vt i j h)) :=
    hproper _ _ (elAdj_ev (crossE_inc_left i j h))
  have hx2 : c (Sum.inr (crossE i j h)) ≠ c (Sum.inr (eA i j h)) :=
    hproper _ _ (cross_share_eA i j h)
  have hx3 : c (Sum.inr (crossE i j h)) ≠ c (Sum.inr (eB i j h)) :=
    hproper _ _ (cross_share_eB i j h)
  exact mem_pair_of_three (Finset.univ.erase (Fin.castSucc i))
    (Fin.castSucc i) (c (Sum.inl (va i)))
    (c (Sum.inl (vt i j h))) (c (Sum.inr (eA i j h))) (c (Sum.inr (eB i j h)))
    (c (Sum.inr (crossE i j h)))
    rfl hPcard hs hy1 hy2 hy3 hs1 hs2 hs3 h12 h13 h23 hx1 hx2 hx3

/-- A cross edge between `B_i` and `B_j` receives a colour in `S_j`. -/
lemma cross_mem_Sset' (c : El → Fin 5) (hproper : ProperTotalColoring c)
    (hmem : ∀ x : El, c x ∈ Lstar x)
    (hblock : ∀ i, c (Sum.inl (vb i)) = c (Sum.inl (va i)))
    (i j : Fin 4) (h : i ≠ j) :
    c (Sum.inr (crossE i j h)) ∈ Sset c j := by
  rw [crossE_comm]
  exact cross_mem_Sset c hproper hmem hblock j i h.symm

/-! ## Four pairwise-intersecting sets `{i, s_i}` have a common element -/

/-- The set `{i, s i}` attached to the index `i : Fin 4` by a function
`s : Fin 4 → Fin 5`. -/
def Sfour (s : Fin 4 → Fin 5) (i : Fin 4) : Finset (Fin 5) :=
  {Fin.castSucc i, s i}

/-- None of the sets `{i, s i}` contains its own index. -/
def FourNoFixed (s : Fin 4 → Fin 5) : Prop := ∀ i, s i ≠ Fin.castSucc i

/-- The four sets `{i, s i}` are pairwise intersecting. -/
def FourPairwiseMeet (s : Fin 4 → Fin 5) : Prop :=
  ∀ i j : Fin 4, i ≠ j → (Sfour s i ∩ Sfour s j).Nonempty

/-- The four sets `{i, s i}` have a common element. -/
def FourHasCommon (s : Fin 4 → Fin 5) : Prop :=
  ∃ t : Fin 5, ∀ i : Fin 4, t ∈ Sfour s i

instance instDecFourNoFixed (s : Fin 4 → Fin 5) : Decidable (FourNoFixed s) := by
  unfold FourNoFixed
  infer_instance

instance instDecFourPairwiseMeet (s : Fin 4 → Fin 5) : Decidable (FourPairwiseMeet s) := by
  unfold FourPairwiseMeet
  exact @Fintype.decidableForallFintype (Fin 4)
    (fun i => ∀ j : Fin 4, i ≠ j → (Sfour s i ∩ Sfour s j).Nonempty)
    (fun i => @Fintype.decidableForallFintype (Fin 4)
      (fun j => i ≠ j → (Sfour s i ∩ Sfour s j).Nonempty)
      (fun j => inferInstance)
      inferInstance)
    inferInstance

instance instDecFourHasCommon (s : Fin 4 → Fin 5) : Decidable (FourHasCommon s) := by
  unfold FourHasCommon
  exact @Fintype.decidableExistsFintype (Fin 5)
    (fun t => ∀ i : Fin 4, t ∈ Sfour s i)
    (fun t => @Fintype.decidableForallFintype (Fin 4)
      (fun i => t ∈ Sfour s i) (fun i => inferInstance) inferInstance)
    inferInstance

/-- **The paper's final counting step** (the paragraph after Lemma 1): four
pairwise-intersecting sets of the form `S_i = {i, s_i}`, each avoiding its own
index `i`, have a common colour.  This is a finite check over the `5^4 = 625`
functions `s : Fin 4 → Fin 5`. -/
lemma four_sets_common : ∀ (s : Fin 4 → Fin 5),
    FourNoFixed s → FourPairwiseMeet s → FourHasCommon s := by
  decide

/-! ## The final contradiction -/

/-- If a colour `t` lies in `S_a` and `S_b` for two distinct blocks `a ≠ b`, and
the list of the cross edge between `B_a` and `B_b` omits `t`, then the cross
edge, whose colour must lie in `S_a ∩ S_b = {t}`, cannot be coloured. -/
lemma contradiction_of_common (c : El → Fin 5) (hproper : ProperTotalColoring c)
    (hmem : ∀ x : El, c x ∈ Lstar x)
    (hblock : ∀ i, c (Sum.inl (vb i)) = c (Sum.inl (va i)))
    (t : Fin 5) (a b : Fin 4) (hab : a ≠ b)
    (hta : t ≠ Fin.castSucc a) (htb : t ≠ Fin.castSucc b)
    (hSa : t ∈ Sset c a) (hSb : t ∈ Sset c b)
    (hl : t ∉ Lstar (Sum.inr (crossE a b hab))) : False := by
  have hsa : c (Sum.inl (va a)) = t := by
    have hh := hSa
    simp only [Sset, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with h | h
    · exact absurd h hta
    · exact h.symm
  have hsb : c (Sum.inl (va b)) = t := by
    have hh := hSb
    simp only [Sset, Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with h | h
    · exact absurd h htb
    · exact h.symm
  have hca : c (Sum.inr (crossE a b hab)) ∈ Sset c a :=
    cross_mem_Sset c hproper hmem hblock a b hab
  have hcb : c (Sum.inr (crossE a b hab)) ∈ Sset c b :=
    cross_mem_Sset' c hproper hmem hblock a b hab
  have hcol : c (Sum.inr (crossE a b hab)) = t := by
    have h1 : c (Sum.inr (crossE a b hab)) ∈
        ({Fin.castSucc a, t} : Finset (Fin 5)) := by
      simpa [Sset, hsa] using hca
    have h2 : c (Sum.inr (crossE a b hab)) ∈
        ({Fin.castSucc b, t} : Finset (Fin 5)) := by
      simpa [Sset, hsb] using hcb
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (Fin.castSucc_inj.mp (h1.symm.trans h2)) hab
    · exact h2
    · exact h1
    · exact h1
  exact hl (hcol ▸ hmem (Sum.inr (crossE a b hab)))

/-- The list assignment `Lstar` of Section 2 admits no proper total colouring:
the counterexample of the paper. -/
theorem not_list_total_colourable : ¬ ListTotalColourable Lstar := by
  rintro ⟨c, hproper, hmem⟩
  have hblock : ∀ i, c (Sum.inl (vb i)) = c (Sum.inl (va i)) :=
    fun i => (block_eq c hproper hmem i).symm
  have hNoFixed : FourNoFixed (fun i => c (Sum.inl (va i))) := by
    intro i
    have h := hmem (Sum.inl (va i))
    simp only [Lstar, vBlock, va] at h
    exact Finset.ne_of_mem_erase h
  have hMeet : FourPairwiseMeet (fun i => c (Sum.inl (va i))) := by
    intro i j hij
    exact ⟨c (Sum.inr (crossE i j hij)), Finset.mem_inter.mpr
      ⟨cross_mem_Sset c hproper hmem hblock i j hij,
       cross_mem_Sset' c hproper hmem hblock i j hij⟩⟩
  obtain ⟨t, ht⟩ := four_sets_common (fun i => c (Sum.inl (va i))) hNoFixed hMeet
  fin_cases t
  · exact contradiction_of_common c hproper hmem hblock (0 : Fin 5) 2 3
      (by decide) (by decide) (by decide) (ht 2) (ht 3) (by decide)
  · exact contradiction_of_common c hproper hmem hblock (1 : Fin 5) 3 0
      (by decide) (by decide) (by decide) (ht 3) (ht 0) (by decide)
  · exact contradiction_of_common c hproper hmem hblock (2 : Fin 5) 0 1
      (by decide) (by decide) (by decide) (ht 0) (ht 1) (by decide)
  · exact contradiction_of_common c hproper hmem hblock (3 : Fin 5) 1 2
      (by decide) (by decide) (by decide) (ht 1) (ht 2) (by decide)
  · exact contradiction_of_common c hproper hmem hblock (4 : Fin 5) 0 2
      (by decide) (by decide) (by decide) (ht 0) (ht 2) (by decide)

/-! ## The four-colouring and the counting facts -/

/-- The vertex set has `20` elements. -/
lemma card_V : Fintype.card V = 20 := by decide

/-- The graph is cubic. -/
lemma cubic_G : Cubic := by decide

/-- The explicit four-colouring of Section 2 is a proper total colouring. -/
lemma colour4_proper : ProperTotalColoring colour4 := by decide

/-- The assignment `Lstar` gives every element a list of four colours. -/
lemma lists_card : ∀ x : El, (Lstar x).card = 4 := by decide

/-- There is no proper total colouring of `G` with three colours: `G` is cubic,
so at any vertex the vertex together with its three incident edges are four
pairwise conflicting elements. -/
lemma no_three_colouring : ¬ ∃ c : El → Fin 3, ProperTotalColoring c := by
  rintro ⟨c, hproper⟩
  let g : Fin 4 → El := fun k =>
    if k = 0 then Sum.inl (va 0)
    else if k = 1 then Sum.inr (eA 0 1 (by decide))
    else if k = 2 then Sum.inr (eA 0 2 (by decide))
    else Sum.inr (eA 0 3 (by decide))
  have hconf : ∀ i j : Fin 4, i ≠ j → elAdj (g i) (g j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [g] <;> decide
  have hinj : Function.Injective (fun k => c (g k)) := by
    intro i j hij
    by_contra hne
    exact hproper (g i) (g j) (hconf i j hne) hij
  have hle := Fintype.card_le_of_injective (fun k => c (g k)) hinj
  simp at hle

end DsBatch.P10
