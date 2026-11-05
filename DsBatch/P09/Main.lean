import DsBatch.P09.Proof

/-!
# P09 — Main

Targets of the formalization of arXiv 2609.04257.
Statements are in `DsBatch/P09/Statement.lean`; the computations in
`DsBatch/P09/Cert.lean`; the lemmas in `DsBatch/P09/Proof.lean`.
-/

namespace DsBatch.P09

open SimpleGraph

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The paper's graph `G` is a connected cubic bipartite graph on 18 vertices. -/
theorem graph_structure : graph_structure_statement := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · refine ⟨?_⟩
    decide
  · intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    fin_cases v <;> decide
  · refine ⟨bip, ?_⟩
    intro v w h
    exact bip_ok v w h

/-- The domination number of `G` is `6`. -/
theorem gamma_eq_six : gamma_eq_six_statement := by
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨{0, 1, 2, 3, 14, 15}, by decide, by unfold Dominates; decide⟩
  · by_contra hlt
    push_neg at hlt
    have hne : {m : ℕ | ∃ D : Finset V, D.card = m ∧ Dominates G D}.Nonempty :=
      ⟨_, Finset.univ, rfl, fun v => Or.inl (Finset.mem_univ v)⟩
    obtain ⟨D, hDcard, hDdom⟩ := Nat.sInf_mem hne
    have hDcard' : D.card = dominationNumber G := hDcard
    have h5 : D.card ≤ 5 := by omega
    obtain ⟨t, hDt, ht5⟩ := Finset.exists_superset_card_eq h5 (by decide : 5 ≤ Fintype.card V)
    exact not_dominates_of_card_five ht5 (dominates_mono hDt hDdom)

/-- Deleting any at most four edges of `G` leaves domination number `6`. -/
theorem four_edge : four_edge_statement := by
  intro F hF hcard
  let I : Finset (Fin 27) := F.image idx
  have hInj : Set.InjOn idx ↑F := by
    intro e1 he1 e2 he2 heq
    have h1 : eOf (idx e1) = e1 := eOf_idx (hF e1 he1)
    have h2 : eOf (idx e2) = e2 := eOf_idx (hF e2 he2)
    rw [← h1, ← h2, heq]
  have hIcard : I.card ≤ 4 := by
    dsimp only [I]
    have hc : (F.image idx).card = F.card := Finset.card_image_of_injOn hInj
    omega
  have hI : ∀ j : Fin 27, j ∈ I ↔ eOf j ∈ F := by
    intro j
    constructor
    · intro hj
      obtain ⟨e, he, hej⟩ := Finset.mem_image.mp hj
      rw [← hej, eOf_idx (hF e he)]
      exact he
    · intro hj
      exact Finset.mem_image.mpr ⟨eOf j, hj, idx_eOf j⟩
  obtain ⟨D, hD6, hDdom⟩ := exists_dominating_six F I hI hIcard
  apply le_antisymm
  · have hle : dominationNumber (G.deleteEdges (F : Set (Sym2 V))) ≤ D.card :=
      Nat.sInf_le ⟨D, rfl, hDdom⟩
    omega
  · rw [← gamma_eq_six]
    exact dominationNumber_le_of_le (SimpleGraph.deleteEdges_le (F : Set (Sym2 V)))

/-- The bondage number of `G` is at least `5`. -/
theorem bondage_ge_five : bondage_ge_five_statement := by
  show 5 ≤ sInf {k : ℕ | ∃ F : Finset (Sym2 V), (∀ e ∈ F, e ∈ G.edgeSet) ∧ F.card = k ∧
      dominationNumber (G.deleteEdges (F : Set (Sym2 V))) > dominationNumber G}
  have hne : {k : ℕ | ∃ F : Finset (Sym2 V), (∀ e ∈ F, e ∈ G.edgeSet) ∧ F.card = k ∧
      dominationNumber (G.deleteEdges (F : Set (Sym2 V))) > dominationNumber G}.Nonempty := by
    obtain ⟨F, hF, hgt⟩ := exists_edge_set_increases gamma_eq_six
    exact ⟨F.card, F, hF, rfl, hgt⟩
  obtain ⟨F, hF, hFcard, hgt⟩ := Nat.sInf_mem hne
  by_contra h
  push_neg at h
  have h4 : F.card ≤ 4 := by omega
  have h6 := four_edge F hF h4
  rw [h6, gamma_eq_six] at hgt
  exact lt_irrefl 6 hgt

/-- Teschner's conjecture is false. -/
theorem teschner_false : teschner_false_statement := by
  intro h
  have he : ∃ e, e ∈ G.edgeSet := ⟨eOf 0, eOf_mem 0⟩
  have hb := h G he
  have h5 : (5 : ℚ) ≤ (bondageNumber G : ℚ) := by exact_mod_cast bondage_ge_five
  have hΔ : (maxDegree G : ℚ) = 3 := by rw [maxDegree_three]; norm_num
  rw [hΔ] at hb
  linarith

end DsBatch.P09
