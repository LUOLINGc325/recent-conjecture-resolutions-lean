import DsBatch.P11.Statement

/-! Proofs for project P11. Target stubs start as `:= by sorry` and are
    replaced by proofs; this file is not frozen.

Refutation of Iradmusa's conjecture with the graph `G` and the 2-list assignment `L` of P02
(Noel, arXiv:2609.23291):
* `λ_2 ≤ 9`, because `L` admits no partial proper colouring of more than nine vertices;
* `λ_3 = 14`, because `G` is 3-choosable, so every 3-list assignment colours all 14 vertices.
Then `λ_2 / 2 ≤ 9/2 < 14/3 = λ_3 / 3`, contradicting `conjecture` at `χ_ℓ = 3`, `r = 2`, `s = 3`. -/

namespace DsBatch.P11

open MathlibExt.GraphTheory.PartialListColoringWanted

/-! ### Supremum and infimum bounds -/

/-- The set whose supremum is `lambdaMax G L` is nonempty: the empty set is always colourable. -/
private lemma lambdaMax_set_nonempty (L : DsBatch.P02.V → Finset ℕ) :
    ({k : ℕ | ∃ S : Finset DsBatch.P02.V, ∃ f : DsBatch.P02.V → ℕ,
      S.card = k ∧ IsListColoring DsBatch.P02.G L f S}).Nonempty :=
  ⟨0, ∅, fun _ => 0, rfl, by simp [IsListColoring]⟩

/-- `λ_L` never exceeds the number of vertices. -/
private lemma lambdaMax_le_card (L : DsBatch.P02.V → Finset ℕ) :
    lambdaMax DsBatch.P02.G L ≤ Fintype.card DsBatch.P02.V := by
  apply csSup_le (lambdaMax_set_nonempty L)
  rintro k ⟨S, f, rfl, _⟩
  exact Finset.card_le_univ S

/-- The 2-list assignment `L` of the paper allows at most nine coloured vertices, so
`λ_L ≤ 9`. -/
private lemma lambdaMax_P02L_le_nine :
    lambdaMax DsBatch.P02.G DsBatch.P02.L ≤ 9 := by
  apply csSup_le (lambdaMax_set_nonempty DsBatch.P02.L)
  rintro k ⟨S, f, rfl, hcol⟩
  exact DsBatch.P02.nine_bound S f ⟨hcol.1, hcol.2⟩

/-- Every 3-list assignment admits a full proper colouring of the 14-vertex graph, hence
`λ_L = 14` for every 3-list assignment `L`. -/
private lemma lambdaMax_eq_fourteen (L : DsBatch.P02.V → Finset ℕ)
    (hL : ∀ v, (L v).card = 3) :
    lambdaMax DsBatch.P02.G L = 14 := by
  have hcard : Fintype.card DsBatch.P02.V = 14 := by decide
  have hbdd : BddAbove {k : ℕ | ∃ S : Finset DsBatch.P02.V, ∃ f : DsBatch.P02.V → ℕ,
      S.card = k ∧ IsListColoring DsBatch.P02.G L f S} := by
    refine ⟨14, ?_⟩
    rintro k ⟨S, f, rfl, _⟩
    have := Finset.card_le_univ S
    omega
  have hle : lambdaMax DsBatch.P02.G L ≤ 14 := by
    apply csSup_le (lambdaMax_set_nonempty L)
    rintro k ⟨S, f, rfl, _⟩
    have := Finset.card_le_univ S
    omega
  have hmem : 14 ∈ {k : ℕ | ∃ S : Finset DsBatch.P02.V, ∃ f : DsBatch.P02.V → ℕ,
      S.card = k ∧ IsListColoring DsBatch.P02.G L f S} := by
    obtain ⟨c, hc1, hc2⟩ := DsBatch.P02.choosable_three L hL
    refine ⟨Finset.univ, c, ?_, ?_⟩
    · rw [Finset.card_univ]; exact hcard
    · refine ⟨?_, ?_⟩
      · intro v _; exact hc1 v
      · intro u _ v _ huv; exact hc2 u v huv
  have hge : 14 ≤ lambdaMax DsBatch.P02.G L := le_csSup hbdd hmem
  omega

/-- `λ_2 ≤ 9`: the paper's 2-list assignment shows that the minimum over 2-list assignments
is at most nine. -/
private lemma lambdaMin_two_le_nine : lambdaMin DsBatch.P02.G 2 ≤ 9 := by
  have hmem : lambdaMax DsBatch.P02.G DsBatch.P02.L ∈
      {k : ℕ | ∃ L : DsBatch.P02.V → Finset ℕ,
        (∀ v, (L v).card = 2) ∧ lambdaMax DsBatch.P02.G L = k} :=
    ⟨DsBatch.P02.L, DsBatch.P02.L_two, rfl⟩
  exact (Nat.sInf_le hmem).trans lambdaMax_P02L_le_nine

/-- `14 ≤ λ_3`: every 3-list assignment colours all fourteen vertices. -/
private lemma fourteen_le_lambdaMin_three : 14 ≤ lambdaMin DsBatch.P02.G 3 := by
  apply le_csInf
  · refine ⟨lambdaMax DsBatch.P02.G (fun _ => Finset.range 3),
      fun _ => Finset.range 3, ?_, rfl⟩
    intro v; simp
  · rintro k ⟨L, hL, rfl⟩
    rw [lambdaMax_eq_fourteen L hL]

/-! ### The refutation -/

/-- Iradmusa's partial list coloring conjecture is false: Noel's 14-vertex graph has
`λ_2 ≤ 9 < 14 ≤ λ_3`, so `λ_2 / 2 < λ_3 / 3`. -/
theorem conjecture_refuted : conjecture_refuted_statement := by
  intro hconj
  have hchoice := p02_isChoiceNumber
  have h2 := lambdaMin_two_le_nine
  have h3 := fourteen_le_lambdaMin_three
  have h := hconj DsBatch.P02.V DsBatch.P02.G 3 2 3 hchoice
    (by norm_num) (by norm_num) (by norm_num)
  have h2' : ((lambdaMin DsBatch.P02.G 2 : ℕ) : ℚ) / 2 ≤ 9 / 2 := by
    have : ((lambdaMin DsBatch.P02.G 2 : ℕ) : ℚ) ≤ 9 := by exact_mod_cast h2
    linarith
  have h3' : (14 : ℚ) / 3 ≤ ((lambdaMin DsBatch.P02.G 3 : ℕ) : ℚ) / 3 := by
    have : (14 : ℚ) ≤ ((lambdaMin DsBatch.P02.G 3 : ℕ) : ℚ) := by exact_mod_cast h3
    linarith
  linarith

end DsBatch.P11
