import DsBatch.P01.Statement

/-! Proofs for project P01.

The paper's verification argument is followed directly:

* `G` is connected: every vertex reaches vertex `1` (index `0`) by a short explicit walk.
* `G` is not bipartite: the odd cycle `1,2,4,5,10,1` cannot be 2-coloured
  (`five_cycle_not_two_colorable`).
* `G` is vertex-determining: the ten open neighbourhoods are pairwise distinct.
* `(α, β) = ((1 6), (2 3))` is a nontrivial two-fold automorphism (checked by `decide`).
* There is no odd `k` with both `C_k` and `C_{2k}`: any cycle has length at most `10`, so
  `k ∈ {3, 5}`; there is no triangle (`no_cycle_3`), and there is no 10-cycle because the
  leaf `9` (index `8`) has the unique neighbour `7` (index `6`) and so cannot lie on a
  cycle (`no_cycle_10`).
-/

namespace DsBatch.P01

/-- The graph is connected: every vertex reaches vertex `1` (index `0`). -/
theorem reachable_zero : ∀ u : V, G.Reachable u 0 := by
  intro u
  fin_cases u
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact (show G.Adj 1 0 by decide).reachable
  · exact ((show G.Adj 2 3 by decide).reachable.trans
          ((show G.Adj 3 1 by decide).reachable.trans
          ((show G.Adj 1 0 by decide).reachable)))
  · exact ((show G.Adj 3 1 by decide).reachable.trans
          ((show G.Adj 1 0 by decide).reachable))
  · exact ((show G.Adj 4 3 by decide).reachable.trans
          ((show G.Adj 3 1 by decide).reachable.trans
          ((show G.Adj 1 0 by decide).reachable)))
  · exact ((show G.Adj 5 2 by decide).reachable.trans
          ((show G.Adj 2 3 by decide).reachable.trans
          ((show G.Adj 3 1 by decide).reachable.trans
          ((show G.Adj 1 0 by decide).reachable))))
  · exact ((show G.Adj 6 4 by decide).reachable.trans
          ((show G.Adj 4 3 by decide).reachable.trans
          ((show G.Adj 3 1 by decide).reachable.trans
          ((show G.Adj 1 0 by decide).reachable))))
  · exact ((show G.Adj 7 9 by decide).reachable.trans
          ((show G.Adj 9 0 by decide).reachable))
  · exact ((show G.Adj 8 6 by decide).reachable.trans
          ((show G.Adj 6 4 by decide).reachable.trans
          ((show G.Adj 4 3 by decide).reachable.trans
          ((show G.Adj 3 1 by decide).reachable.trans
          ((show G.Adj 1 0 by decide).reachable)))))
  · exact (show G.Adj 9 0 by decide).reachable

/-- The graph is connected. -/
theorem connected_G : G.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, fun w => (reachable_zero w).symm⟩

/-- No two vertices have the same open neighbourhood. -/
theorem vertex_determining_G : VertexDetermining G := by
  intro u v h
  by_contra hne
  have key : ∀ u v : V, u ≠ v → ¬ (∀ w : V, G.Adj u w ↔ G.Adj v w) := by decide
  exact key u v hne (fun w => by
    have hw := Set.ext_iff.mp h w
    simpa [SimpleGraph.mem_neighborSet] using hw)

/-- In `Fin 2`, a 5-cycle cannot be properly 2-coloured. -/
theorem five_cycle_not_two_colorable :
    ∀ a b c d e : Fin 2, a ≠ b → b ≠ c → c ≠ d → d ≠ e → e ≠ a → False := by
  intro a b c d e h1 h2 h3 h4 h5
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> simp_all

/-- The graph is not bipartite (the odd cycle `1,2,4,5,10,1`). -/
theorem not_bipartite_G : ¬ G.IsBipartite := by
  rintro ⟨C⟩
  exact five_cycle_not_two_colorable (C 0) (C 1) (C 3) (C 4) (C 9)
    (C.valid (show G.Adj 0 1 by decide))
    (C.valid (show G.Adj 1 3 by decide))
    (C.valid (show G.Adj 3 4 by decide))
    (C.valid (show G.Adj 4 9 by decide))
    (C.valid (show G.Adj 9 0 by decide))

/-- There is no triangle. -/
theorem no_triangle : ∀ a b c : V, G.Adj a b → G.Adj b c → G.Adj c a → False := by decide

/-- The graph has no 3-cycle. -/
theorem no_cycle_3 : ¬ HasCycleOfLength G 3 := by
  unfold HasCycleOfLength
  rintro ⟨-, f, hf_inj, hf_adj⟩
  have h01 : G.Adj (f 0) (f 1) := hf_adj 0 1 (by decide)
  have h12 : G.Adj (f 1) (f 2) := hf_adj 1 2 (by decide)
  have h20 : G.Adj (f 2) (f 0) := hf_adj 2 0 (by decide)
  exact no_triangle (f 0) (f 1) (f 2) h01 h12 h20

/-- Vertex `9` (index `8`) has the unique neighbour `7` (index `6`). -/
theorem unique_neighbor_eight : ∀ x : V, G.Adj x 8 → x = 6 := by decide

/-- In the cycle graph on `Fin 10`, `i` is adjacent to `i - 1`. -/
theorem cycleGraph_ten_adj_sub_one (i : Fin 10) :
    (SimpleGraph.cycleGraph 10).Adj i (i - 1) := by
  rw [SimpleGraph.cycleGraph_adj']
  left
  have h : i - (i - 1) = (1 : Fin 10) := by abel
  rw [h]
  decide

/-- In the cycle graph on `Fin 10`, `i` is adjacent to `i + 1`. -/
theorem cycleGraph_ten_adj_add_one (i : Fin 10) :
    (SimpleGraph.cycleGraph 10).Adj i (i + 1) := by
  rw [SimpleGraph.cycleGraph_adj']
  right
  have h : (i + 1) - i = (1 : Fin 10) := by abel
  rw [h]
  decide

/-- In `Fin 10` the two cycle-neighbours `i - 1` and `i + 1` are distinct. -/
theorem fin_sub_one_ne_add_one (i : Fin 10) : i - 1 ≠ i + 1 := by
  fin_cases i <;> decide

/-- The graph has no 10-cycle: a 10-cycle would use the leaf `9` (index `8`), whose two
cycle-neighbours would both have to be its unique graph-neighbour `7` (index `6`). -/
theorem no_cycle_10 : ¬ HasCycleOfLength G 10 := by
  unfold HasCycleOfLength
  rintro ⟨-, f, hf_inj, hf_adj⟩
  obtain ⟨i, hi⟩ := Finite.surjective_of_injective hf_inj (8 : V)
  have hprev : G.Adj (f (i - 1)) 8 := by
    have h := hf_adj i (i - 1) (cycleGraph_ten_adj_sub_one i)
    rw [hi] at h
    exact (G.adj_comm _ _).mpr h
  have hnext : G.Adj (f (i + 1)) 8 := by
    have h := hf_adj i (i + 1) (cycleGraph_ten_adj_add_one i)
    rw [hi] at h
    exact (G.adj_comm _ _).mpr h
  have h1 : f (i - 1) = 6 := unique_neighbor_eight _ hprev
  have h2 : f (i + 1) = 6 := unique_neighbor_eight _ hnext
  exact fin_sub_one_ne_add_one i (hf_inj (h1.trans h2.symm))

/-- The graph contains neither `C_k` nor `C_{2k}` for any odd `k`. -/
theorem no_odd_double_cycle : ¬ ContainsOddDoubleCycle G := by
  unfold ContainsOddDoubleCycle
  rintro ⟨k, hkodd, hk, h2k⟩
  obtain ⟨hk3, f, hf_inj, hf_adj⟩ := hk
  obtain ⟨h2k3, g, hg_inj, hg_adj⟩ := h2k
  have hk10 : k ≤ 10 := by
    have h := Fintype.card_le_of_injective f hf_inj
    simpa using h
  have h2k10 : 2 * k ≤ 10 := by
    have h := Fintype.card_le_of_injective g hg_inj
    simpa using h
  obtain ⟨m, rfl⟩ := hkodd
  have hm1 : 1 ≤ m := by omega
  have hm2 : m ≤ 2 := by omega
  interval_cases m
  · exact no_cycle_3 ⟨hk3, f, hf_inj, hf_adj⟩
  · exact no_cycle_10 ⟨h2k3, g, hg_inj, hg_adj⟩

/-- The paper's main theorem (Theorem 1). -/
theorem counterexample : counterexample_statement := by
  unfold counterexample_statement
  refine ⟨connected_G, vertex_determining_G, ⟨?_, ?_⟩, no_odd_double_cycle⟩
  · exact ⟨alpha, beta, by decide, by unfold IsTwoFoldAutomorphism; decide⟩
  · rintro (hnc | hb)
    · exact hnc connected_G
    · exact not_bipartite_G hb

/-- Mizzi's conjecture on unstable graphs is false. -/
theorem mizzi_conjecture_false : mizzi_conjecture_false_statement := by
  unfold mizzi_conjecture_false_statement MizziConjecture
  intro h
  exact no_odd_double_cycle (h V G ⟨⟨alpha, beta, by decide,
    by unfold IsTwoFoldAutomorphism; decide⟩, by
      rintro (hnc | hb)
      · exact hnc connected_G
      · exact not_bipartite_G hb⟩)

end DsBatch.P01
