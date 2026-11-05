import DsBatch.P08.Statement

/-! Proofs for project P08, after arXiv 2609.28702.

Strategy (all in Mathlib terms, avoiding the paper's appeal to the
unpublished radius theorem of [BST94]):

* a nontrivial squco graph is connected: a square walk projects to a walk,
  while the complement of a disconnected graph is connected;
* consequently every vertex has a neighbour, so every vertex lies in a ball
  `B₂(x)` of radius two, and domination of closed neighbourhoods implies
  `B₂(x) ⊆ B₂(y)`;
* `N_{sq G}(x)` is the complement of `B₂(x)` in `G`, so `B₂(x) ⊆ B₂(y)` is
  equivalent to `N_{sq G}(y) ⊆ N_{sq G}(x)`;
* counting ordered pairs `(x,y)` with `x ≠ y` on which a closed or open
  neighbourhood inclusion holds, and comparing with the false dominating
  pairs of `sq G`, gives that every closed neighbourhood inclusion is in
  fact an open neighbourhood inclusion;
* a true and a false dominating pair cannot coexist (one forces adjacency,
  the other non-adjacency), which yields the main theorem; the corollary
  then follows because the closed neighbourhood of a simplicial vertex is a
  clique, so a neighbour is dominated by it. -/

namespace DsBatch.P08

open SimpleGraph

section Basic

variable {V : Type*} {G : SimpleGraph V}

/-! ### Elementary neighbourhood facts and the square -/

lemma mem_ball2 {x y : V} :
    y ∈ ball2 G x ↔ y = x ∨ G.Adj x y ∨ ∃ z, G.Adj x z ∧ G.Adj z y := Iff.rfl

lemma mem_closedNhd {x y : V} :
    y ∈ closedNhd G x ↔ y = x ∨ G.Adj x y := by
  rw [closedNhd, Set.mem_union, Set.mem_singleton_iff, mem_neighborSet]

/-- Vertices of `sq G` are exactly the vertices at distance at least three in
`G`: the open neighbourhood of `x` in `sq G` is the complement of `B₂(x)`. -/
lemma mem_neighborSet_sq {x y : V} : y ∈ (sq G).neighborSet x ↔ y ∉ ball2 G x := by
  rw [mem_neighborSet, sq, compl_adj]
  unfold square ball2
  simp only [ne_eq]
  constructor
  · rintro ⟨hne, hnot⟩ hb
    rcases hb with rfl | hb | hb
    · exact hne rfl
    · exact hnot ⟨hne, Or.inl hb⟩
    · exact hnot ⟨hne, Or.inr hb⟩
  · intro hb
    refine ⟨?_, ?_⟩
    · intro hxy
      exact hb (Or.inl hxy.symm)
    · intro h
      exact hb (Or.inr h.2)

lemma ball2_subset_of_dominatedBy {x y : V} (h : DominatedBy G x y) :
    ball2 G x ⊆ ball2 G y := by
  intro z hz
  rw [mem_ball2] at hz ⊢
  rcases hz with hzx | hxz | ⟨w, hxw, hwz⟩
  · rw [hzx]
    have hx : x ∈ closedNhd G y := h (by rw [mem_closedNhd]; exact Or.inl rfl)
    rw [mem_closedNhd] at hx
    rcases hx with hxy | hyx
    · exact Or.inl hxy
    · exact Or.inr (Or.inl hyx)
  · have hz' : z ∈ closedNhd G y := h (by rw [mem_closedNhd]; exact Or.inr hxz)
    rw [mem_closedNhd] at hz'
    rcases hz' with hyz | hyz
    · exact Or.inl hyz
    · exact Or.inr (Or.inl hyz)
  · have hw : w ∈ closedNhd G y := h (by rw [mem_closedNhd]; exact Or.inr hxw)
    rw [mem_closedNhd] at hw
    rcases hw with hwy | hyw
    · rw [hwy] at hwz; exact Or.inr (Or.inl hwz)
    · exact Or.inr (Or.inr ⟨w, hyw, hwz⟩)

lemma ball2_subset_of_neighborSet_subset {x y : V}
    (h : G.neighborSet x ⊆ G.neighborSet y) (hx : ∃ w, G.Adj x w) :
    ball2 G x ⊆ ball2 G y := by
  obtain ⟨w, hxw⟩ := hx
  have hyw : G.Adj y w := h ((mem_neighborSet G x w).mpr hxw)
  intro z hz
  rw [mem_ball2] at hz ⊢
  rcases hz with hzx | hxz | ⟨u, hxu, huz⟩
  · rw [hzx]
    exact Or.inr (Or.inr ⟨w, hyw, hxw.symm⟩)
  · exact Or.inr (Or.inl (h ((mem_neighborSet G x z).mpr hxz)))
  · exact Or.inr (Or.inr ⟨u, h ((mem_neighborSet G x u).mpr hxu), huz⟩)

lemma neighborSet_sq_subset_of_ball2_subset {x y : V}
    (h : ball2 G x ⊆ ball2 G y) :
    (sq G).neighborSet y ⊆ (sq G).neighborSet x := by
  intro z hz
  rw [mem_neighborSet_sq] at hz ⊢
  intro hzx
  exact hz (h hzx)

/-- In a graph with no isolated vertex, `N[x] ⊆ N[y]` forces `x ~ y`. -/
lemma adj_of_dominatedBy {x y : V} (h : DominatedBy G x y) (hxy : x ≠ y) :
    G.Adj x y := by
  have hx : x ∈ closedNhd G x := by rw [mem_closedNhd]; exact Or.inl rfl
  rcases mem_closedNhd.mp (h hx) with h' | h'
  · exact absurd h' hxy
  · exact h'.symm

/-- A false dominating pair consists of non-adjacent vertices. -/
lemma not_adj_of_neighborSet_subset {x y : V}
    (h : G.neighborSet x ⊆ G.neighborSet y ∨ G.neighborSet y ⊆ G.neighborSet x) :
    ¬ G.Adj x y := by
  intro hadj
  have hyx : y ∈ G.neighborSet x := (mem_neighborSet G x y).mpr hadj
  have hxy : x ∈ G.neighborSet y := (mem_neighborSet G y x).mpr hadj.symm
  rcases h with h | h
  · exact G.irrefl ((mem_neighborSet G y y).mp (h hyx))
  · exact G.irrefl ((mem_neighborSet G x x).mp (h hxy))

/-! ### Connectivity of nontrivial squco graphs -/

lemma reachable_of_adj {H : SimpleGraph V} {u v : V} (h : H.Adj u v) : H.Reachable u v :=
  ⟨Walk.cons h Walk.nil⟩

lemma reachable_of_square_adj {u v : V} (h : (square G).Adj u v) : G.Reachable u v := by
  obtain ⟨-, h⟩ := h
  rcases h with h | ⟨z, huz, hzv⟩
  · exact reachable_of_adj h
  · exact (reachable_of_adj huz).trans (reachable_of_adj hzv)

lemma reachable_of_square_reachable {u v : V} (h : (square G).Reachable u v) :
    G.Reachable u v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact ⟨Walk.nil⟩
  | cons hstep _ ih => exact (reachable_of_square_adj hstep).trans ih

lemma exists_not_reachable_of_not_preconnected (h : ¬ G.Preconnected) (x : V) :
    ∃ z, ¬ G.Reachable x z := by
  by_contra hc
  push_neg at hc
  exact h fun u v => (hc u).symm.trans (hc v)

lemma compl_adj_of_not_reachable {x y : V} (h : ¬ G.Reachable x y) : Gᶜ.Adj x y := by
  rw [compl_adj]
  refine ⟨?_, ?_⟩
  · intro hxy
    exact h (hxy ▸ Reachable.refl x)
  · intro hadj
    exact h (reachable_of_adj hadj)

lemma preconnected_compl_of_not_preconnected (h : ¬ G.Preconnected) : Gᶜ.Preconnected := by
  intro a b
  by_cases hab : a = b
  · subst hab
    exact ⟨Walk.nil⟩
  by_cases hR : G.Reachable a b
  · obtain ⟨z, hz⟩ := exists_not_reachable_of_not_preconnected h a
    have h1 : (Gᶜ).Adj a z := compl_adj_of_not_reachable hz
    have h2 : (Gᶜ).Adj b z := compl_adj_of_not_reachable (fun h' => hz (hR.trans h'))
    exact (reachable_of_adj h1).trans (reachable_of_adj h2).symm
  · exact reachable_of_adj (compl_adj_of_not_reachable hR)

lemma preconnected_of_squco (h : IsSquareComplementary G) : G.Preconnected := by
  by_contra hnc
  obtain ⟨e⟩ := h
  have hcomp : Gᶜ.Preconnected := preconnected_compl_of_not_preconnected hnc
  have hsq : (square G).Preconnected := e.preconnected_iff.mpr hcomp
  exact hnc fun u v => reachable_of_square_reachable (hsq u v)

lemma exists_adj_of_preconnected [Nontrivial V] (h : G.Preconnected) (x : V) :
    ∃ w, G.Adj x w := by
  have hx : x ∈ G.support := by
    rw [Preconnected.support_eq_univ h]
    trivial
  exact (mem_support G).mp hx

lemma compl_compl_eq (G : SimpleGraph V) : Gᶜᶜ = G := by
  ext x y
  rw [compl_adj, compl_adj]
  constructor
  · rintro ⟨hne, hnot⟩
    by_contra h
    exact hnot ⟨hne, h⟩
  · intro h
    exact ⟨h.ne, fun hc => hc.2 h⟩

def complIso {G H : SimpleGraph V} (e : G ≃g H) : Gᶜ ≃g Hᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro x y
    rw [compl_adj, compl_adj]
    constructor
    · rintro ⟨hne, hna⟩
      exact ⟨fun heq => hne (by rw [heq]),
        fun hadj => hna (e.map_adj_iff.mpr hadj)⟩
    · rintro ⟨hne, hna⟩
      exact ⟨fun heq => hne (Equiv.injective e.toEquiv heq),
        fun hadj => hna (e.map_adj_iff.mp hadj)⟩

/-- A squco graph is isomorphic to the complement of its square. -/
lemma sq_iso_of_squco (h : IsSquareComplementary G) : Nonempty (sq G ≃g G) := by
  obtain ⟨e⟩ := h
  refine ⟨{ toEquiv := e.toEquiv, map_rel_iff' := ?_ }⟩
  intro x y
  show G.Adj (e x) (e y) ↔ (square G)ᶜ.Adj x y
  rw [compl_adj]
  have hiff : Gᶜ.Adj (e x) (e y) ↔ (square G).Adj x y := e.map_adj_iff
  rw [compl_adj] at hiff
  constructor
  · intro hadj
    refine ⟨fun hxy => hadj.ne (by rw [hxy]), fun hsq => ?_⟩
    exact (hiff.mpr hsq).2 hadj
  · rintro ⟨hne, hna⟩
    by_contra hcon
    exact hna (hiff.mp ⟨fun heq => hne (Equiv.injective e.toEquiv heq), hcon⟩)

end Basic

/-! ### Counting dominating pairs -/

section Counting

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Ordered pairs of distinct vertices on which a closed *or* an open
neighbourhood inclusion holds (in either direction). -/
noncomputable def domPairs (G : SimpleGraph V) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun p =>
    p.1 ≠ p.2 ∧
      (DominatedBy G p.1 p.2 ∨ DominatedBy G p.2 p.1 ∨
        G.neighborSet p.1 ⊆ G.neighborSet p.2 ∨
        G.neighborSet p.2 ⊆ G.neighborSet p.1))

/-- Ordered pairs of distinct vertices on which an open neighbourhood inclusion
holds (in either direction), the "false dominating pairs". -/
noncomputable def falsePairs (G : SimpleGraph V) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun p =>
    p.1 ≠ p.2 ∧
      (G.neighborSet p.1 ⊆ G.neighborSet p.2 ∨
        G.neighborSet p.2 ⊆ G.neighborSet p.1))

lemma mem_domPairs {p : V × V} :
    p ∈ domPairs G ↔ p.1 ≠ p.2 ∧
      (DominatedBy G p.1 p.2 ∨ DominatedBy G p.2 p.1 ∨
        G.neighborSet p.1 ⊆ G.neighborSet p.2 ∨
        G.neighborSet p.2 ⊆ G.neighborSet p.1) := by
  classical
  simp [domPairs]

lemma mem_falsePairs {p : V × V} :
    p ∈ falsePairs G ↔ p.1 ≠ p.2 ∧
      (G.neighborSet p.1 ⊆ G.neighborSet p.2 ∨
        G.neighborSet p.2 ⊆ G.neighborSet p.1) := by
  classical
  simp [falsePairs]

lemma falsePairs_subset_domPairs : falsePairs G ⊆ domPairs G := by
  intro p hp
  rw [mem_falsePairs] at hp
  rw [mem_domPairs]
  exact ⟨hp.1, Or.inr (Or.inr hp.2)⟩

/-- The paper's key observation: a dominating pair of `G` becomes a false
dominating pair of `sq G`, with the two vertices swapped. -/
lemma swap_mem_falsePairs_sq (hneigh : ∀ x, ∃ w, G.Adj x w) {p : V × V}
    (hp : p ∈ domPairs G) : (p.2, p.1) ∈ falsePairs (sq G) := by
  rw [mem_domPairs] at hp
  rw [mem_falsePairs]
  obtain ⟨hne, h | h | h | h⟩ := hp
  · exact ⟨hne.symm,
      Or.inl (neighborSet_sq_subset_of_ball2_subset (ball2_subset_of_dominatedBy h))⟩
  · exact ⟨hne.symm,
      Or.inr (neighborSet_sq_subset_of_ball2_subset (ball2_subset_of_dominatedBy h))⟩
  · exact ⟨hne.symm,
      Or.inl (neighborSet_sq_subset_of_ball2_subset
        (ball2_subset_of_neighborSet_subset h (hneigh p.1)))⟩
  · exact ⟨hne.symm,
      Or.inr (neighborSet_sq_subset_of_ball2_subset
        (ball2_subset_of_neighborSet_subset h (hneigh p.2)))⟩

lemma card_domPairs_le_falsePairs_sq (hneigh : ∀ x, ∃ w, G.Adj x w) :
    (domPairs G).card ≤ (falsePairs (sq G)).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun p : V × V => (p.2, p.1)) ?_ ?_
  · intro p hp
    exact swap_mem_falsePairs_sq hneigh hp
  · intro p _ q _ hpq
    cases p with
    | mk a b =>
      cases q with
      | mk c d =>
        simp only [Prod.mk.injEq] at hpq ⊢
        exact ⟨hpq.2, hpq.1⟩

lemma mem_falsePairs_map_iff {H : SimpleGraph V} (e : G ≃g H) {p : V × V} :
    (e p.1, e p.2) ∈ falsePairs H ↔ p ∈ falsePairs G := by
  rw [mem_falsePairs, mem_falsePairs]
  constructor
  · rintro ⟨hne, h | h⟩
    · refine ⟨fun hpq => hne (by rw [hpq]), Or.inl ?_⟩
      intro z hz
      exact (Iso.apply_mem_neighborSet_iff e).mp (h ((Iso.apply_mem_neighborSet_iff e).mpr hz))
    · refine ⟨fun hpq => hne (by rw [hpq]), Or.inr ?_⟩
      intro z hz
      exact (Iso.apply_mem_neighborSet_iff e).mp (h ((Iso.apply_mem_neighborSet_iff e).mpr hz))
  · rintro ⟨hne, h | h⟩
    · refine ⟨fun hpq => hne (Equiv.injective e.toEquiv hpq), Or.inl ?_⟩
      intro z hz
      obtain ⟨w, hw⟩ := e.toEquiv.surjective z
      rw [← hw] at hz ⊢
      exact (Iso.apply_mem_neighborSet_iff e).mpr (h ((Iso.apply_mem_neighborSet_iff e).mp hz))
    · refine ⟨fun hpq => hne (Equiv.injective e.toEquiv hpq), Or.inr ?_⟩
      intro z hz
      obtain ⟨w, hw⟩ := e.toEquiv.surjective z
      rw [← hw] at hz ⊢
      exact (Iso.apply_mem_neighborSet_iff e).mpr (h ((Iso.apply_mem_neighborSet_iff e).mp hz))

lemma falsePairs_card_eq_of_iso {H : SimpleGraph V} (e : G ≃g H) :
    (falsePairs G).card = (falsePairs H).card := by
  classical
  apply le_antisymm
  · refine Finset.card_le_card_of_injOn (fun p : V × V => (e p.1, e p.2)) ?_ ?_
    · intro p hp
      exact (mem_falsePairs_map_iff e).mpr hp
    · intro p _ q _ hpq
      exact Prod.ext (Equiv.injective e.toEquiv (congrArg Prod.fst hpq))
        (Equiv.injective e.toEquiv (congrArg Prod.snd hpq))
  · refine Finset.card_le_card_of_injOn (fun p : V × V => (e.symm p.1, e.symm p.2)) ?_ ?_
    · intro p hp
      exact (mem_falsePairs_map_iff (G := H) (H := G) e.symm).mpr hp
    · intro p _ q _ hpq
      exact Prod.ext (Equiv.injective e.symm.toEquiv (congrArg Prod.fst hpq))
        (Equiv.injective e.symm.toEquiv (congrArg Prod.snd hpq))

end Counting

/-! ### The two targets -/

theorem no_comparable_closed_neighborhoods :
    no_comparable_closed_neighborhoods_statement := by
  intro V instV G hsquco hnt x y hxy hdom
  haveI : Nontrivial V := by
    apply Fintype.one_lt_card_iff_nontrivial.mp
    have h2 : 2 ≤ Fintype.card V := hnt
    omega
  have hconn : G.Preconnected := preconnected_of_squco hsquco
  have hneigh : ∀ x, ∃ w, G.Adj x w := fun x => exists_adj_of_preconnected hconn x
  obtain ⟨e⟩ := sq_iso_of_squco hsquco
  have hcard : (domPairs G).card ≤ (falsePairs G).card := by
    have h1 := card_domPairs_le_falsePairs_sq hneigh
    have h2 : (falsePairs (sq G)).card = (falsePairs G).card :=
      falsePairs_card_eq_of_iso e
    rwa [h2] at h1
  have heq : falsePairs G = domPairs G :=
    Finset.eq_of_subset_of_card_le falsePairs_subset_domPairs hcard
  have hp : (x, y) ∈ domPairs G := by
    rw [mem_domPairs]
    refine ⟨hxy, ?_⟩
    rcases hdom with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  rw [← heq] at hp
  rw [mem_falsePairs] at hp
  obtain ⟨-, hsub⟩ := hp
  have hnotadj : ¬ G.Adj x y := not_adj_of_neighborSet_subset hsub
  rcases hdom with h | h
  · exact hnotadj (adj_of_dominatedBy h hxy)
  · exact hnotadj (adj_of_dominatedBy h hxy.symm).symm

theorem no_simplicial_vertex :
    no_simplicial_vertex_statement := by
  intro V instV G hsquco hnt x hsimp
  haveI : Nontrivial V := by
    apply Fintype.one_lt_card_iff_nontrivial.mp
    have h2 : 2 ≤ Fintype.card V := hnt
    omega
  have hconn : G.Preconnected := preconnected_of_squco hsquco
  obtain ⟨y, hxy⟩ := exists_adj_of_preconnected hconn x
  have hdom : DominatedBy G x y := by
    intro z hz
    rw [mem_closedNhd] at hz ⊢
    rcases hz with hzx | hxz
    · exact Or.inr (hzx ▸ hxy.symm)
    · by_cases hzy : z = y
      · exact Or.inl hzy
      · have hzN : z ∈ closedNhd G x := by rw [mem_closedNhd]; exact Or.inr hxz
        have hyN : y ∈ closedNhd G x := by rw [mem_closedNhd]; exact Or.inr hxy
        exact Or.inr ((hsimp hzN hyN hzy).symm)
  exact no_comparable_closed_neighborhoods G hsquco hnt x y hxy.ne (Or.inl hdom)

end DsBatch.P08
