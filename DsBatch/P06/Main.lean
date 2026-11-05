import DsBatch.P06.Statement

/-! Proofs for project P06: the explicit graph `H` of arXiv 2607.23462.

* `Cubic`, `ClawFree`, `DiamondFree` are finite kernel computations (`decide`) on the
  18 vertices.
* The strong 7-edge-colouring is the explicit colour table of Appendix A, checked on
  all vertex quadruples.
* The absence of a strong 6-edge-colouring follows the paper's forcing argument
  (Proposition 3.4): the six edges `K = {x,u,v,w,y,z}` of the gadget form a `K₆` in
  `L(Q)²`, so they exhaust the six colours; then `r, s, t, q` are forced in turn,
  `m, n` split the two remaining colours, and `p` has no colour left. -/

set_option maxHeartbeats 4000000

namespace DsBatch.P06

open V

/-! ## The explicit strong 7-edge-colouring (Appendix A) -/

/-- The edge colouring of `H` given in Appendix A.  Within each copy of `Q` the colours
are, with `x,u,v,w,y,z,r,s,t,q,m,n,p` as in Section 3:
`x↦1, u↦2, v↦3, w↦6, y↦4, z↦5, r↦7, s↦3, t↦1, q↦2, m↦4, n↦5, p↦6`
for `Q₁`, and the same except `m↦5, n↦4, p↦7` for `Q₂`; the bridge `a₂⁽¹⁾a₂⁽²⁾`
receives colour `3`.  Colours are represented by `Fin 7` values `1,…,6,0` in order,
so the literal `7` is `0`.  All other pairs receive the dummy colour `0`. -/
def col : V → V → Fin 7
  -- first copy Q₁
  | .a0, .b0 | .b0, .a0 => 1            -- x
  | .b0, .b1 | .b1, .b0 => 2            -- u
  | .b0, .b2 | .b2, .b0 => 3            -- v
  | .b1, .b2 | .b2, .b1 => 6            -- w
  | .b1, .c1 | .c1, .b1 => 4            -- y
  | .b2, .c2 | .c2, .b2 => 5            -- z
  | .c1, .c2 | .c2, .c1 => 0            -- r  (colour 7)
  | .c0, .c1 | .c1, .c0 => 3            -- s
  | .c0, .c2 | .c2, .c0 => 1            -- t
  | .a1, .c0 | .c0, .a1 => 2            -- q
  | .a0, .a1 | .a1, .a0 => 4            -- m
  | .a0, .a2 | .a2, .a0 => 5            -- n
  | .a1, .a2 | .a2, .a1 => 6            -- p
  -- second copy Q₂
  | .a0', .b0' | .b0', .a0' => 1
  | .b0', .b1' | .b1', .b0' => 2
  | .b0', .b2' | .b2', .b0' => 3
  | .b1', .b2' | .b2', .b1' => 6
  | .b1', .c1' | .c1', .b1' => 4
  | .b2', .c2' | .c2', .b2' => 5
  | .c1', .c2' | .c2', .c1' => 0
  | .c0', .c1' | .c1', .c0' => 3
  | .c0', .c2' | .c2', .c0' => 1
  | .a1', .c0' | .c0', .a1' => 2
  | .a0', .a1' | .a1', .a0' => 5      -- m'
  | .a0', .a2' | .a2', .a0' => 4      -- n'
  | .a1', .a2' | .a2', .a1' => 0      -- p' (colour 7)
  -- the bridge
  | .a2, .a2' | .a2', .a2 => 3
  | _, _ => 0

lemma col_symm : ∀ u v, col u v = col v u := by decide

lemma col_strong : ∀ u v x y, EdgeConflict H u v x y → col u v ≠ col x y := by
  unfold EdgeConflict
  decide

/-! ## The forcing argument against six colours -/

/-- The six edges `K = {x,u,v,w,y,z}` of the gadget, indexed as in the paper's
availability table: `x = a₀b₀`, `u = b₀b₁`, `v = b₀b₂`, `w = b₁b₂`, `y = b₁c₁`,
`z = b₂c₂`. -/
def base : Fin 6 → V × V
  | 0 => (a0, b0)   -- x
  | 1 => (b0, b1)   -- u
  | 2 => (b0, b2)   -- v
  | 3 => (b1, b2)   -- w
  | 4 => (b1, c1)   -- y
  | 5 => (b2, c2)   -- z

/-- `r = c₁c₂`. -/
def eR : V × V := (c1, c2)

/-- `s = c₀c₁`. -/
def eS : V × V := (c0, c1)

/-- `t = c₀c₂`. -/
def eT : V × V := (c0, c2)

/-- `q = a₁c₀`. -/
def eQ : V × V := (a1, c0)

/-- `m = a₀a₁`. -/
def eM : V × V := (a0, a1)

/-- `n = a₀a₂`. -/
def eN : V × V := (a0, a2)

/-- `p = a₁a₂`. -/
def eP : V × V := (a1, a2)

/-- Lemma 3.2: `K = {x,u,v,w,y,z}` is a `K₆` in `L(Q)²`, i.e. its edges are
pairwise in conflict. -/
lemma clique_conflict : ∀ i j : Fin 6, i ≠ j →
    EdgeConflict H (base i).1 (base i).2 (base j).1 (base j).2 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> (unfold EdgeConflict base; decide)

/-- Proposition 3.4: `Q`, hence `H`, has no strong 6-edge-colouring. -/
lemma not_six : ¬ StrongEdgeColoring H 6 := by
  rintro ⟨c, hsym, hstr⟩
  -- `d i` is the colour of the `i`-th clique edge.
  let d : Fin 6 → Fin 6 := fun i => c (base i).1 (base i).2
  have hinj : Function.Injective d := by
    intro i j hij
    by_contra hne
    exact hstr (base i).1 (base i).2 (base j).1 (base j).2 (clique_conflict i j hne) hij
  -- The six clique colours are all distinct, so they use all six colours.
  have hsurj : Function.Surjective d := Finite.surjective_of_injective hinj
  -- An edge conflicting with five of the clique edges has the sixth colour.
  have forced : ∀ (e : V × V) (k : Fin 6),
      (∀ i, i ≠ k → c e.1 e.2 ≠ d i) → c e.1 e.2 = d k := by
    intro e k hne
    obtain ⟨j, hj⟩ := hsurj (c e.1 e.2)
    by_cases hjk : j = k
    · subst hjk; exact hj.symm
    · exact absurd hj.symm (hne j hjk)
  -- The conflict facts of the availability table that the forcing chain uses.
  have hS1 : c eS.1 eS.2 ≠ c (base 1).1 (base 1).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eS base; decide)
  have hS3 : c eS.1 eS.2 ≠ c (base 3).1 (base 3).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eS base; decide)
  have hS4 : c eS.1 eS.2 ≠ c (base 4).1 (base 4).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eS base; decide)
  have hS5 : c eS.1 eS.2 ≠ c (base 5).1 (base 5).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eS base; decide)
  have hT2 : c eT.1 eT.2 ≠ c (base 2).1 (base 2).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eT base; decide)
  have hT3 : c eT.1 eT.2 ≠ c (base 3).1 (base 3).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eT base; decide)
  have hT4 : c eT.1 eT.2 ≠ c (base 4).1 (base 4).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eT base; decide)
  have hT5 : c eT.1 eT.2 ≠ c (base 5).1 (base 5).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eT base; decide)
  have hQ0 : c eQ.1 eQ.2 ≠ c (base 0).1 (base 0).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eQ base; decide)
  have hQ4 : c eQ.1 eQ.2 ≠ c (base 4).1 (base 4).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eQ base; decide)
  have hQ5 : c eQ.1 eQ.2 ≠ c (base 5).1 (base 5).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eQ base; decide)
  have hM0 : c eM.1 eM.2 ≠ c (base 0).1 (base 0).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eM base; decide)
  have hM1 : c eM.1 eM.2 ≠ c (base 1).1 (base 1).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eM base; decide)
  have hM2 : c eM.1 eM.2 ≠ c (base 2).1 (base 2).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eM base; decide)
  have hN0 : c eN.1 eN.2 ≠ c (base 0).1 (base 0).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eN base; decide)
  have hN1 : c eN.1 eN.2 ≠ c (base 1).1 (base 1).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eN base; decide)
  have hN2 : c eN.1 eN.2 ≠ c (base 2).1 (base 2).2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eN base; decide)
  -- Step 1: `r` has the single available colour `x`.
  have hr : c eR.1 eR.2 = d 0 := by
    apply forced eR 0
    intro i hi
    fin_cases i
    · exact absurd rfl hi
    all_goals exact hstr _ _ _ _ (by unfold EdgeConflict eR base; decide)
  -- Step 1: `s` conflicts with `r`, so it gets `v`; `t` conflicts with `r`, so it gets `u`.
  have hs : c eS.1 eS.2 = d 2 := by
    apply forced eS 2
    intro i hi
    fin_cases i
    · intro h
      exact hstr _ _ _ _ (by unfold EdgeConflict eS eR; decide) (h.trans hr.symm)
    · exact hS1
    · exact absurd rfl hi
    · exact hS3
    · exact hS4
    · exact hS5
  have ht : c eT.1 eT.2 = d 1 := by
    apply forced eT 1
    intro i hi
    fin_cases i
    · intro h
      exact hstr _ _ _ _ (by unfold EdgeConflict eT eR; decide) (h.trans hr.symm)
    · exact absurd rfl hi
    · exact hT2
    · exact hT3
    · exact hT4
    · exact hT5
  -- Step 2: `q` conflicts with `s` and `t`, so it gets `w`.
  have hq : c eQ.1 eQ.2 = d 3 := by
    apply forced eQ 3
    intro i hi
    fin_cases i
    · exact hQ0
    · intro h
      exact hstr _ _ _ _ (by unfold EdgeConflict eQ eT; decide) (h.trans ht.symm)
    · intro h
      exact hstr _ _ _ _ (by unfold EdgeConflict eQ eS; decide) (h.trans hs.symm)
    · exact absurd rfl hi
    · exact hQ4
    · exact hQ5
  -- Step 3: `m` and `n` take the two remaining colours `y` and `z`, in some order.
  have hm : c eM.1 eM.2 = d 4 ∨ c eM.1 eM.2 = d 5 := by
    obtain ⟨j, hj⟩ := hsurj (c eM.1 eM.2)
    fin_cases j
    · exact absurd hj.symm hM0
    · exact absurd hj.symm hM1
    · exact absurd hj.symm hM2
    · exact absurd (hj.symm.trans hq.symm) (hstr _ _ _ _ (by unfold EdgeConflict eM eQ; decide))
    · exact Or.inl hj.symm
    · exact Or.inr hj.symm
  have hn : c eN.1 eN.2 = d 4 ∨ c eN.1 eN.2 = d 5 := by
    obtain ⟨j, hj⟩ := hsurj (c eN.1 eN.2)
    fin_cases j
    · exact absurd hj.symm hN0
    · exact absurd hj.symm hN1
    · exact absurd hj.symm hN2
    · exact absurd (hj.symm.trans hq.symm) (hstr _ _ _ _ (by unfold EdgeConflict eN eQ; decide))
    · exact Or.inl hj.symm
    · exact Or.inr hj.symm
  have hmn : c eM.1 eM.2 ≠ c eN.1 eN.2 :=
    hstr _ _ _ _ (by unfold EdgeConflict eM eN; decide)
  -- `p` conflicts with all of `s,t,q,m,n`, which now carry the five colours other
  -- than `x`; and `p` also conflicts with `x`.  Every colour is forbidden.
  have hp4 : c eP.1 eP.2 ≠ d 4 := by
    intro h
    rcases hm with hm4 | hm5
    · exact hstr _ _ _ _ (by unfold EdgeConflict eP eM; decide) (h.trans hm4.symm)
    · rcases hn with hn4 | hn5
      · exact hstr _ _ _ _ (by unfold EdgeConflict eP eN; decide) (h.trans hn4.symm)
      · exact hmn (hm5.trans hn5.symm)
  have hp5 : c eP.1 eP.2 ≠ d 5 := by
    intro h
    rcases hm with hm4 | hm5
    · rcases hn with hn4 | hn5
      · exact hmn (hm4.trans hn4.symm)
      · exact hstr _ _ _ _ (by unfold EdgeConflict eP eN; decide) (h.trans hn5.symm)
    · exact hstr _ _ _ _ (by unfold EdgeConflict eP eM; decide) (h.trans hm5.symm)
  obtain ⟨j, hj⟩ := hsurj (c eP.1 eP.2)
  fin_cases j
  · exact hstr _ _ _ _ (by unfold EdgeConflict eP base; decide) hj.symm
  · exact hstr _ _ _ _ (by unfold EdgeConflict eP eT; decide) (hj.symm.trans ht.symm)
  · exact hstr _ _ _ _ (by unfold EdgeConflict eP eS; decide) (hj.symm.trans hs.symm)
  · exact hstr _ _ _ _ (by unfold EdgeConflict eP eQ; decide) (hj.symm.trans hq.symm)
  · exact hp4 hj.symm
  · exact hp5 hj.symm

/-! ## The main theorem -/

theorem main : main_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- cubic
    unfold Cubic degree
    decide
  · -- claw-free
    unfold ClawFree
    decide
  · -- diamond-free
    unfold DiamondFree
    decide
  · -- strong 7-edge-colouring
    exact ⟨col, col_symm, col_strong⟩
  · -- no strong 6-edge-colouring
    exact not_six

end DsBatch.P06
