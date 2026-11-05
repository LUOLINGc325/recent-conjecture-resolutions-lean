import DsBatch.P06.Defs

/-! Frozen specification for project P06. This file must stay sorry-free:
    state each target as `def <name>_statement : Prop := <type>` here and put
    the proof-carrying `theorem` in Main.lean.

    Target (queue scope, required part): the explicit graph `H` of
    arXiv 2607.23462 is cubic, claw-free, diamond-free, has a strong
    7-edge-colouring and no strong 6-edge-colouring. -/

namespace DsBatch.P06

open V

/-- The paper's theorem (Theorem 1.1) for its explicit 18-vertex graph `H`
(Constructions 3 and 4): `H` is cubic, claw-free and diamond-free, has a strong
7-edge-colouring, and has no strong 6-edge-colouring.  In particular its strong
chromatic index is exactly `7`. -/
def main_statement : Prop :=
  Cubic H ∧ ClawFree H ∧ DiamondFree H ∧
    StrongEdgeColoring H 7 ∧ ¬ StrongEdgeColoring H 6

/-! ## Non-vacuity checks

The explicit object exists with the stated structure, and each defined property is
neither vacuous nor trivially true/false. -/

/-- `H` has 18 vertices. -/
example : Fintype.card V = 18 := by decide

/-- The triangles and connecting edges of `H` are present: `a₀a₁` is an edge. -/
example : H.Adj a0 a1 := by decide

/-- Non-edges are absent: `a₀c₁` is not an edge of `H`. -/
example : ¬ H.Adj a0 c1 := by decide

/-- The bridge `a₂⁽¹⁾a₂⁽²⁾` joins the two copies. -/
example : H.Adj a2 a2' := by decide

/-- The degree of `a₀` in `H` is `3`. -/
example : degree H a0 = 3 := by decide

/-- The notion of degree is not constant: an isolated vertex has degree `0`. -/
example : degree (⊥ : SimpleGraph V) a0 = 0 := by decide

/-- A graph on `V` that is not claw-free: the centre `a₀` with the three pairwise
non-adjacent neighbours `b₀`, `c₀`, `a₁`. -/
abbrev clawRel (u v : V) : Prop := u = a0 ∧ (v = b0 ∨ v = c0 ∨ v = a1)

instance : DecidableRel clawRel := fun _ _ => inferInstance

/-- The claw `K_{1,3}` on `V`, used only to show `ClawFree` is not vacuous. -/
abbrev clawGraph : SimpleGraph V := SimpleGraph.fromRel clawRel

/-- `ClawFree` is not trivially true: the star centred at `a₀` is not claw-free. -/
example : ¬ ClawFree clawGraph := by
  intro h
  have h' := h a0 b0 c0 a1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  exact (by decide : ¬ (clawGraph.Adj b0 c0 ∨ clawGraph.Adj b0 a1 ∨
    clawGraph.Adj c0 a1)) h'

/-- `ClawFree` is not trivially false: the empty graph is claw-free. -/
example : ClawFree (⊥ : SimpleGraph V) := by
  intro v x y z hx _ _ _ _ _
  exact absurd hx (by simp)

/-- A graph on `V` containing a diamond `K₄ - e`: the edge `a₀a₁` has the two common
neighbours `b₀` and `c₀`. -/
abbrev diamondRel (u v : V) : Prop :=
  (u = a0 ∧ v = a1) ∨ (u = a0 ∧ v = b0) ∨ (u = a1 ∧ v = b0) ∨
    (u = a0 ∧ v = c0) ∨ (u = a1 ∧ v = c0)

instance : DecidableRel diamondRel := fun _ _ => inferInstance

/-- The diamond `K₄ - e` on `V`, used only to show `DiamondFree` is not vacuous. -/
abbrev diamondGraph : SimpleGraph V := SimpleGraph.fromRel diamondRel

/-- `DiamondFree` is not trivially true: `a₀a₁` has two common neighbours. -/
example : ¬ DiamondFree diamondGraph := by
  intro h
  have h' := h a0 a1 b0 c0 (by decide) (by decide) (by decide) (by decide) (by decide)
  exact (by decide : b0 ≠ c0) h'

/-- `DiamondFree` is not trivially false: the empty graph is diamond-free. -/
example : DiamondFree (⊥ : SimpleGraph V) := by
  intro u v x y huv _ _ _ _
  exact absurd huv (by simp)

/-- `StrongEdgeColoring` is not trivially false: the empty graph has a strong
`1`-edge-colouring (no edges, so no conflicts). -/
example : StrongEdgeColoring (⊥ : SimpleGraph V) 1 := by
  refine ⟨fun _ _ => 0, fun _ _ => rfl, ?_⟩
  intro u v x y h
  exact absurd h.1 (by simp)

/-- `StrongEdgeColoring` is not trivially true: the three edges of the triangle `A` of
`H` are pairwise in conflict, so two colours do not suffice for `H`. -/
example : ¬ StrongEdgeColoring H 2 := by
  rintro ⟨c, _hsym, hstr⟩
  have hp : c a0 a1 ≠ c a1 a2 :=
    hstr a0 a1 a1 a2 (by unfold EdgeConflict; decide)
  have hq : c a1 a2 ≠ c a2 a0 :=
    hstr a1 a2 a2 a0 (by unfold EdgeConflict; decide)
  have hr : c a2 a0 ≠ c a0 a1 :=
    hstr a2 a0 a0 a1 (by unfold EdgeConflict; decide)
  exact (by decide : ∀ p q r : Fin 2, p ≠ q → q ≠ r → r ≠ p → False)
    (c a0 a1) (c a1 a2) (c a2 a0) hp hq hr

end DsBatch.P06
