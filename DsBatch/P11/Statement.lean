import DsBatch.P11.Defs
import DsBatch.P02.Main

/-! Frozen specification for project P11. This file must stay sorry-free:
    state each target as `def <name>_statement : Prop := <type>` here and put
    the proof-carrying `theorem` in Main.lean. -/

namespace DsBatch.P11

open MathlibExt.GraphTheory.PartialListColoringWanted

/-- Iradmusa's partial list coloring conjecture (Open Problem Garden record `OPG-788`, posted
May 12th, 2008) is false: Noel's 14-vertex graph of arXiv:2609.23291 is a counterexample.

The target is exactly the negation of the atlas-lean `conjecture` definition. -/
def conjecture_refuted_statement : Prop := ¬ conjecture

/-! ## Technical lemmas for the non-vacuity checks

The atlas-lean `SimpleGraph.IsListColorable` quantifies over an arbitrary color type `C`, while
the ported P02 development works with lists of natural numbers.  These two lemmas translate
between the two presentations; `Main.lean` reuses them for the proof. -/

/-- A graph that is choosable in the `ℕ`-list sense of P02 is list-colorable in the atlas-lean
sense over an arbitrary color type: the finite union of the lists is injectively encoded in `ℕ`. -/
lemma isListColorable_of_choosable {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} {q : ℕ} (h : DsBatch.P02.Choosable H q) :
    H.IsListColorable q := by
  intro C _ lists hlists
  classical
  let U : Finset C := Finset.univ.biUnion lists
  let e : {c // c ∈ U} ≃ Fin (Fintype.card U) := Fintype.equivFin _
  let ψ : C → ℕ := fun c => if hc : c ∈ U then (e ⟨c, hc⟩).val else 0
  have hψ : ∀ {a b : C}, a ∈ U → b ∈ U → ψ a = ψ b → a = b := by
    intro a b ha hb hab
    simp only [ψ, dite_eq_left ha, dite_eq_left hb] at hab
    have h1 : e ⟨a, ha⟩ = e ⟨b, hb⟩ := Fin.ext hab
    have h2 := e.injective h1
    simpa using congrArg Subtype.val h2
  -- P02's notion uses lists of size exactly `q`; shrink the given lists to size `q`.
  have hsmall : ∀ v, ∃ t : Finset C, t ⊆ lists v ∧ t.card = q := fun v =>
    Finset.exists_subset_card_eq (hlists v)
  choose ls hls_sub hls_card using hsmall
  have hls_U : ∀ v, ls v ⊆ U := fun v c hc =>
    Finset.subset_biUnion_of_mem lists (Finset.mem_univ v) (hls_sub v hc)
  let lists' : W → Finset ℕ := fun v => (ls v).image ψ
  have hcard : ∀ v, (lists' v).card = q := by
    intro v
    have hinj : Set.InjOn ψ (↑(ls v) : Set C) := by
      intro a ha b hb hab
      exact hψ (hls_U v ha) (hls_U v hb) hab
    rw [Finset.card_image_of_injOn hinj]
    exact hls_card v
  obtain ⟨c', hmem', hprop'⟩ := h lists' hcard
  let g : W → C := fun v => Classical.choose (Finset.mem_image.mp (hmem' v))
  have hg_mem : ∀ v, g v ∈ lists v := fun v =>
    hls_sub v (Classical.choose_spec (Finset.mem_image.mp (hmem' v))).1
  have hg_val : ∀ v, ψ (g v) = c' v := fun v =>
    (Classical.choose_spec (Finset.mem_image.mp (hmem' v))).2
  refine ⟨⟨g, ?_⟩, hg_mem⟩
  intro u v huv hEq
  exact hprop' u v huv (by rw [← hg_val u, hEq, hg_val v])

/-- Conversely, atlas-lean list-colorability over `ℕ` gives P02's `Choosable` predicate. -/
lemma choosable_of_isListColorable {W : Type*} {H : SimpleGraph W} {q : ℕ}
    (h : H.IsListColorable q) : DsBatch.P02.Choosable H q := by
  intro L hL
  obtain ⟨color, hmem⟩ := h ℕ L (fun v => by rw [hL v])
  exact ⟨color, hmem, fun u v huv => color.valid huv⟩

/-- The explicit 14-vertex graph of P02 (Noel's graph) has choice number `3` in the atlas-lean
sense, i.e. it satisfies the hypothesis of `conjecture`. -/
theorem p02_isChoiceNumber : DsBatch.P02.G.IsChoiceNumber 3 := by
  refine ⟨isListColorable_of_choosable DsBatch.P02.choosable_three, ?_⟩
  intro r hr hlist
  have hch := choosable_of_isListColorable hlist
  interval_cases r
  · exact DsBatch.P02.not_choosable_zero hch
  · exact DsBatch.P02.not_choosable_one hch
  · exact DsBatch.P02.not_choosable_two hch

/-! ## Non-vacuity checks

The explicit object of the paper satisfies the hypotheses of the statement, and the predicates
involved are neither empty nor universal. -/

/-- The explicit graph of the counterexample exists: it has 14 vertices. -/
example : Fintype.card DsBatch.P02.V = 14 := by decide

/-- The explicit graph satisfies the hypothesis of `conjecture`: its choice number is `3`. -/
example : DsBatch.P02.G.IsChoiceNumber 3 := p02_isChoiceNumber

/-- The explicit 2-list assignment of the paper is a genuine 2-list assignment. -/
example : DsBatch.P02.IsListAssignment DsBatch.P02.L 2 := by
  unfold DsBatch.P02.IsListAssignment; decide

/-- The 2-list assignment is not trivially fully colorable: nine vertices can be coloured, and
the colouring is a proper list colouring in the atlas-lean sense. -/
example : ∃ (S : Finset DsBatch.P02.V) (f : DsBatch.P02.V → ℕ),
    IsListColoring DsBatch.P02.G DsBatch.P02.L f S ∧ S.card = 9 := by
  refine ⟨DsBatch.P02.S9, DsBatch.P02.c9, ?_, by decide⟩
  have hp : DsBatch.P02.IsPartialListColoring DsBatch.P02.G DsBatch.P02.L
      DsBatch.P02.S9 DsBatch.P02.c9 := by
    unfold DsBatch.P02.IsPartialListColoring
    decide
  exact hp

/-- `IsChoiceNumber` is not vacuously false: the one-vertex edgeless graph has choice number one,
so `conjecture` has a nonempty class of graphs satisfying its hypothesis. -/
example : (⊥ : SimpleGraph (Fin 1)).IsChoiceNumber 1 := by
  constructor
  · intro C _ lists hlists
    obtain ⟨x, hx⟩ : ∃ x, x ∈ lists 0 :=
      Finset.card_pos.mp (by have h := hlists 0; omega)
    refine ⟨⟨fun _ => x, ?_⟩, ?_⟩
    · intro a b hab; exact absurd hab (by simp)
    · intro v; fin_cases v; exact hx
  · intro r hr h
    have hr0 : r = 0 := by omega
    subst hr0
    obtain ⟨color, hmem⟩ := h (ℕ) (fun _ => (∅ : Finset ℕ)) (by intro v; simp)
    exact absurd (hmem 0) (by simp)

end DsBatch.P11
