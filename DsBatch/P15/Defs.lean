import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# P15 — Counterexamples to the local antimagic leaf conjecture

Formal objects of arXiv 2610.22783 (Brondani–França, "Counterexamples to the
local antimagic leaf conjecture").

The paper's notions (Section 2, "Preliminaries"):

* all graphs are finite, simple and connected, with at least three vertices;
* given a bijection `f : E(G) → {1,…,m}`, the *induced weight* of a vertex `v`
  is `f⁺(v) = ∑_{e ∋ v} f(e)`, the sum of the labels of the edges incident
  with `v`; `f` is *local antimagic* if `f⁺(u) ≠ f⁺(v)` whenever `uv ∈ E(G)`,
  and *antimagic* if all induced weights are pairwise distinct;
* `C(f) = {f⁺(v) : v ∈ V(G)}`, and the *local antimagic chromatic number*
  `χ_la(G)` is the minimum of `|C(f)|` over all local antimagic bijections `f`;
* a *leaf* is a vertex of degree one, `ℓ(G)` is the number of leaves, and a
  *caterpillar* is a tree whose internal vertices induce a path (possibly a
  trivial one);
* for `r ≥ 2`, `Cat(p₁,…,pᵣ)` is the tree obtained from the path
  `v₁–…–vᵣ` by adjoining `pᵢ` leaves to `vᵢ` (the paper assumes
  `p₁, pᵣ ≥ 1` and `pᵢ ≥ 0`).

A bijection `E(G) → {1,…,m}` is represented by an equivalence
`E(G) ≃ Fin m` together with the label `(i : Fin m).val + 1`.
-/

namespace DsBatch.P15

/-! ## Caterpillars `Cat(p₁, …, pᵣ)` -/

/-- Vertex type of `Cat(p₁, …, pᵣ)`: the `r` path vertices `Sum.inl i`
together with the `pᵢ` leaves `Sum.inr ⟨i, j⟩` attached to the path vertex
`i`. -/
abbrev CatVertex {r : ℕ} (p : Fin r → ℕ) : Type :=
  Fin r ⊕ (Σ i : Fin r, Fin (p i))

/-- Adjacency of `Cat(p₁, …, pᵣ)`:

* two path vertices are adjacent when their indices are consecutive;
* a path vertex `i` is adjacent to each of its `pᵢ` leaves;
* there are no other adjacencies (in particular leaves are pairwise
  nonadjacent). -/
def catAdj {r : ℕ} (p : Fin r → ℕ) : CatVertex p → CatVertex p → Prop
  | Sum.inl i, Sum.inl j => i.val + 1 = j.val ∨ j.val + 1 = i.val
  | Sum.inl i, Sum.inr x => x.1 = i
  | Sum.inr x, Sum.inl i => x.1 = i
  | Sum.inr _, Sum.inr _ => False

lemma catAdj_symm {r : ℕ} (p : Fin r → ℕ) : Std.Symm (catAdj p) := by
  refine ⟨fun u v h => ?_⟩
  cases u with
  | inl i =>
    cases v with
    | inl j =>
      simp only [catAdj] at h ⊢
      omega
    | inr x =>
      simp only [catAdj] at h ⊢
      exact h
  | inr x =>
    cases v with
    | inl i =>
      simp only [catAdj] at h ⊢
      exact h
    | inr y =>
      simp only [catAdj] at h

lemma catAdj_irrefl {r : ℕ} (p : Fin r → ℕ) : Std.Irrefl (catAdj p) := by
  refine ⟨fun u => ?_⟩
  cases u with
  | inl i =>
    simp only [catAdj]
    omega
  | inr x =>
    simp only [catAdj]
    simp

/-- The caterpillar `Cat(p₁, …, pᵣ)`. -/
def catGraph {r : ℕ} (p : Fin r → ℕ) : SimpleGraph (CatVertex p) where
  Adj := catAdj p
  symm := catAdj_symm p
  loopless := catAdj_irrefl p

instance catGraphDecidableAdj {r : ℕ} (p : Fin r → ℕ) :
    DecidableRel (catGraph p).Adj := by
  intro u v
  cases u with
  | inl i =>
    cases v with
    | inl j => simp only [catGraph, catAdj]; infer_instance
    | inr x => simp only [catGraph, catAdj]; infer_instance
  | inr x =>
    cases v with
    | inl i => simp only [catGraph, catAdj]; infer_instance
    | inr y => simp only [catGraph, catAdj]; infer_instance

/-- The paper's `T₃ = Cat(8, 7, 25)`: a path `a–b–c` with 8, 7 and 25
pendant leaves at `a`, `b` and `c` respectively. -/
def shape3 : Fin 3 → ℕ := ![8, 7, 25]

/-- Vertex set of `T₃`. -/
abbrev V3 : Type := CatVertex shape3

/-- The caterpillar `T₃ = Cat(8, 7, 25)`. -/
abbrev T3 : SimpleGraph V3 := catGraph shape3

/-- The path vertex `a` of `T₃`. -/
abbrev vA : V3 := Sum.inl 0

/-- The path vertex `b` of `T₃`. -/
abbrev vB : V3 := Sum.inl 1

/-- The path vertex `c` of `T₃`. -/
abbrev vC : V3 := Sum.inl 2

/-! ## Bijective edge labellings and induced weights -/

/-- A bijective edge labelling `E(G) ≃ Fin m`, where `m = |E(G)|`.  Its
labels are the integers `(i : Fin m).val + 1`, i.e. this represents a
bijection `E(G) → {1, …, m}` as in the paper. -/
abbrev Labeling {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Type :=
  G.edgeSet ≃ Fin (Fintype.card G.edgeSet)

/-- The label in `{1, …, |E(G)|}` assigned by `L` to the edge `e`. -/
def edgeLabel {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : Labeling G) (e : G.edgeSet) : ℕ :=
  (L e).val + 1

/-- The induced weight `f⁺(v)`: the sum of the labels of the edges incident
with `v`. -/
def inducedWeight {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : Labeling G) (v : V) : ℕ :=
  ∑ e ∈ (G.incidenceFinset v).attach,
    edgeLabel G L ⟨e.1, G.mem_edgeFinset.mp (G.incidenceFinset_subset v e.2)⟩

/-- A bijective edge labelling is *local antimagic* when adjacent vertices
receive different induced weights. -/
def IsLocalAntimagic {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (L : Labeling G) : Prop :=
  ∀ u v, G.Adj u v → inducedWeight G L u ≠ inducedWeight G L v

/-- A bijective edge labelling is *antimagic* when all induced weights are
pairwise distinct. -/
def IsAntimagic {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : Labeling G) : Prop :=
  Function.Injective (inducedWeight G L)

/-- The set `C(f) = {f⁺(v) : v ∈ V(G)}` of distinct induced weights. -/
def weightImage {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : Labeling G) : Finset ℕ :=
  Finset.univ.image (inducedWeight G L)

/-- The local antimagic chromatic number `χ_la(G)`: the minimum number of
distinct induced weights `|C(f)|` over all local antimagic bijections
`f : E(G) → {1, …, |E(G)|}`. -/
noncomputable def chiLa {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  sInf {k : ℕ | ∃ L : Labeling G, IsLocalAntimagic G L ∧ (weightImage G L).card = k}

/-- The number `ℓ(G)` of leaves (vertices of degree one). -/
def leafCount {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Fintype.card {v : V // G.degree v = 1}

/-- A caterpillar: a tree whose internal vertices (vertices of degree `≠ 1`)
induce a path.  The path vertices are `v : Fin r → V`; they are required to
be distinct, to be exactly the non-leaves, and to be adjacent precisely to
their consecutive neighbours. -/
def IsCaterpillar {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Prop :=
  G.IsTree ∧
    ∃ (r : ℕ) (v : Fin r → V),
      Function.Injective v ∧
        (∀ i, G.degree (v i) ≠ 1) ∧
        (∀ x, G.degree x ≠ 1 → ∃ i, x = v i) ∧
        (∀ i j, G.Adj (v i) (v j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val))

/-- The leaf conjecture (Conjecture 2.2 of the paper): for every tree `T` of
order at least three, `χ_la(T) ≤ ℓ(T) + 2`. -/
def LeafConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree → 3 ≤ Fintype.card V → chiLa T ≤ leafCount T + 2

/-! ## An explicit local antimagic labelling of `T₃`

The edge `ab` has label `1`, the edge `bc` has label `2`, the eight leaves at
`a` get labels `3, …, 10`, the seven leaves at `b` get `11, …, 17`, and the
twenty-five leaves at `c` get `18, …, 42`.  Then the induced weights are
`f⁺(a) = 1 + (3+…+10) = 53`, `f⁺(b) = 1 + 2 + (11+…+17) = 101` and
`f⁺(c) = 2 + (18+…+42) = 752`, while the leaf weights are the labels
`1, …, 42`; in particular every adjacent pair has different weights. -/

lemma shape3_le_25 (i : Fin 3) : shape3 i ≤ 25 := by
  fin_cases i <;> decide

/-- An unordered-pair labelling function for the edges of `T₃`; its values on
non-edges are irrelevant. -/
def pairLabel : V3 → V3 → Fin 42
  | Sum.inl i, Sum.inl j =>
      if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) then 0
      else if (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) then 1
      else 0
  | Sum.inl i, Sum.inr x =>
      if i.val = 0 then ⟨2 + x.2.val, by have := x.2.isLt; have := shape3_le_25 x.1; omega⟩
      else if i.val = 1 then ⟨10 + x.2.val, by have := x.2.isLt; have := shape3_le_25 x.1; omega⟩
      else ⟨17 + x.2.val, by have := x.2.isLt; have := shape3_le_25 x.1; omega⟩
  | Sum.inr x, Sum.inl i =>
      if i.val = 0 then ⟨2 + x.2.val, by have := x.2.isLt; have := shape3_le_25 x.1; omega⟩
      else if i.val = 1 then ⟨10 + x.2.val, by have := x.2.isLt; have := shape3_le_25 x.1; omega⟩
      else ⟨17 + x.2.val, by have := x.2.isLt; have := shape3_le_25 x.1; omega⟩
  | Sum.inr _, Sum.inr _ => 0

lemma pairLabel_symm (u v : V3) : pairLabel u v = pairLabel v u := by
  cases u with
  | inl i =>
    cases v with
    | inl j =>
      fin_cases i <;> fin_cases j <;> decide
    | inr x =>
      -- the two branches agree by construction
      rfl
  | inr x =>
    cases v with
    | inl i =>
      rfl
    | inr y => rfl

/-- The labelling function on the edges of `T₃` (as unordered pairs). -/
def t3LabelFun (e : T3.edgeSet) : Fin 42 :=
  Sym2.lift ⟨pairLabel, pairLabel_symm⟩ (e : Sym2 V3)

/-- The explicit bijection `E(T₃) → {1, …, 42}` of the paper's proof: the
arrangement of labels described above. -/
noncomputable def t3Labeling : Labeling T3 :=
  (Equiv.ofBijective t3LabelFun (by decide : Function.Bijective t3LabelFun)).trans
    (finCongr (by decide : Fintype.card T3.edgeSet = 42).symm)

/-- The explicit labelling of `T₃` is local antimagic. -/
lemma t3Labeling_isLocalAntimagic : IsLocalAntimagic T3 t3Labeling := by
  unfold IsLocalAntimagic
  decide

end DsBatch.P15
