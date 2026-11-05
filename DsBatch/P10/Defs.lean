import Mathlib

/-!
# P10 — The List Total Colouring Conjecture is False (arXiv 2609.38417)

Formal objects of the paper (Jonathan A. Noel, "The List Total Colouring
Conjecture is False"):

* the explicit graph `G` on `20` vertices of Section 2: four vertex-disjoint
  copies `B_1, …, B_4` of `K_{2,3}`; the block `B_i` has *private* vertices
  `a_i`, `b_i` (the part of the bipartition of size two) and *terminal* vertices
  `v_{i,j}` for `j ≠ i`; the unique edge between `B_i` and `B_j` is the *cross
  edge* joining `v_{i,j}` to `v_{j,i}`;
* a *total colouring* of a loopless multigraph: a colour for each vertex and
  each edge such that adjacent vertices, incident edges, and each edge and its
  endpoints receive distinct colours (Section 1);
* the *total chromatic number* `χ''` and the *list total chromatic number*
  `χ''_ℓ` (Section 1);
* the specific assignment `L` of lists of size four (Section 2, Figure 2) for
  which `G` admits no proper list total colouring.

The graph `G` is encoded as `SimpleGraph V` on the structured vertex type `V`.
An edge is represented by the pair of its endpoints: internal edges of a block
by the terminal vertex and whether the private endpoint is `a_i` or `b_i`, cross
edges by an unordered pair of blocks.  The type `E` is therefore in canonical
bijection with the edge set of `G`.
-/

namespace DsBatch.P10

/-! ## The counterexample graph -/

/-- The two private vertices `a_i`, `b_i` of a block. -/
inductive Priv where
  | a
  | b
  deriving DecidableEq

instance : Fintype Priv where
  elems := {Priv.a, Priv.b}
  complete := by intro x; cases x <;> simp

/-- The terminal vertices `v_{i,j}` of the block `B_i`: pairs `(i, j)` with
`i ≠ j`.  There are `4 · 3 = 12` terminal vertices. -/
abbrev Term : Type := {p : Fin 4 × Fin 4 // p.1 ≠ p.2}

/-- The vertex set of the paper's graph `G`: the four pairs of private vertices
`a_i, b_i` and the twelve terminal vertices `v_{i,j}`.  Thus `|V| = 20`. -/
abbrev V : Type := (Fin 4 × Priv) ⊕ Term

/-- The private vertex `a_i`. -/
def va (i : Fin 4) : V := Sum.inl (i, Priv.a)

/-- The private vertex `b_i`. -/
def vb (i : Fin 4) : V := Sum.inl (i, Priv.b)

/-- The terminal vertex `v_{i,j}` (`i ≠ j`). -/
def vt (i j : Fin 4) (h : i ≠ j) : V := Sum.inr ⟨(i, j), h⟩

@[simp] lemma va_inj {i j : Fin 4} : va i = va j ↔ i = j := by simp [va]
@[simp] lemma vb_inj {i j : Fin 4} : vb i = vb j ↔ i = j := by simp [vb]
@[simp] lemma vt_inj {i j i' j' : Fin 4} {h : i ≠ j} {h' : i' ≠ j'} :
    vt i j h = vt i' j' h' ↔ i = i' ∧ j = j' := by
  simp [vt, Subtype.ext_iff, Prod.ext_iff]

@[simp] lemma va_ne_vb (i j : Fin 4) : va i ≠ vb j := by simp [va, vb]
@[simp] lemma va_ne_vt (i j k : Fin 4) (h : j ≠ k) : va i ≠ vt j k h := by simp [va, vt]
@[simp] lemma vb_ne_va (i j : Fin 4) : vb i ≠ va j := by simp [va, vb]
@[simp] lemma vb_ne_vt (i j k : Fin 4) (h : j ≠ k) : vb i ≠ vt j k h := by simp [vb, vt]
@[simp] lemma vt_ne_va (i j k : Fin 4) (h : i ≠ j) : vt i j h ≠ va k := by simp [va, vt]
@[simp] lemma vt_ne_vb (i j k : Fin 4) (h : i ≠ j) : vt i j h ≠ vb k := by simp [vb, vt]

/-- The relation generating the paper's graph: `a_i` and `b_i` are joined to
every terminal `v_{i,j}` of `B_i` (`j ≠ i`), and terminals `v_{i,j}` and
`v_{j,i}` are joined by the cross edge between `B_i` and `B_j`. -/
def rel : V → V → Prop
  | Sum.inl (i, _), Sum.inr p => i = p.val.1
  | Sum.inr p, Sum.inr q => q.val.1 = p.val.2 ∧ q.val.2 = p.val.1
  | _, _ => False

instance : DecidableRel rel := by
  rintro (⟨i, p⟩ | p) (⟨j, q⟩ | q) <;> simp only [rel] <;> infer_instance

/-- The graph `G` of the paper (Section 2), a simple cubic graph on `20`
vertices. -/
def G : SimpleGraph V := SimpleGraph.fromRel rel

instance : DecidableRel G.Adj := by
  unfold G
  infer_instance

/-- The private vertices are not adjacent to one another. -/
@[simp] lemma not_adj_priv (i j : Fin 4) (p q : Priv) :
    ¬ G.Adj (Sum.inl (i, p)) (Sum.inl (j, q)) := by
  rw [G, SimpleGraph.fromRel_adj]
  simp [rel]

/-- `a_i` is adjacent exactly to the terminals of `B_i`. -/
@[simp] lemma adj_va_term (i : Fin 4) (p : Term) :
    G.Adj (va i) (Sum.inr p) ↔ i = p.val.1 := by
  rw [G, SimpleGraph.fromRel_adj]
  simp [rel, va]

/-- `b_i` is adjacent exactly to the terminals of `B_i`. -/
@[simp] lemma adj_vb_term (i : Fin 4) (p : Term) :
    G.Adj (vb i) (Sum.inr p) ↔ i = p.val.1 := by
  rw [G, SimpleGraph.fromRel_adj]
  simp [rel, vb]

/-- The cross edges: `v_{i,j}` is adjacent to `v_{j,i}`. -/
@[simp] lemma adj_term_term (p q : Term) :
    G.Adj (Sum.inr p) (Sum.inr q) ↔
      (q.val.1 = p.val.2 ∧ q.val.2 = p.val.1) := by
  rw [G, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact ⟨h.2.symm, h.1.symm⟩
  · intro h
    refine ⟨?_, Or.inl h⟩
    intro hpq
    have hpq' : p = q := Sum.inr.inj hpq
    rw [hpq'] at h
    exact q.property h.1

/-! ## The edge type -/

/-- The `6` cross edges, indexed by the unordered pair `{i, j}` of blocks with
`i < j`. -/
abbrev CrossIdx : Type := {p : Fin 4 × Fin 4 // p.1 < p.2}

/-- The edge set of `G`: the internal edges of the blocks (`a_i v_{i,j}` and
`b_i v_{i,j}`, encoded by the terminal `v_{i,j}` and which private endpoint is
used) and the cross edges. -/
abbrev E : Type := (Term × Priv) ⊕ CrossIdx

/-- The internal edge `a_i v_{i,j}` (`i ≠ j`). -/
def eA (i j : Fin 4) (h : i ≠ j) : E := Sum.inl (⟨(i, j), h⟩, Priv.a)

/-- The internal edge `b_i v_{i,j}` (`i ≠ j`). -/
def eB (i j : Fin 4) (h : i ≠ j) : E := Sum.inl (⟨(i, j), h⟩, Priv.b)

/-- The unordered-pair index of the cross edge joining `v_{i,j}` and `v_{j,i}`. -/
def crossIdx (i j : Fin 4) (h : i ≠ j) : CrossIdx :=
  if hij : i < j then ⟨(i, j), hij⟩
  else ⟨(j, i), by dsimp; omega⟩

/-- The cross edge between the blocks `B_i` and `B_j` (`i ≠ j`). -/
def crossE (i j : Fin 4) (h : i ≠ j) : E := Sum.inr (crossIdx i j h)

lemma crossE_comm (i j : Fin 4) (h : i ≠ j) : crossE i j h = crossE j i h.symm := by
  unfold crossE crossIdx
  by_cases hij : i < j
  · have hji : ¬ j < i := by omega
    simp [hij, hji]
  · have hji : j < i := by omega
    simp [hij, hji]

/-- The first endpoint of an edge. -/
def eLeft : E → V
  | Sum.inl (p, Priv.a) => va p.val.1
  | Sum.inl (p, Priv.b) => vb p.val.1
  | Sum.inr q => vt q.val.1 q.val.2 (ne_of_lt q.property)

/-- The second endpoint of an edge. -/
def eRight : E → V
  | Sum.inl (p, _) => vt p.val.1 p.val.2 p.property
  | Sum.inr q => vt q.val.2 q.val.1 (ne_of_lt q.property).symm

lemma eA_left (i j : Fin 4) (h : i ≠ j) : eLeft (eA i j h) = va i := rfl
lemma eA_right (i j : Fin 4) (h : i ≠ j) : eRight (eA i j h) = vt i j h := rfl
lemma eB_left (i j : Fin 4) (h : i ≠ j) : eLeft (eB i j h) = vb i := rfl
lemma eB_right (i j : Fin 4) (h : i ≠ j) : eRight (eB i j h) = vt i j h := rfl

/-- The cross edge `v_{i,j}v_{j,i}` is incident to `v_{i,j}`. -/
lemma crossE_inc_left (i j : Fin 4) (h : i ≠ j) : eLeft (crossE i j h) = vt i j h ∨
    eRight (crossE i j h) = vt i j h := by
  unfold crossE crossIdx eLeft eRight
  by_cases hij : i < j
  · simp [hij]
  · have hji : j < i := by omega
    simp [hij, hji]

/-- The cross edge `v_{i,j}v_{j,i}` is incident to `v_{j,i}`. -/
lemma crossE_inc_right (i j : Fin 4) (h : i ≠ j) : eLeft (crossE i j h) = vt j i h.symm ∨
    eRight (crossE i j h) = vt j i h.symm := by
  unfold crossE crossIdx eLeft eRight
  by_cases hij : i < j
  · simp [hij]
  · have hji : j < i := by omega
    simp [hij, hji]

/-! ## Total colourings -/

/-- An element of the graph that receives a colour in a total colouring: a
vertex or an edge. -/
abbrev El : Type := V ⊕ E

/-- Two elements of the graph are *conflicting* when they are adjacent vertices,
incident edges, or an edge and one of its endpoints. -/
def elAdj : El → El → Prop
  | Sum.inl u, Sum.inl w => G.Adj u w
  | Sum.inl u, Sum.inr e => eLeft e = u ∨ eRight e = u
  | Sum.inr e, Sum.inl u => eLeft e = u ∨ eRight e = u
  | Sum.inr e, Sum.inr f =>
      e ≠ f ∧ (eLeft e = eLeft f ∨ eLeft e = eRight f ∨
        eRight e = eLeft f ∨ eRight e = eRight f)

/-- A proper total colouring with colours in `C`: conflicting elements receive
different colours (Section 1 of the paper). -/
def ProperTotalColoring {C : Type} (c : El → C) : Prop :=
  ∀ x y : El, elAdj x y → c x ≠ c y

instance instDecidableElAdj (x y : El) : Decidable (elAdj x y) := by
  cases x with
  | inl u =>
    cases y with
    | inl w => exact inferInstanceAs (Decidable (G.Adj u w))
    | inr e => exact inferInstanceAs (Decidable (eLeft e = u ∨ eRight e = u))
  | inr e =>
    cases y with
    | inl u => exact inferInstanceAs (Decidable (eLeft e = u ∨ eRight e = u))
    | inr f =>
      exact inferInstanceAs (Decidable
        (e ≠ f ∧ (eLeft e = eLeft f ∨ eLeft e = eRight f ∨
          eRight e = eLeft f ∨ eRight e = eRight f)))

/-- Decidability of properness, by checking all ordered pairs of elements. -/
instance instDecidableProperTotalColoring {C : Type} [DecidableEq C] (c : El → C) :
    Decidable (ProperTotalColoring c) :=
  decidable_of_iff
    (∀ p ∈ (Finset.univ : Finset (El × El)), ¬ elAdj p.1 p.2 ∨ c p.1 ≠ c p.2) (by
      simp [ProperTotalColoring, Finset.mem_univ, imp_iff_not_or])

/-- The graph is cubic: every vertex has degree three. -/
def Cubic : Prop := ∀ v : V, G.degree v = 3

instance : Decidable Cubic := by unfold Cubic; infer_instance

/-- A vector of colours gives a total colouring that is proper. -/
def TotalColouringExists := ∃ c : El → Fin 4, ProperTotalColoring c

/-! ### A total colouring with four colours (Section 2) -/

/-- The colour (`0`-based, i.e. the paper's colour minus one) of the terminal
vertex `v_{i,j}` in the four-colouring of Section 2:
`c(v_{i,j}) = j` for `i, j ≤ 3`, `c(v_{i,4}) = i` for `i ≤ 3`, and
`(c(v_{4,1}), c(v_{4,2}), c(v_{4,3})) = (2, 3, 1)`. -/
def termColour (p : Term) : Fin 4 :=
  if p.val.1.val = 3 then ⟨(p.val.2.val + 1) % 3, by omega⟩
  else if p.val.2.val = 3 then p.val.1
  else p.val.2

/-- Cyclic successor on the colours `{0,1,2}` (the paper's `{1,2,3}`). -/
def cycSucc (c : Fin 4) : Fin 4 := ⟨(c.val + 1) % 3, by omega⟩

/-- Cyclic predecessor on the colours `{0,1,2}`. -/
def cycPred (c : Fin 4) : Fin 4 := ⟨(c.val + 2) % 3, by omega⟩

/-- The four-colouring of Section 2: private vertices and cross edges get
colour `4` (index `3`); each terminal `v` of colour `r` sends the edge to `a_i`
with the colour following `r` cyclically and the edge to `b_i` with the colour
preceding `r`. -/
def colour4 : El → Fin 4
  | Sum.inl (Sum.inl (_, _)) => 3
  | Sum.inl (Sum.inr p) => termColour p
  | Sum.inr (Sum.inl (p, Priv.a)) => cycSucc (termColour p)
  | Sum.inr (Sum.inl (p, Priv.b)) => cycPred (termColour p)
  | Sum.inr (Sum.inr _) => 3

/-! ### The list assignment `L` (Section 2, Figure 2) -/

/-- The colour omitted by the list of the cross edge between the blocks `B_i`
and `B_j`: for consecutive blocks `B_i, B_{i+1}` (cyclically) the omitted colour
is `i + 2` (cyclically), and the two cross edges `B_1B_3`, `B_2B_4` omit
colour `5`.  Indices are `0`-based here. -/
def omitCol (i j : Fin 4) : Fin 5 :=
  if (i.val + 1) % 4 = j.val then ⟨(i.val + 2) % 4, by omega⟩
  else if (j.val + 1) % 4 = i.val then ⟨(j.val + 2) % 4, by omega⟩
  else 4

lemma omitCol_comm (i j : Fin 4) : omitCol i j = omitCol j i := by
  unfold omitCol
  by_cases h1 : (i.val + 1) % 4 = j.val
  · by_cases h2 : (j.val + 1) % 4 = i.val
    · have : i = j := by omega
      subst this
      simp [h1, h2]
    · simp [h1, h2]
  · by_cases h2 : (j.val + 1) % 4 = i.val
    · simp [h1, h2]
    · simp [h1, h2]

/-- The block of a vertex. -/
def vBlock : V → Fin 4
  | Sum.inl (i, _) => i
  | Sum.inr p => p.val.1

/-- The block of an edge: both endpoints of an internal edge lie in one block;
for a cross edge this is its smaller block index. -/
def eBlock : E → Fin 4
  | Sum.inl (p, _) => p.val.1
  | Sum.inr q => q.val.1

/-- The assignment `L` of lists of size four of Section 2 (Figure 2): every
vertex and internal edge of `B_i` has list `{1,2,3,4,5} \ {i}`, and the cross
edge between `B_i` and `B_j` has list `{1,2,3,4,5} \ {omitCol i j}`. -/
def Lstar : El → Finset (Fin 5)
  | Sum.inl v => Finset.univ.erase (Fin.castSucc (vBlock v))
  | Sum.inr e =>
    match e with
    | Sum.inl _ => Finset.univ.erase (Fin.castSucc (eBlock e))
    | Sum.inr q => Finset.univ.erase (omitCol q.val.1 q.val.2)

/-- `G` admits a proper total colouring all of whose colours are drawn from the
lists `L`. -/
def ListTotalColourable (L : El → Finset (Fin 5)) : Prop :=
  ∃ c : El → Fin 5, ProperTotalColoring c ∧ ∀ x : El, c x ∈ L x

end DsBatch.P10
