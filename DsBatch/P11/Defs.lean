import Mathlib

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-!
# Definitions for project P11: atlas-lean port of P02

The definitions below are copied verbatim from `facebookresearch/atlas-lean`
(Apache-2.0), with only the `module`, `public import`, `@[expose] public section` lines and the
`MathlibExt` import dropped, as required by the queue:

* `IsListColoring`, `lambdaMax`, `lambdaMin`, `conjecture` from
  `WantedExt/GraphTheory/PartialListColoringWanted.lean`
  (`papers/atlas-P02/PartialListColoringWanted.lean`);
* `SimpleGraph.IsListColorable` and `SimpleGraph.IsChoiceNumber` (needed by `conjecture`) from
  `MathlibExt/Combinatorics/SimpleGraph/ListColoring.lean`
  (`papers/atlas-P02/ListColoring.lean`).

Since the `MathlibExt` import is dropped, the contents of the second file are inlined first, so
that `conjecture` can use `SimpleGraph.IsChoiceNumber`; the definition bodies are unchanged.

The source record is `OPG-788`, Iradmusa's partial list coloring monotonicity conjecture from the
Open Problem Garden (posted May 12th, 2008): the ratio `λ_t / t` is nonincreasing in `t` up to the
list chromatic number.
-/

/-!
# List colorings of simple graphs

This file provides basic predicates for vertex list colorability and choice
numbers. A list coloring is represented by a Mathlib `SimpleGraph.Coloring`
whose value at each vertex belongs to that vertex's finite list of colors.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {q r : ℕ}

/-- A graph is `q`-list-colorable if every assignment of at least `q` colors to
each vertex admits a proper coloring chosen from those lists. -/
def IsListColorable (G : SimpleGraph V) (q : ℕ) : Prop :=
  ∀ (C : Type) [DecidableEq C] (lists : V → Finset C),
    (∀ v, q ≤ (lists v).card) →
      ∃ color : G.Coloring C, ∀ v, color v ∈ lists v

/-- `q` is the choice number of `G` if `G` is `q`-list-colorable but is not
list-colorable with any smaller number of colors. -/
def IsChoiceNumber (G : SimpleGraph V) (q : ℕ) : Prop :=
  G.IsListColorable q ∧ ∀ r < q, ¬G.IsListColorable r

/-- List colorability is monotone in the number of colors required in each list. -/
theorem IsListColorable.mono (hG : G.IsListColorable q) (hqr : q ≤ r) :
    G.IsListColorable r := by
  intro C _ lists hlists
  exact hG C lists fun v => hqr.trans (hlists v)

/-- A list-colorable graph is colorable with the same number of colors. -/
theorem IsListColorable.colorable (hG : G.IsListColorable q) : G.Colorable q := by
  let lists : V → Finset (Fin q) := fun _ => Finset.univ
  obtain ⟨color, _⟩ := hG (Fin q) lists (by simp [lists])
  exact ⟨color⟩

end SimpleGraph

/-!
# Partial List Coloring
-/

namespace MathlibExt.GraphTheory.PartialListColoringWanted

/-! Source record `OPG-788`. Iradmusa's partial list coloring monotonicity conjecture
from the Open Problem Garden (posted May 12th, 2008): the ratio `λ_t / t` is
nonincreasing in `t` up to the list chromatic number. -/

/-- A proper coloring of the vertex subset `S` respecting the list assignment `L`:
every vertex of `S` gets a color from its own list, and adjacent vertices get distinct colors. -/
def IsListColoring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : V → Finset ℕ) (f : V → ℕ) (S : Finset V) : Prop :=
  (∀ v ∈ S, f v ∈ L v) ∧ ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → f v ≠ f w

/-- `lambdaMax G L` is `λ_L`: the maximum number of vertices of `G` colorable
with respect to the list assignment `L` (the largest `k` for which some
`k`-element subset admits a proper list coloring). -/
noncomputable def lambdaMax {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (L : V → Finset ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset V, ∃ f : V → ℕ, S.card = k ∧ IsListColoring G L f S}

/-- `lambdaMin G t` is `λ_t`: the minimum of `λ_L` over all list assignments
`L` with every list of size `t`. -/
noncomputable def lambdaMin {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ L : V → Finset ℕ, (∀ v, (L v).card = t) ∧ lambdaMax G L = k}

/-- Iradmusa's conjecture: for a graph with choice number `χ_ℓ` (via the
shared `SimpleGraph.IsChoiceNumber` predicate) and `1 ≤ r ≤ s ≤ χ_ℓ`, one
has `λ_r / r ≥ λ_s / s`. -/
def conjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (χ_ℓ r s : ℕ),
    G.IsChoiceNumber χ_ℓ →
    1 ≤ r → r ≤ s → s ≤ χ_ℓ →
    (lambdaMin G r : ℚ) / (r : ℚ) ≥ (lambdaMin G s : ℚ) / (s : ℚ)

end MathlibExt.GraphTheory.PartialListColoringWanted
