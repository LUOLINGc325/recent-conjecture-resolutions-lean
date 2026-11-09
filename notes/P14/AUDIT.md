PASS

Fidelity audit of `DsBatch/P14` against arXiv 2610.03151, "Arithmetic properties of solubilizers" (L. Sabatini).

## 1. Definitions (`DsBatch/P14/Defs.lean`)

- `cyclicSubgroup x = Subgroup.closure ({x} : Set G)` (Defs.lean:23) is exactly the cyclic subgroup ⟨x⟩. Faithful.
- `normalizerOf x = Subgroup.normalizer ((cyclicSubgroup x : Subgroup G) : Set G)` (Defs.lean:27-28). Mathlib's `Subgroup.normalizer` (Algebra/Group/Subgroup/Defs.lean:669) is `{g | g·S·g⁻¹ = S}`, and here `S` is the carrier set of the subgroup ⟨x⟩, so this is the standard subgroup normalizer N_G(⟨x⟩) = {g : ⟨x^g⟩ = ⟨x⟩}. The paper (main-2.tex:186) defines N_G(x) = {g : ⟨x⟩ ⊴ ⟨x,g⟩} and states this is equivalent to ⟨x⟩ = ⟨x^g⟩; these coincide. It is NOT the normalizer of the one-element set {x} and NOT the centralizer. Faithful.
- `solubilizer x = {g : G | Group.IsSolvable (Subgroup.closure ({x, g} : Set G))}` (Defs.lean:32-33). This is exactly the paper's Sol_G(x) = {g : ⟨x,g⟩ is soluble} (main-2.tex:125), using the real Mathlib solvability predicate `Group.IsSolvable`. Faithful.
- `solubilizerIn x K = {g : K | Group.IsSolvable (closure {x, (g : G)})}` (Defs.lean:36-37) is exactly Sol_G(x) ∩ K regarded as a subset of K. Faithful.

## 2. Statement (`DsBatch/P14/Statement.lean`)

`main_statement` (Statement.lean:32-34):
`∀ (G : Type u) [Group G] [Finite G] (x : G) (K : Subgroup G), Nat.card ↥(normalizerOf x ⊓ K) ∣ Nat.card ↥(solubilizerIn x K)`.

- Precisely the required theorem for all finite groups: quantifier order G, x, K matches Theorem thMain (main-2.tex:137-141); the finiteness hypothesis is present as `[Finite G]`; no added hypotheses, no weakening, no missing case. K = G (⊤) is the conjecture as a special case.
- `normalizerOf x ⊓ K` is the subgroup intersection N_G(x) ∩ K (both are subgroups); `Nat.card` of its subtype is |N_G(x) ∩ K|. `solubilizerIn x K` is the set intersection Sol_G(x) ∩ K as a subset of K; `Nat.card` of its subtype is |Sol_G(x) ∩ K|. The subgroup-vs-set distinction is handled correctly.
- Universe polymorphism (`Type u` with `universe u`) is acceptable: `main_statement`/`main` are universe-polymorphic and hold in every universe.
- `Nat.card` of these finite types equals the cardinality (subgroups/subtypes of a finite group are finite), so "divides" is on the correct natural-number cardinalities.

## 3. project.json

Targets (project.json:9-14): `{"name": "DsBatch.P14.main", "lean_type": "DsBatch.P14.main_statement"}`. `main_statement` is defined in `DsBatch.P14` (Statement.lean:32) and the stub theorem `main : main_statement` is in `DsBatch.P14` (Main.lean:10). Names and lean_type match exactly. Single target = the required scope, no more, no less.

## 4. Non-vacuity

The definitions are genuine and cannot make the statement vacuous: `solubilizer` is a real `Set G` predicate (not fiat-univ), and `normalizerOf` is a real normalizer subgroup (not fiat-bot). The examples in Statement.lean are meaningful:
- `1 ∈ solubilizer x` (54-59), `x ∈ solubilizer x` (62-66), `(1 : K) ∈ solubilizerIn x K` (69-74): Sol and Sol ∩ K are non-empty in every group; no fiat-emptiness.
- `cyclicSubgroup x ≤ normalizerOf x` (77-79): N_G(x) contains ⟨x⟩ (via `Subgroup.le_normalizer`), so N_G(x) is not a degenerate ⊥ (for x ≠ 1 it is non-trivial).
- Explicit finite instances with positive counts: G = (ZMod 5)ˣ, x = 1, K = ⊤ gives |N∩K| = |Sol∩K| = 4 (85-106), and K = ⊥ gives 1 ∣ 1 (110-126).

Missing (noted explicitly, but not blockers): the examples do not demonstrate (a) the paper's inclusion N_G(x) ⊆ Sol_G(x) (main-2.tex:189), (b) a strict divisibility case with quotient > 1, or (c) that Sol_G(x) ≠ G in some group (the comment at Statement.lean:38-43 claims "neither empty nor all of G", but the examples only establish non-emptiness and membership, not that Sol is a proper subset). These are worthwhile additional guards but not required for fidelity; the definitions and the statement are faithful and the theorem is not trivially true.

## 5. Paper-vs-Lean mismatches

None found. Quantifier order, the subgroup/set intersection distinction, and the cardinality-of-subset interpretation all match the paper.
