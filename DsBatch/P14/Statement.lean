import DsBatch.P14.Defs

/-!
# P14 — Statements

Formal target of arXiv 2610.03151 (L. Sabatini, "Arithmetic properties of
solubilizers").

Required scope (from `queue/QUEUE.md`): for every finite group `G`, every
`x : G` and every subgroup `K ≤ G`,

  `|N_G(x) ∩ K|` divides `|Sol_G(x) ∩ K|`,

where `Sol_G(x) = {g : G : ⟨x, g⟩ is soluble}` and
`N_G(x) = {g : G : ⟨x⟩ ⊴ ⟨x, g⟩}`.  The case `K = G` is the
Mousavi–Poozesh–Zamani conjecture.

The target below states exactly this.  `N_G(x) ∩ K` is the subgroup
`normalizerOf x ⊓ K`; `Sol_G(x) ∩ K` is the subtype `solubilizerIn x K`
of `K`.
-/

namespace DsBatch.P14

universe u

variable {G : Type*} [Group G]

/-- **Theorem main** (Theorem `thMain` of the paper).  For every finite group
`G`, every `x : G` and every subgroup `K ≤ G`, the cardinality of
`N_G(x) ∩ K` divides the cardinality of `Sol_G(x) ∩ K`. -/
def main_statement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (x : G) (K : Subgroup G),
    Nat.card ↥(normalizerOf x ⊓ K) ∣ Nat.card ↥(solubilizerIn x K)

/-! ## Non-vacuity checks

`Sol_G(x)` is not empty: it contains `1` and `x` (for every `x`, the subgroup
`⟨x, 1⟩ = ⟨x⟩` is cyclic, hence soluble), and `N_G(x)` contains the cyclic
subgroup `⟨x⟩` (a subgroup is contained in its normalizer).  The conclusion is
therefore a divisibility between two genuine subsets, and it holds with
positive counts in explicit examples. -/

/-- The cyclic subgroup `⟨x⟩` is commutative, hence soluble. -/
private theorem isSolvable_closure_singleton (x : G) :
    Group.IsSolvable (Subgroup.closure ({x} : Set G)) := by
  rw [← Subgroup.zpowers_eq_closure]
  have : IsMulCommutative (Subgroup.zpowers x) := Subgroup.zpowers_isMulCommutative x
  infer_instance

/-- `1` belongs to the solubilizer of every element: `⟨x, 1⟩ = ⟨x⟩` is
cyclic. -/
example (x : G) : (1 : G) ∈ solubilizer x := by
  unfold solubilizer
  change Group.IsSolvable (Subgroup.closure ({x, 1} : Set G))
  rw [show ({x, 1} : Set G) = {x} ∪ {1} by ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
  rw [Subgroup.closure_union_one]
  exact isSolvable_closure_singleton x

/-- `x` belongs to its own solubilizer. -/
example (x : G) : x ∈ solubilizer x := by
  unfold solubilizer
  change Group.IsSolvable (Subgroup.closure ({x, x} : Set G))
  rw [show ({x, x} : Set G) = {x} by ext y; simp]
  exact isSolvable_closure_singleton x

/-- `1` belongs to `Sol_G(x) ∩ K` for every subgroup `K`. -/
example (x : G) (K : Subgroup G) : (1 : K) ∈ solubilizerIn x K := by
  unfold solubilizerIn
  change Group.IsSolvable (Subgroup.closure ({x, (1 : G)} : Set G))
  rw [show ({x, (1 : G)} : Set G) = {x} ∪ {1} by ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
  rw [Subgroup.closure_union_one]
  exact isSolvable_closure_singleton x

/-- `N_G(x)` contains `⟨x⟩`, so it is not a degenerate `⊥` for `x ≠ 1`. -/
example (x : G) : cyclicSubgroup x ≤ normalizerOf x := by
  unfold normalizerOf
  exact Subgroup.le_normalizer

/-- The hypothesis class of `main_statement` is inhabited, and in an abelian
group the two sides are both `|G|` (for `K = ⊤`): the conclusion has an
instance with positive counts.  Here `G = (ZMod 5)ˣ` written multiplicatively,
`x = 1`, `K = ⊤`. -/
example :
    Nat.card ↥(normalizerOf (1 : Multiplicative (ZMod 5)) ⊓ ⊤) =
      Nat.card ↥(solubilizerIn (1 : Multiplicative (ZMod 5)) ⊤) := by
  have hN : normalizerOf (1 : Multiplicative (ZMod 5)) ⊓ ⊤ = ⊤ := by
    have h : normalizerOf (1 : Multiplicative (ZMod 5)) = ⊤ := by
      unfold normalizerOf
      exact CommGroup.normalizer_eq_top _
    simp [h]
  have hS : solubilizerIn (1 : Multiplicative (ZMod 5)) ⊤ = Set.univ := by
    ext g
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    change Group.IsSolvable
      (Subgroup.closure ({(1 : Multiplicative (ZMod 5)),
        (g : Multiplicative (ZMod 5))} : Set (Multiplicative (ZMod 5))))
    have : IsMulCommutative
        (Subgroup.closure ({(1 : Multiplicative (ZMod 5)),
          (g : Multiplicative (ZMod 5))} : Set (Multiplicative (ZMod 5)))) :=
      Subgroup.isMulCommutative_closure (by
        intro a _ b _ _; exact mul_comm a b)
    infer_instance
  rw [hN, hS]
  simp

/-- For `K = ⊥` the two sides have cardinality `1`, so the statement is not
vacuous at the bottom either. -/
example :
    Nat.card ↥(normalizerOf (1 : Multiplicative (ZMod 5)) ⊓ ⊥) ∣
      Nat.card ↥(solubilizerIn (1 : Multiplicative (ZMod 5)) ⊥) := by
  have hN : normalizerOf (1 : Multiplicative (ZMod 5)) ⊓ ⊥ = ⊥ := by simp
  have hS : solubilizerIn (1 : Multiplicative (ZMod 5)) ⊥ = Set.univ := by
    ext g
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have hg : (g : Multiplicative (ZMod 5)) = 1 := Subgroup.mem_bot.mp g.2
    change Group.IsSolvable
      (Subgroup.closure ({(1 : Multiplicative (ZMod 5)),
        (g : Multiplicative (ZMod 5))} : Set (Multiplicative (ZMod 5))))
    rw [hg, show ({(1 : Multiplicative (ZMod 5)),
        (1 : Multiplicative (ZMod 5))} : Set (Multiplicative (ZMod 5))) = {1} by
      ext y; simp]
    exact isSolvable_closure_singleton 1
  rw [hN, hS]
  simp

end DsBatch.P14
