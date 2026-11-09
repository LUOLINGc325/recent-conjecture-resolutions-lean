import DsBatch.P14.Basic

/-!
# P14 — Counting cosets

If `S` is a union of right `T`-cosets in a group `G`, then `|S| = |T| * |S/T|`.
We apply this to the normalizer and to the solubilizer in the main induction.
-/

namespace DsBatch.P14

open scoped Pointwise

variable {G : Type*} [Group G]

/-- If `S` is a union of right `T`-cosets, then `|S| = |T| * |S/T|`. -/
theorem card_eq_card_mul_card_image {T : Subgroup G} [T.Normal] (S : Set G)
    (hS : ∀ s ∈ S, ∀ t : G, t ∈ T → s * t ∈ S) :
    Nat.card ↥S = Nat.card ↥T * Nat.card ↥(QuotientGroup.mk' T '' S) := by
  have hpre : QuotientGroup.mk ⁻¹' (QuotientGroup.mk' T '' S) = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hxs⟩ := hx
      have hmk : (↑s : G ⧸ T) = ↑x := by
        simpa [QuotientGroup.mk'_apply] using hxs
      have hmem : s⁻¹ * x ∈ T := QuotientGroup.eq.mp hmk
      have hx' : s * (s⁻¹ * x) = x := by group
      rw [← hx']
      exact hS s hs (s⁻¹ * x) hmem
    · intro hx
      exact ⟨x, hx, rfl⟩
  conv_lhs => rw [← hpre]
  exact QuotientGroup.card_preimage_mk T (QuotientGroup.mk' T '' S)

/-- The count of a subgroup `H` containing `T`, in terms of the quotient
`H/T` (realised as the image of `H` in `G/T`). -/
theorem card_eq_card_mul_card_map {T H : Subgroup G} [T.Normal] (hTH : T ≤ H) :
    Nat.card ↥H = Nat.card ↥T * Nat.card ↥(H.map (QuotientGroup.mk' T)) := by
  have hS : ∀ s ∈ (H : Set G), ∀ t : G, t ∈ T → s * t ∈ (H : Set G) := by
    intro s hs t ht
    exact H.mul_mem hs (hTH ht)
  have h := card_eq_card_mul_card_image (T := T) (S := (H : Set G)) hS
  have hgoal : Nat.card ↥(H.map (QuotientGroup.mk' T)) =
      Nat.card ↥(QuotientGroup.mk' T '' (H : Set G)) := rfl
  rw [hgoal]
  exact h

end DsBatch.P14
