import DsBatch.P14.Statement

/-! Foundational lemmas for project P14 (conjugation by the normalizer,
    solubility transport, identity in the solubilizer). -/

namespace DsBatch.P14

universe u

variable {G : Type u} [Group G]

/-! ## Conjugation by the normalizer preserves solubility -/

/-- If `h` normalizes `⟨x⟩`, then `h * x * h⁻¹` still lies in `⟨x⟩`. -/
lemma conj_mem_cyclicSubgroup {x h : G} (hh : h ∈ normalizerOf x) :
    h * x * h⁻¹ ∈ cyclicSubgroup x := by
  have hh' : h ∈ Subgroup.normalizer ((cyclicSubgroup x : Subgroup G) : Set G) := hh
  exact (Subgroup.mem_normalizer_iff.mp hh' x).mp
    (Subgroup.subset_closure (by simp))

/-- If `h` normalizes `⟨x⟩`, conjugation by `h` maps `⟨x⟩` to itself. -/
lemma map_conj_cyclicSubgroup {x h : G} (hh : h ∈ normalizerOf x) :
    Subgroup.map (MulAut.conj h) (cyclicSubgroup x) = cyclicSubgroup x := by
  have hh' : h ∈ Subgroup.normalizer ((cyclicSubgroup x : Subgroup G) : Set G) := hh
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hh'

/-- Conjugating a two-generator subgroup `⟨x, a⟩` by an element `h` of the
normalizer of `⟨x⟩` yields `⟨x, h a h⁻¹⟩`; hence solubility is preserved. -/
lemma isSolvable_closure_pair_conj {x h a : G} (hh : h ∈ normalizerOf x)
    (ha : Group.IsSolvable (Subgroup.closure ({x, a} : Set G))) :
    Group.IsSolvable (Subgroup.closure ({x, h * a * h⁻¹} : Set G)) := by
  classical
  have hhinv : h⁻¹ ∈ normalizerOf x := (normalizerOf x).inv_mem hh
  have hcx : h⁻¹ * x * h ∈ cyclicSubgroup x := by
    simpa using conj_mem_cyclicSubgroup hhinv
  -- conjugation by `h⁻¹` maps the target closure to a subgroup of `⟨x,a⟩`
  -- conjugation by `h` maps `⟨h⁻¹ x h, a⟩` onto `⟨x, h a h⁻¹⟩`
  have himage : ((MulAut.conj h) : G → G) '' ({h⁻¹ * x * h, a} : Set G)
      = ({x, h * a * h⁻¹} : Set G) := by
    ext y
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with hz | hz
      · left
        rw [hz, MulAut.conj_apply]
        group
      · right
        rw [hz, MulAut.conj_apply]
    · intro hy
      rcases hy with hy | hy
      · rw [hy]
        refine ⟨h⁻¹ * x * h, Or.inl rfl, ?_⟩
        rw [MulAut.conj_apply]
        group
      · rw [hy]
        refine ⟨a, Or.inr rfl, ?_⟩
        rw [MulAut.conj_apply]
  have hmap : Subgroup.map (MulAut.conj h).toMonoidHom
      (Subgroup.closure ({h⁻¹ * x * h, a} : Set G))
      = Subgroup.closure ({x, h * a * h⁻¹} : Set G) := by
    have := MonoidHom.map_closure (MulAut.conj h).toMonoidHom
      ({h⁻¹ * x * h, a} : Set G)
    simpa [himage] using this
  have hle : Subgroup.closure ({h⁻¹ * x * h, a} : Set G) ≤
      Subgroup.closure ({x, a} : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with hy | hy
    · rw [hy]
      exact Subgroup.closure_mono
        (by intro z hz
            exact Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hz))) hcx
    · rw [hy]
      exact Subgroup.subset_closure (by simp)
  have hVU : Group.IsSolvable ↥(Subgroup.closure ({h⁻¹ * x * h, a} : Set G)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  -- conjugation is a surjection from `⟨h⁻¹ x h, a⟩` onto `⟨x, h a h⁻¹⟩`
  let f : ↥(Subgroup.closure ({h⁻¹ * x * h, a} : Set G)) →*
      ↥(Subgroup.closure ({x, h * a * h⁻¹} : Set G)) :=
    MonoidHom.codRestrict
      ((MulAut.conj h).toMonoidHom.comp (Subgroup.subtype _)) _
      (fun y => by
        have hmem : (MulAut.conj h) (y : G) ∈
            Subgroup.map (MulAut.conj h).toMonoidHom
              (Subgroup.closure ({h⁻¹ * x * h, a} : Set G)) :=
          Subgroup.mem_map_of_mem _ y.2
        rwa [hmap] at hmem)
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : G) ∈ Subgroup.map (MulAut.conj h).toMonoidHom
        (Subgroup.closure ({h⁻¹ * x * h, a} : Set G)) := by
      rw [hmap]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  exact Group.isSolvable_of_surjective (f := f) hf

/-- The solubilizer is invariant under conjugation by the normalizer of `⟨x⟩`. -/
lemma solubilizerIn_conj_mem {x : G} {K : Subgroup G} {h : K}
    (hh : (h : G) ∈ normalizerOf x) {a : K} (ha : a ∈ solubilizerIn x K) :
    (h * a * h⁻¹ : K) ∈ solubilizerIn x K := by
  have hha : Group.IsSolvable (Subgroup.closure ({x, (a : G)} : Set G)) := ha
  have hsol := isSolvable_closure_pair_conj hh hha
  change Group.IsSolvable (Subgroup.closure ({x, ((h * a * h⁻¹ : K) : G)} : Set G))
  simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hsol

/-- The identity belongs to every solubilizer intersection. -/
lemma one_mem_solubilizerIn (x : G) (K : Subgroup G) : (1 : K) ∈ solubilizerIn x K := by
  have h : Group.IsSolvable (Subgroup.closure ({x} : Set G)) := by
    rw [← Subgroup.zpowers_eq_closure]
    have : IsMulCommutative (Subgroup.zpowers x) := Subgroup.zpowers_isMulCommutative x
    infer_instance
  unfold solubilizerIn
  change Group.IsSolvable (Subgroup.closure ({x, (1 : G)} : Set G))
  rw [show ({x, (1 : G)} : Set G) = {x} ∪ {1} by
    ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
  rw [Subgroup.closure_union_one]
  exact h

end DsBatch.P14
