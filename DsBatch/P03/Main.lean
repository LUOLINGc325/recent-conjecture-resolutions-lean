import DsBatch.P03.Statement

/-! Proofs for project P03, following the paper's §3 argument.

The proof is local to a rotation `((U,V),W) ↦ (U,(V,W))` inside an arbitrary
context `C`.  We show:

* `lab` of the rotation configuration is preserved by the context
  (`lab_fill_eq`, `lab_fill_eq_iff`);
* `f` is additive over contexts when the hole labels agree (`f_fill_add`);
* `d` is additive over contexts up to the (equal) incoming path-depth state at the
  hole (`d_fill_exists`);
* in the three label cases for the local configuration, either `f` changes or
  `d` changes (`local_f`, `local_d`).
-/

namespace DsBatch.P03

open OBT

/-! ### Elementary facts about `ZMod 2` -/

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by fin_cases x <;> decide

lemma zmod2_key (a b : ZMod 3) :
    (if a = 1 - a - b then (1 : ZMod 2) else 0) + (if a = b then (1 : ZMod 2) else 0)
      = if (1 - a - b) = b then (0 : ZMod 2) else 1 := by
  rcases (by decide : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2) a with rfl | rfl | rfl <;>
  rcases (by decide : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2) b with rfl | rfl | rfl <;>
  decide

lemma zmod2_parity_key (x : ZMod 2) :
    (if x = 0 then (1 : ZMod 2) else 0) + (if 1 + x = 0 then 1 else 0) = 1 := by
  fin_cases x <;> decide

/-! ### Context lemmas for the labels and the two statistics -/

lemma lab_fill_eq : ∀ (C : Ctx) (A B : OBT), lab A = lab B → lab (C.fill A) = lab (C.fill B)
  | Ctx.hole, A, B, h => h
  | Ctx.left C X, A, B, h => by
      have ih := lab_fill_eq C A B h
      simp only [Ctx.fill, lab]
      rw [ih]
  | Ctx.right X C, A, B, h => by
      have ih := lab_fill_eq C A B h
      simp only [Ctx.fill, lab]
      rw [ih]

lemma lab_fill_eq_iff : ∀ (C : Ctx) (A B : OBT),
    lab (C.fill A) = lab (C.fill B) → lab A = lab B
  | Ctx.hole, A, B, h => h
  | Ctx.left C X, A, B, h => by
      simp only [Ctx.fill, lab] at h
      exact lab_fill_eq_iff C A B (sub_right_inj.mp (sub_left_inj.mp h))
  | Ctx.right X C, A, B, h => by
      simp only [Ctx.fill, lab] at h
      exact lab_fill_eq_iff C A B (sub_right_inj.mp h)

lemma f_fill_add : ∀ (C : Ctx) (A B : OBT), lab A = lab B →
    f (C.fill A) + f (C.fill B) = f A + f B
  | Ctx.hole, A, B, h => by simp [Ctx.fill]
  | Ctx.left C X, A, B, h => by
      have hlab := lab_fill_eq C A B h
      have hnode : lab (node (C.fill A) X) = lab (node (C.fill B) X) := by
        simp only [lab]; rw [hlab]
      have hi : (if lab (C.fill A) = lab (node (C.fill A) X) then (1 : ZMod 2) else 0)
              = (if lab (C.fill B) = lab (node (C.fill B) X) then (1 : ZMod 2) else 0) := by
        rw [hlab, hnode]
      simp only [Ctx.fill, f]
      rw [hi]
      have ih := f_fill_add C A B h
      have hX : f X + f X = 0 := zmod2_add_self _
      have hI : (if lab (C.fill B) = lab (node (C.fill B) X) then (1 : ZMod 2) else 0)
              + (if lab (C.fill B) = lab (node (C.fill B) X) then (1 : ZMod 2) else 0) = 0 :=
        zmod2_add_self _
      calc f (C.fill A) + f X + (if lab (C.fill B) = lab (node (C.fill B) X) then 1 else 0)
              + (f (C.fill B) + f X + (if lab (C.fill B) = lab (node (C.fill B) X) then 1 else 0))
          = (f (C.fill A) + f (C.fill B)) + (f X + f X)
              + ((if lab (C.fill B) = lab (node (C.fill B) X) then (1 : ZMod 2) else 0)
                 + (if lab (C.fill B) = lab (node (C.fill B) X) then (1 : ZMod 2) else 0)) := by abel
        _ = (f A + f B) + 0 + 0 := by rw [ih, hX, hI]
        _ = f A + f B := by simp
  | Ctx.right X C, A, B, h => by
      have hlab := lab_fill_eq C A B h
      have hnode : lab (node X (C.fill A)) = lab (node X (C.fill B)) := by
        simp only [lab]; rw [hlab]
      have hi : (if lab X = lab (node X (C.fill A)) then (1 : ZMod 2) else 0)
              = (if lab X = lab (node X (C.fill B)) then (1 : ZMod 2) else 0) := by
        rw [hnode]
      simp only [Ctx.fill, f]
      rw [hi]
      have ih := f_fill_add C A B h
      have hX : f X + f X = 0 := zmod2_add_self _
      have hI : (if lab X = lab (node X (C.fill B)) then (1 : ZMod 2) else 0)
              + (if lab X = lab (node X (C.fill B)) then (1 : ZMod 2) else 0) = 0 :=
        zmod2_add_self _
      calc f X + f (C.fill A) + (if lab X = lab (node X (C.fill B)) then 1 else 0)
              + (f X + f (C.fill B) + (if lab X = lab (node X (C.fill B)) then 1 else 0))
          = (f (C.fill A) + f (C.fill B)) + (f X + f X)
              + ((if lab X = lab (node X (C.fill B)) then (1 : ZMod 2) else 0)
                 + (if lab X = lab (node X (C.fill B)) then (1 : ZMod 2) else 0)) := by abel
        _ = (f A + f B) + 0 + 0 := by rw [ih, hX, hI]
        _ = f A + f B := by simp

/-- `dAux T k false` does not depend on `k`: with a non-highlighted incoming edge
the path depth resets to `0`. -/
lemma dAux_false : ∀ (T : OBT) (k k' : ZMod 2), dAux T k false = dAux T k' false
  | leaf, _, _ => rfl
  | node l r, k, k' => by
      simp only [dAux]
      rfl

/-- Over a context, the `d` statistic is additive up to the path-depth state at the
hole, which is the same for both filled trees because their root labels agree. -/
lemma d_fill_exists : ∀ (C : Ctx) (A B : OBT), lab A = lab B → ∀ (k : ZMod 2) (e : Bool),
    ∃ (k' : ZMod 2) (e' : Bool),
      dAux (C.fill A) k e + dAux (C.fill B) k e = dAux A k' e' + dAux B k' e'
  | Ctx.hole, A, B, h, k, e => ⟨k, e, by simp [Ctx.fill]⟩
  | Ctx.left C X, A, B, h, k, e => by
      obtain ⟨k'', e'', ih⟩ := d_fill_exists C A B h (if e then 1 + k else 0)
        (lab (C.fill B) = lab (node (C.fill B) X))
      have hlab := lab_fill_eq C A B h
      have hnode : lab (node (C.fill A) X) = lab (node (C.fill B) X) := by
        simp only [lab]; rw [hlab]
      have heL : (lab (C.fill A) = lab (node (C.fill A) X))
               = (lab (C.fill B) = lab (node (C.fill B) X)) := by rw [hlab, hnode]
      have heR : (lab X = lab (node (C.fill A) X)) = (lab X = lab (node (C.fill B) X)) := by
        rw [hnode]
      refine ⟨k'', e'', ?_⟩
      simp only [Ctx.fill, dAux]
      simp only [heL, heR]
      have h2 : (2 : ZMod 2) = 0 := by decide
      ring_nf
      simp only [h2, mul_zero, add_zero]
      rw [ih]
  | Ctx.right X C, A, B, h, k, e => by
      have hlab := lab_fill_eq C A B h
      have hnode : lab (node X (C.fill A)) = lab (node X (C.fill B)) := by
        simp only [lab]; rw [hlab]
      have heL : (lab X = lab (node X (C.fill A))) = (lab X = lab (node X (C.fill B))) := by
        rw [hnode]
      have heR : (lab (C.fill A) = lab (node X (C.fill A)))
               = (lab (C.fill B) = lab (node X (C.fill B))) := by rw [hlab, hnode]
      obtain ⟨k'', e'', ih⟩ := d_fill_exists C A B h (if e then 1 + k else 0)
        (lab (C.fill B) = lab (node X (C.fill B)))
      refine ⟨k'', e'', ?_⟩
      simp only [Ctx.fill, dAux]
      simp only [heL, heR]
      have h2 : (2 : ZMod 2) = 0 := by decide
      ring_nf
      simp only [h2, mul_zero, add_zero, zero_add]
      rw [ih]

/-! ### The local configuration `((U,V),W) ↦ (U,(V,W))` -/

lemma lab_rot_sub (U V W : OBT) :
    lab (node (node U V) W) - lab (node U (node V W)) = 2 * (lab U - lab W) := by
  simp only [lab]; ring

/-- A rotation preserves the root label, and in fact forces `lab W = lab U`. -/
lemma local_lab_WU (U V W : OBT)
    (h : lab (node (node U V) W) = lab (node U (node V W))) : lab W = lab U := by
  have h' : lab (node (node U V) W) - lab (node U (node V W)) = 0 := sub_eq_zero.mpr h
  rw [lab_rot_sub] at h'
  have h2ne : (2 : ZMod 3) ≠ 0 := by decide
  rcases mul_eq_zero.mp h' with h2 | h0
  · exact absurd h2 h2ne
  · exact (sub_eq_zero.mp h0).symm

/-- Under a label-preserving rotation the common root label is `lab V`. -/
lemma local_lab_root (U V W : OBT)
    (h : lab (node (node U V) W) = lab (node U (node V W))) :
    lab (node (node U V) W) = lab V := by
  have hc := local_lab_WU U V W h
  simp only [lab]; rw [hc]; ring

/-- In the local rotation, the `f` statistic changes by `1` unless the labels of
`node U V` and `V` agree. -/
lemma local_f (U V W : OBT)
    (h : lab (node (node U V) W) = lab (node U (node V W))) :
    f (node (node U V) W) + f (node U (node V W))
      = if lab (node U V) = lab V then 0 else 1 := by
  have hWU := local_lab_WU U V W h
  have hroot := local_lab_root U V W h
  have hB : lab (node U (node V W)) = lab V := h.symm.trans hroot
  have hVW : lab (node V W) = lab (node U V) := by simp only [lab]; rw [hWU]; ring
  have hcond : (lab V = lab (node V W)) = (lab (node U V) = lab V) := by
    rw [hVW]
    exact propext eq_comm
  simp only [f]
  simp only [hroot, hB, hcond]
  set I1 : ZMod 2 := (if U.lab = (U.node V).lab then 1 else 0) with hI1
  set I : ZMod 2 := (if (U.node V).lab = V.lab then 1 else 0) with hI
  set I4 : ZMod 2 := (if U.lab = V.lab then 1 else 0) with hI4
  have h2 : (2 : ZMod 2) = 0 := by decide
  ring_nf
  simp only [h2, mul_zero, add_zero, zero_add]
  rw [hI1, hI4]
  exact zmod2_key U.lab V.lab

/-- In the remaining local case `lab (node U V) = lab V`, the `d` statistic
changes by `1`, for every incoming path-depth state. -/
lemma local_d (U V W : OBT)
    (h : lab (node (node U V) W) = lab (node U (node V W)))
    (hp : lab (node U V) = lab V) (k : ZMod 2) (e : Bool) :
    dAux (node (node U V) W) k e + dAux (node U (node V W)) k e = 1 := by
  have hWU := local_lab_WU U V W h
  have hroot := local_lab_root U V W h
  have hB : lab (node U (node V W)) = lab V := h.symm.trans hroot
  have hVW : lab (node V W) = lab (node U V) := by simp only [lab]; rw [hWU]; ring
  have hne : lab U ≠ lab V := by
    have hk : ∀ a b : ZMod 3, 1 - a - b = b → a ≠ b := by decide
    exact hk (lab U) (lab V) hp
  have hneW : lab W ≠ lab V := by rw [hWU]; exact hne
  simp only [dAux]
  simp only [hroot, hB, hp, hVW, hWU, hne]
  simp only [decide_eq_true_eq, decide_false, true_and, false_and, ite_true, ite_false,
    Bool.false_eq_true]
  have hU : dAux U ((if e then k + 1 else 0) + 1) false = dAux U (if e then k + 1 else 0) false :=
    dAux_false U _ _
  have hW : dAux W (if e then k + 1 else 0) false = dAux W ((if e then k + 1 else 0) + 1) false :=
    dAux_false W _ _
  rw [hU, hW]
  have h2 : (2 : ZMod 2) = 0 := by decide
  ring_nf
  simp only [h2, mul_zero, add_zero, zero_add]
  exact zmod2_parity_key (if e then 1 + k else 0)

/-! ### The main theorem -/

/-- A single forward rotation changes `κ`. -/
lemma rotFwd_kappa_ne (T T' : OBT) (hrot : RotFwd T T') : kappa T ≠ kappa T' := by
  rintro hκ
  rcases hrot with ⟨C, U, V, W, hT, hT'⟩
  have hlab : lab T = lab T' := congrArg Prod.fst hκ
  have hf : f T = f T' := congrArg (fun x => x.2.1) hκ
  have hd : d T = d T' := congrArg (fun x => x.2.2) hκ
  rw [hT, hT'] at hlab
  have hAB : lab (node (node U V) W) = lab (node U (node V W)) :=
    lab_fill_eq_iff C _ _ hlab
  by_cases hp : lab (node U V) = lab V
  · -- the label case where `d` changes
    have hdsum : dAux (C.fill (node (node U V) W)) 0 false
        + dAux (C.fill (node U (node V W))) 0 false = 1 := by
      obtain ⟨k', e', hk⟩ := d_fill_exists C _ _ hAB 0 false
      rw [hk]
      exact local_d U V W hAB hp k' e'
    have hdsumT : d T + d T' = 1 := by
      rw [hT, hT']
      exact hdsum
    have hdzero : d T + d T' = 0 := by
      rw [hd]
      exact zmod2_add_self (d T')
    rw [hdsumT] at hdzero
    exact one_ne_zero hdzero
  · -- the label cases where `f` changes
    have hfsum : f (C.fill (node (node U V) W)) + f (C.fill (node U (node V W))) = 1 := by
      rw [f_fill_add C _ _ hAB]
      rw [local_f U V W hAB]
      simp [hp]
    have hfsumT : f T + f T' = 1 := by
      rw [hT, hT']
      exact hfsum
    have hfzero : f T + f T' = 0 := by
      rw [hf]
      exact zmod2_add_self (f T')
    rw [hfsumT] at hfzero
    exact one_ne_zero hfzero

/-- The explicit colouring `κ` is proper on every associahedron. -/
theorem kappa_proper : kappa_proper_statement := by
  intro n hn T T' hrot
  rcases hrot with h | h
  · exact rotFwd_kappa_ne T.1 T'.1 h
  · intro hκ
    exact rotFwd_kappa_ne T'.1 T.1 h hκ.symm

/-- The chromatic number of every associahedron is at most 12. -/
theorem chromaticNumber_le_twelve : chromaticNumber_le_twelve_statement := by
  intro n hn
  have hcard : Fintype.card (ZMod 3 × ZMod 2 × ZMod 2) = 12 := by decide
  let e : (ZMod 3 × ZMod 2 × ZMod 2) ≃ Fin 12 := Fintype.equivFinOfCardEq hcard
  have hcol : (associahedron n).Coloring (Fin 12) :=
    SimpleGraph.Coloring.mk (fun T => e (kappa T.1)) (by
      intro T T' hAdj hEq
      exact kappa_proper n hn T T' hAdj (e.injective hEq))
  exact SimpleGraph.Colorable.chromaticNumber_le ⟨hcol⟩

end DsBatch.P03
