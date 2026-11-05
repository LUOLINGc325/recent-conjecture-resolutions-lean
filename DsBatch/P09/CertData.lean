import DsBatch.P09.Statement

/-!
# P09 — computational certificate

This file contains the data and the kernel-checked computations used in the
proof of `four_edge` and `gamma_eq_six`:

* an indexing `eOf : Fin 27 → Sym2 V` of the 27 edges of the paper's graph;
* a family of 55 dominating 6-sets of `G` together with, for every vertex `x`
  outside the set, the list of indices of the edges from `x` into the set;
* a family of `go`-enumerations of `k`-element subsets, with kernel-checked
  proofs that
  - every 4-element set of edge indices is avoided by one of the 55 sets
    (`check4`), and
  - no 5-element set of vertices dominates `G` (`check5`).

Nothing here is `sorry`-free by accident: no `sorry`/`axiom`/`native_decide`
appears in this file; all computations are kernel `decide` checks.
-/

namespace DsBatch.P09

open SimpleGraph

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! ## Indexing the 27 edges -/

/-- First endpoint of the `i`-th edge of the paper's list. -/
def e1 : Fin 27 → V :=
  ![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 5, 6, 6, 7, 7, 8, 9, 9, 10, 11, 12, 12, 14, 16]

/-- Second endpoint of the `i`-th edge of the paper's list. -/
def e2 : Fin 27 → V :=
  ![6, 10, 16, 8, 11, 12, 4, 5, 13, 4, 5, 9, 16, 11, 7, 13, 8, 14, 13, 10, 14, 15, 15, 15, 17, 17, 17]

/-- The `i`-th edge of `G`, as an unordered pair. -/
def eOf (i : Fin 27) : Sym2 V := s(e1 i, e2 i)

lemma eOf_mem : ∀ i : Fin 27, eOf i ∈ G.edgeSet := by
  decide

lemma eOf_inj : Function.Injective eOf := by
  decide

lemma eOf_surj : ∀ e ∈ G.edgeSet, ∃ i, eOf i = e := by
  decide

lemma range_eOf : Set.range eOf = G.edgeSet := by
  ext e
  constructor
  · rintro ⟨i, rfl⟩
    exact eOf_mem i
  · intro he
    exact eOf_surj e he

/-- The index of an edge of `G` (junk value `0` off the edge set). -/
noncomputable def idx (e : Sym2 V) : Fin 27 :=
  if h : ∃ i, eOf i = e then Classical.choose h else 0

lemma idx_eOf (i : Fin 27) : idx (eOf i) = i := by
  have h : ∃ j, eOf j = eOf i := ⟨i, rfl⟩
  simp only [idx, dif_pos h]
  exact eOf_inj (Classical.choose_spec h)

lemma eOf_idx {e : Sym2 V} (he : e ∈ G.edgeSet) : eOf (idx e) = e := by
  have h : ∃ i, eOf i = e := eOf_surj e he
  simp only [idx, dif_pos h]
  exact Classical.choose_spec h

/-! ## The certificate family -/

/-- One certificate: a set `D` of six vertices, and for each vertex `x` outside
`D` a complete list of the indices of the edges from `x` into `D`. -/
structure Cert where
  D : Finset V
  bundles : List (V × List (Fin 27))

/-- The 55 dominating 6-sets (a greedy cover of all 17550 four-edge sets by the
minimum dominating sets of `G`). -/
def certs : List Cert := [
  { D := {0, 1, 2, 3, 14, 15}, bundles := [(4, ([6, 9] : List (Fin 27))), (5, ([7, 10] : List (Fin 27))), (6, ([0] : List (Fin 27))), (7, ([17] : List (Fin 27))), (8, ([3] : List (Fin 27))), (9, ([11, 20] : List (Fin 27))), (10, ([1, 21] : List (Fin 27))), (11, ([4, 22] : List (Fin 27))), (12, ([5, 23] : List (Fin 27))), (13, ([8] : List (Fin 27))), (16, ([2] : List (Fin 27))), (17, ([25] : List (Fin 27)))] },
  { D := {4, 7, 10, 11, 13, 17}, bundles := [(0, ([1] : List (Fin 27))), (1, ([4] : List (Fin 27))), (2, ([6, 8] : List (Fin 27))), (3, ([9] : List (Fin 27))), (5, ([13] : List (Fin 27))), (6, ([14, 15] : List (Fin 27))), (8, ([16, 18] : List (Fin 27))), (9, ([19] : List (Fin 27))), (12, ([24] : List (Fin 27))), (14, ([17, 25] : List (Fin 27))), (15, ([21, 22] : List (Fin 27))), (16, ([12, 26] : List (Fin 27)))] },
  { D := {5, 6, 8, 9, 15, 16}, bundles := [(0, ([0, 2] : List (Fin 27))), (1, ([3] : List (Fin 27))), (2, ([7] : List (Fin 27))), (3, ([10, 11] : List (Fin 27))), (4, ([12] : List (Fin 27))), (7, ([14, 16] : List (Fin 27))), (10, ([19, 21] : List (Fin 27))), (11, ([13, 22] : List (Fin 27))), (12, ([23] : List (Fin 27))), (13, ([15, 18] : List (Fin 27))), (14, ([20] : List (Fin 27))), (17, ([26] : List (Fin 27)))] },
  { D := {0, 2, 7, 9, 11, 12}, bundles := [(1, ([4, 5] : List (Fin 27))), (3, ([11] : List (Fin 27))), (4, ([6] : List (Fin 27))), (5, ([7, 13] : List (Fin 27))), (6, ([0, 14] : List (Fin 27))), (8, ([16] : List (Fin 27))), (10, ([1, 19] : List (Fin 27))), (13, ([8] : List (Fin 27))), (14, ([17, 20] : List (Fin 27))), (15, ([22, 23] : List (Fin 27))), (16, ([2] : List (Fin 27))), (17, ([24] : List (Fin 27)))] },
  { D := {1, 5, 10, 13, 14, 16}, bundles := [(0, ([1, 2] : List (Fin 27))), (2, ([7, 8] : List (Fin 27))), (3, ([10] : List (Fin 27))), (4, ([12] : List (Fin 27))), (6, ([15] : List (Fin 27))), (7, ([17] : List (Fin 27))), (8, ([3, 18] : List (Fin 27))), (9, ([19, 20] : List (Fin 27))), (11, ([4, 13] : List (Fin 27))), (12, ([5] : List (Fin 27))), (15, ([21] : List (Fin 27))), (17, ([25, 26] : List (Fin 27)))] },
  { D := {0, 2, 3, 8, 15, 17}, bundles := [(1, ([3] : List (Fin 27))), (4, ([6, 9] : List (Fin 27))), (5, ([7, 10] : List (Fin 27))), (6, ([0] : List (Fin 27))), (7, ([16] : List (Fin 27))), (9, ([11] : List (Fin 27))), (10, ([1, 21] : List (Fin 27))), (11, ([22] : List (Fin 27))), (12, ([23, 24] : List (Fin 27))), (13, ([8, 18] : List (Fin 27))), (14, ([25] : List (Fin 27))), (16, ([2, 26] : List (Fin 27)))] },
  { D := {1, 4, 5, 6, 10, 17}, bundles := [(0, ([0, 1] : List (Fin 27))), (2, ([6, 7] : List (Fin 27))), (3, ([9, 10] : List (Fin 27))), (7, ([14] : List (Fin 27))), (8, ([3] : List (Fin 27))), (9, ([19] : List (Fin 27))), (11, ([4, 13] : List (Fin 27))), (12, ([5, 24] : List (Fin 27))), (13, ([15] : List (Fin 27))), (14, ([25] : List (Fin 27))), (15, ([21] : List (Fin 27))), (16, ([12, 26] : List (Fin 27)))] },
  { D := {0, 4, 5, 8, 12, 14}, bundles := [(1, ([3, 5] : List (Fin 27))), (2, ([6, 7] : List (Fin 27))), (3, ([9, 10] : List (Fin 27))), (6, ([0] : List (Fin 27))), (7, ([16, 17] : List (Fin 27))), (9, ([20] : List (Fin 27))), (10, ([1] : List (Fin 27))), (11, ([13] : List (Fin 27))), (13, ([18] : List (Fin 27))), (15, ([23] : List (Fin 27))), (16, ([2, 12] : List (Fin 27))), (17, ([24, 25] : List (Fin 27)))] },
  { D := {1, 2, 7, 9, 15, 16}, bundles := [(0, ([2] : List (Fin 27))), (3, ([11] : List (Fin 27))), (4, ([6, 12] : List (Fin 27))), (5, ([7] : List (Fin 27))), (6, ([14] : List (Fin 27))), (8, ([3, 16] : List (Fin 27))), (10, ([19, 21] : List (Fin 27))), (11, ([4, 22] : List (Fin 27))), (12, ([5, 23] : List (Fin 27))), (13, ([8] : List (Fin 27))), (14, ([17, 20] : List (Fin 27))), (17, ([26] : List (Fin 27)))] },
  { D := {4, 6, 8, 9, 11, 17}, bundles := [(0, ([0] : List (Fin 27))), (1, ([3, 4] : List (Fin 27))), (2, ([6] : List (Fin 27))), (3, ([9, 11] : List (Fin 27))), (5, ([13] : List (Fin 27))), (7, ([14, 16] : List (Fin 27))), (10, ([19] : List (Fin 27))), (12, ([24] : List (Fin 27))), (13, ([15, 18] : List (Fin 27))), (14, ([20, 25] : List (Fin 27))), (15, ([22] : List (Fin 27))), (16, ([12, 26] : List (Fin 27)))] },
  { D := {0, 3, 11, 12, 13, 14}, bundles := [(1, ([4, 5] : List (Fin 27))), (2, ([8] : List (Fin 27))), (4, ([9] : List (Fin 27))), (5, ([10, 13] : List (Fin 27))), (6, ([0, 15] : List (Fin 27))), (7, ([17] : List (Fin 27))), (8, ([18] : List (Fin 27))), (9, ([11, 20] : List (Fin 27))), (10, ([1] : List (Fin 27))), (15, ([22, 23] : List (Fin 27))), (16, ([2] : List (Fin 27))), (17, ([24, 25] : List (Fin 27)))] },
  { D := {5, 7, 9, 12, 13, 16}, bundles := [(0, ([2] : List (Fin 27))), (1, ([5] : List (Fin 27))), (2, ([7, 8] : List (Fin 27))), (3, ([10, 11] : List (Fin 27))), (4, ([12] : List (Fin 27))), (6, ([14, 15] : List (Fin 27))), (8, ([16, 18] : List (Fin 27))), (10, ([19] : List (Fin 27))), (11, ([13] : List (Fin 27))), (14, ([17, 20] : List (Fin 27))), (15, ([23] : List (Fin 27))), (17, ([24, 26] : List (Fin 27)))] },
  { D := {1, 2, 3, 6, 10, 17}, bundles := [(0, ([0, 1] : List (Fin 27))), (4, ([6, 9] : List (Fin 27))), (5, ([7, 10] : List (Fin 27))), (7, ([14] : List (Fin 27))), (8, ([3] : List (Fin 27))), (9, ([11, 19] : List (Fin 27))), (11, ([4] : List (Fin 27))), (12, ([5, 24] : List (Fin 27))), (13, ([8, 15] : List (Fin 27))), (14, ([25] : List (Fin 27))), (15, ([21] : List (Fin 27))), (16, ([26] : List (Fin 27)))] },
  { D := {4, 6, 8, 10, 11, 17}, bundles := [(0, ([0, 1] : List (Fin 27))), (1, ([3, 4] : List (Fin 27))), (2, ([6] : List (Fin 27))), (3, ([9] : List (Fin 27))), (5, ([13] : List (Fin 27))), (7, ([14, 16] : List (Fin 27))), (9, ([19] : List (Fin 27))), (12, ([24] : List (Fin 27))), (13, ([15, 18] : List (Fin 27))), (14, ([25] : List (Fin 27))), (15, ([21, 22] : List (Fin 27))), (16, ([12, 26] : List (Fin 27)))] },
  { D := {7, 9, 11, 12, 13, 16}, bundles := [(0, ([2] : List (Fin 27))), (1, ([4, 5] : List (Fin 27))), (2, ([8] : List (Fin 27))), (3, ([11] : List (Fin 27))), (4, ([12] : List (Fin 27))), (5, ([13] : List (Fin 27))), (6, ([14, 15] : List (Fin 27))), (8, ([16, 18] : List (Fin 27))), (10, ([19] : List (Fin 27))), (14, ([17, 20] : List (Fin 27))), (15, ([22, 23] : List (Fin 27))), (17, ([24, 26] : List (Fin 27)))] },
  { D := {0, 4, 5, 8, 14, 15}, bundles := [(1, ([3] : List (Fin 27))), (2, ([6, 7] : List (Fin 27))), (3, ([9, 10] : List (Fin 27))), (6, ([0] : List (Fin 27))), (7, ([16, 17] : List (Fin 27))), (9, ([20] : List (Fin 27))), (10, ([1, 21] : List (Fin 27))), (11, ([13, 22] : List (Fin 27))), (12, ([23] : List (Fin 27))), (13, ([18] : List (Fin 27))), (16, ([2, 12] : List (Fin 27))), (17, ([25] : List (Fin 27)))] },
  { D := {0, 2, 8, 9, 15, 17}, bundles := [(1, ([3] : List (Fin 27))), (3, ([11] : List (Fin 27))), (4, ([6] : List (Fin 27))), (5, ([7] : List (Fin 27))), (6, ([0] : List (Fin 27))), (7, ([16] : List (Fin 27))), (10, ([1, 19, 21] : List (Fin 27))), (11, ([22] : List (Fin 27))), (12, ([23, 24] : List (Fin 27))), (13, ([8, 18] : List (Fin 27))), (14, ([20, 25] : List (Fin 27))), (16, ([2, 26] : List (Fin 27)))] },
  { D := {0, 4, 8, 9, 11, 17}, bundles := [(1, ([3, 4] : List (Fin 27))), (2, ([6] : List (Fin 27))), (3, ([9, 11] : List (Fin 27))), (5, ([13] : List (Fin 27))), (6, ([0] : List (Fin 27))), (7, ([16] : List (Fin 27))), (10, ([1, 19] : List (Fin 27))), (12, ([24] : List (Fin 27))), (13, ([18] : List (Fin 27))), (14, ([20, 25] : List (Fin 27))), (15, ([22] : List (Fin 27))), (16, ([2, 12, 26] : List (Fin 27)))] },
  { D := {0, 2, 7, 9, 11, 17}, bundles := [(1, ([4] : List (Fin 27))), (3, ([11] : List (Fin 27))), (4, ([6] : List (Fin 27))), (5, ([7, 13] : List (Fin 27))), (6, ([0, 14] : List (Fin 27))), (8, ([16] : List (Fin 27))), (10, ([1, 19] : List (Fin 27))), (12, ([24] : List (Fin 27))), (13, ([8] : List (Fin 27))), (14, ([17, 20, 25] : List (Fin 27))), (15, ([22] : List (Fin 27))), (16, ([2, 26] : List (Fin 27)))] },
  { D := {1, 5, 13, 14, 15, 16}, bundles := [(0, ([2] : List (Fin 27))), (2, ([7, 8] : List (Fin 27))), (3, ([10] : List (Fin 27))), (4, ([12] : List (Fin 27))), (6, ([15] : List (Fin 27))), (7, ([17] : List (Fin 27))), (8, ([3, 18] : List (Fin 27))), (9, ([20] : List (Fin 27))), (10, ([21] : List (Fin 27))), (11, ([4, 13, 22] : List (Fin 27))), (12, ([5, 23] : List (Fin 27))), (17, ([25, 26] : List (Fin 27)))] },
  { D := {1, 5, 6, 10, 14, 16}, bundles := [(0, ([0, 1, 2] : List (Fin 27))), (2, ([7] : List (Fin 27))), (3, ([10] : List (Fin 27))), (4, ([12] : List (Fin 27))), (7, ([14, 17] : List (Fin 27))), (8, ([3] : List (Fin 27))), (9, ([19, 20] : List (Fin 27))), (11, ([4, 13] : List (Fin 27))), (12, ([5] : List (Fin 27))), (13, ([15] : List (Fin 27))), (15, ([21] : List (Fin 27))), (17, ([25, 26] : List (Fin 27)))] },
  { D := {0, 2, 3, 8, 11, 17}, bundles := [(1, ([3, 4] : List (Fin 27))), (4, ([6, 9] : List (Fin 27))), (5, ([7, 10, 13] : List (Fin 27))), (6, ([0] : List (Fin 27))), (7, ([16] : List (Fin 27))), (9, ([11] : List (Fin 27))), (10, ([1] : List (Fin 27))), (12, ([24] : List (Fin 27))), (13, ([8, 18] : List (Fin 27))), (14, ([25] : List (Fin 27))), (15, ([22] : List (Fin 27))), (16, ([2, 26] : List (Fin 27)))] },
  { D := {1, 3, 10, 13, 14, 16}, bundles := [(0, ([1, 2] : List (Fin 27))), (2, ([8] : List (Fin 27))), (4, ([9, 12] : List (Fin 27))), (5, ([10] : List (Fin 27))), (6, ([15] : List (Fin 27))), (7, ([17] : List (Fin 27))), (8, ([3, 18] : List (Fin 27))), (9, ([11, 19, 20] : List (Fin 27))), (11, ([4] : List (Fin 27))), (12, ([5] : List (Fin 27))), (15, ([21] : List (Fin 27))), (17, ([25, 26] : List (Fin 27)))] },
  { D := {5, 10, 12, 13, 14, 16}, bundles := [(0, ([1, 2] : List (Fin 27))), (1, ([5] : List (Fin 27))), (2, ([7, 8] : List (Fin 27))), (3, ([10] : List (Fin 27))), (4, ([12] : List (Fin 27))), (6, ([15] : List (Fin 27))), (7, ([17] : List (Fin 27))), (8, ([18] : List (Fin 27))), (9, ([19, 20] : List (Fin 27))), (11, ([13] : List (Fin 27))), (15, ([21, 23] : List (Fin 27))), (17, ([24, 25, 26] : List (Fin 27)))] },
  { D := {0, 2, 8, 9, 11, 12}, bundles := [(1, ([3, 4, 5] : List (Fin 27))), (3, ([11] : List (Fin 27))), (4, ([6] : List (Fin 27))), (5, ([7, 13] : List (Fin 27))), (6, ([0] : List (Fin 27))), (7, ([16] : List (Fin 27))), (10, ([1, 19] : List (Fin 27))), (13, ([8, 18] : List (Fin 27))), (14, ([20] : List (Fin 27))), (15, ([22, 23] : List (Fin 27))), (16, ([2] : List (Fin 27))), (17, ([24] : List (Fin 27)))] },
  { D := {0, 4, 5, 12, 13, 14}, bundles := [(1, ([5] : List (Fin 27))), (2, ([6, 7, 8] : List (Fin 27))), (3, ([9, 10] : List (Fin 27))), (6, ([0, 15] : List (Fin 27))), (7, ([17] : List (Fin 27))), (8, ([18] : List (Fin 27))), (9, ([20] : List (Fin 27))), (10, ([1] : List (Fin 27))), (11, ([13] : List (Fin 27))), (15, ([23] : List (Fin 27))), (16, ([2, 12] : List (Fin 27))), (17, ([24, 25] : List (Fin 27)))] },
  { D := {1, 4, 5, 10, 13, 14}, bundles := [(0, ([1] : List (Fin 27))), (2, ([6, 7, 8] : List (Fin 27))), (3, ([9, 10] : List (Fin 27))), (6, ([15] : List (Fin 27))), (7, ([17] : List (Fin 27))), (8, ([3, 18] : List (Fin 27))), (9, ([19, 20] : List (Fin 27))), (11, ([4, 13] : List (Fin 27))), (12, ([5] : List (Fin 27))), (15, ([21] : List (Fin 27))), (16, ([12] : List (Fin 27))), (17, ([25] : List (Fin 27)))] },
  { D := {0, 4, 5, 8, 9, 12}, bundles := [(1, ([3, 5] : List (Fin 27))), (2, ([6, 7] : List (Fin 27))), (3, ([9, 10, 11] : List (Fin 27))), (6, ([0] : List (Fin 27))), (7, ([16] : List (Fin 27))), (10, ([1, 19] : List (Fin 27))), (11, ([13] : List (Fin 27))), (13, ([18] : List (Fin 27))), (14, ([20] : List (Fin 27))), (15, ([23] : List (Fin 27))), (16, ([2, 12] : List (Fin 27))), (17, ([24] : List (Fin 27)))] },
  { D := {1, 5, 7, 10, 13, 16}, bundles := [(0, ([1, 2] : List (Fin 27))), (2, ([7, 8] : List (Fin 27))), (3, ([10] : List (Fin 27))), (4, ([12] : List (Fin 27))), (6, ([14, 15] : List (Fin 27))), (8, ([3, 16, 18] : List (Fin 27))), (9, ([19] : List (Fin 27))), (11, ([4, 13] : List (Fin 27))), (12, ([5] : List (Fin 27))), (14, ([17] : List (Fin 27))), (15, ([21] : List (Fin 27))), (17, ([26] : List (Fin 27)))] },
  { D := {2, 6, 8, 9, 11, 17}, bundles := [(0, ([0] : List (Fin 27))), (1, ([3, 4] : List (Fin 27))), (3, ([11] : List (Fin 27))), (4, ([6] : List (Fin 27))), (5, ([7, 13] : List (Fin 27))), (7, ([14, 16] : List (Fin 27))), (10, ([19] : List (Fin 27))), (12, ([24] : List (Fin 27))), (13, ([8, 15, 18] : List (Fin 27))), (14, ([20, 25] : List (Fin 27))), (15, ([22] : List (Fin 27))), (16, ([26] : List (Fin 27)))] },
  { D := {4, 5, 6, 8, 9, 12}, bundles := [(0, ([0] : List (Fin 27))), (1, ([3, 5] : List (Fin 27))), (2, ([6, 7] : List (Fin 27))), (3, ([9, 10, 11] : List (Fin 27))), (7, ([14, 16] : List (Fin 27))), (10, ([19] : List (Fin 27))), (11, ([13] : List (Fin 27))), (13, ([15, 18] : List (Fin 27))), (14, ([20] : List (Fin 27))), (15, ([23] : List (Fin 27))), (16, ([12] : List (Fin 27))), (17, ([24] : List (Fin 27)))] },
  { D := {3, 6, 10, 11, 13, 17}, bundles := [(0, ([0, 1] : List (Fin 27))), (1, ([4] : List (Fin 27))), (2, ([8] : List (Fin 27))), (4, ([9] : List (Fin 27))), (5, ([10, 13] : List (Fin 27))), (7, ([14] : List (Fin 27))), (8, ([18] : List (Fin 27))), (9, ([11, 19] : List (Fin 27))), (12, ([24] : List (Fin 27))), (14, ([25] : List (Fin 27))), (15, ([21, 22] : List (Fin 27))), (16, ([26] : List (Fin 27)))] },
  { D := {2, 5, 7, 10, 12, 16}, bundles := [(0, ([1, 2] : List (Fin 27))), (1, ([5] : List (Fin 27))), (3, ([10] : List (Fin 27))), (4, ([6, 12] : List (Fin 27))), (6, ([14] : List (Fin 27))), (8, ([16] : List (Fin 27))), (9, ([19] : List (Fin 27))), (11, ([13] : List (Fin 27))), (13, ([8] : List (Fin 27))), (14, ([17] : List (Fin 27))), (15, ([21, 23] : List (Fin 27))), (17, ([24, 26] : List (Fin 27)))] },
  { D := {0, 4, 11, 13, 14, 15}, bundles := [(1, ([4] : List (Fin 27))), (2, ([6, 8] : List (Fin 27))), (3, ([9] : List (Fin 27))), (5, ([13] : List (Fin 27))), (6, ([0, 15] : List (Fin 27))), (7, ([17] : List (Fin 27))), (8, ([18] : List (Fin 27))), (9, ([20] : List (Fin 27))), (10, ([1, 21] : List (Fin 27))), (12, ([23] : List (Fin 27))), (16, ([2, 12] : List (Fin 27))), (17, ([25] : List (Fin 27)))] },
  { D := {1, 2, 4, 7, 10, 17}, bundles := [(0, ([1] : List (Fin 27))), (3, ([9] : List (Fin 27))), (5, ([7] : List (Fin 27))), (6, ([14] : List (Fin 27))), (8, ([3, 16] : List (Fin 27))), (9, ([19] : List (Fin 27))), (11, ([4] : List (Fin 27))), (12, ([5, 24] : List (Fin 27))), (13, ([8] : List (Fin 27))), (14, ([17, 25] : List (Fin 27))), (15, ([21] : List (Fin 27))), (16, ([12, 26] : List (Fin 27)))] },
  { D := {0, 3, 5, 8, 12, 14}, bundles := [(1, ([3, 5] : List (Fin 27))), (2, ([7] : List (Fin 27))), (4, ([9] : List (Fin 27))), (6, ([0] : List (Fin 27))), (7, ([16, 17] : List (Fin 27))), (9, ([11, 20] : List (Fin 27))), (10, ([1] : List (Fin 27))), (11, ([13] : List (Fin 27))), (13, ([18] : List (Fin 27))), (15, ([23] : List (Fin 27))), (16, ([2] : List (Fin 27))), (17, ([24, 25] : List (Fin 27)))] },
  { D := {1, 2, 6, 9, 12, 16}, bundles := [(0, ([0, 2] : List (Fin 27))), (3, ([11] : List (Fin 27))), (4, ([6, 12] : List (Fin 27))), (5, ([7] : List (Fin 27))), (7, ([14] : List (Fin 27))), (8, ([3] : List (Fin 27))), (10, ([19] : List (Fin 27))), (11, ([4] : List (Fin 27))), (13, ([8, 15] : List (Fin 27))), (14, ([20] : List (Fin 27))), (15, ([23] : List (Fin 27))), (17, ([24, 26] : List (Fin 27)))] },
  { D := {1, 4, 6, 10, 11, 14}, bundles := [(0, ([0, 1] : List (Fin 27))), (2, ([6] : List (Fin 27))), (3, ([9] : List (Fin 27))), (5, ([13] : List (Fin 27))), (7, ([14, 17] : List (Fin 27))), (8, ([3] : List (Fin 27))), (9, ([19, 20] : List (Fin 27))), (12, ([5] : List (Fin 27))), (13, ([15] : List (Fin 27))), (15, ([21, 22] : List (Fin 27))), (16, ([12] : List (Fin 27))), (17, ([25] : List (Fin 27)))] },
  { D := {5, 7, 8, 9, 15, 16}, bundles := [(0, ([2] : List (Fin 27))), (1, ([3] : List (Fin 27))), (2, ([7] : List (Fin 27))), (3, ([10, 11] : List (Fin 27))), (4, ([12] : List (Fin 27))), (6, ([14] : List (Fin 27))), (10, ([19, 21] : List (Fin 27))), (11, ([13, 22] : List (Fin 27))), (12, ([23] : List (Fin 27))), (13, ([18] : List (Fin 27))), (14, ([17, 20] : List (Fin 27))), (17, ([26] : List (Fin 27)))] },
  { D := {5, 7, 8, 10, 12, 16}, bundles := [(0, ([1, 2] : List (Fin 27))), (1, ([3, 5] : List (Fin 27))), (2, ([7] : List (Fin 27))), (3, ([10] : List (Fin 27))), (4, ([12] : List (Fin 27))), (6, ([14] : List (Fin 27))), (9, ([19] : List (Fin 27))), (11, ([13] : List (Fin 27))), (13, ([18] : List (Fin 27))), (14, ([17] : List (Fin 27))), (15, ([21, 23] : List (Fin 27))), (17, ([24, 26] : List (Fin 27)))] },
  { D := {5, 8, 9, 13, 15, 16}, bundles := [(0, ([2] : List (Fin 27))), (1, ([3] : List (Fin 27))), (2, ([7, 8] : List (Fin 27))), (3, ([10, 11] : List (Fin 27))), (4, ([12] : List (Fin 27))), (6, ([15] : List (Fin 27))), (7, ([16] : List (Fin 27))), (10, ([19, 21] : List (Fin 27))), (11, ([13, 22] : List (Fin 27))), (12, ([23] : List (Fin 27))), (14, ([20] : List (Fin 27))), (17, ([26] : List (Fin 27)))] },
  { D := {0, 2, 5, 8, 12, 14}, bundles := [(1, ([3, 5] : List (Fin 27))), (3, ([10] : List (Fin 27))), (4, ([6] : List (Fin 27))), (6, ([0] : List (Fin 27))), (7, ([16, 17] : List (Fin 27))), (9, ([20] : List (Fin 27))), (10, ([1] : List (Fin 27))), (11, ([13] : List (Fin 27))), (13, ([8, 18] : List (Fin 27))), (15, ([23] : List (Fin 27))), (16, ([2] : List (Fin 27))), (17, ([24, 25] : List (Fin 27)))] },
  { D := {0, 1, 2, 7, 9, 12}, bundles := [(3, ([11] : List (Fin 27))), (4, ([6] : List (Fin 27))), (5, ([7] : List (Fin 27))), (6, ([0, 14] : List (Fin 27))), (8, ([3, 16] : List (Fin 27))), (10, ([1, 19] : List (Fin 27))), (11, ([4] : List (Fin 27))), (13, ([8] : List (Fin 27))), (14, ([17, 20] : List (Fin 27))), (15, ([23] : List (Fin 27))), (16, ([2] : List (Fin 27))), (17, ([24] : List (Fin 27)))] },
  { D := {0, 3, 5, 8, 15, 17}, bundles := [(1, ([3] : List (Fin 27))), (2, ([7] : List (Fin 27))), (4, ([9] : List (Fin 27))), (6, ([0] : List (Fin 27))), (7, ([16] : List (Fin 27))), (9, ([11] : List (Fin 27))), (10, ([1, 21] : List (Fin 27))), (11, ([13, 22] : List (Fin 27))), (12, ([23, 24] : List (Fin 27))), (13, ([18] : List (Fin 27))), (14, ([25] : List (Fin 27))), (16, ([2, 26] : List (Fin 27)))] },
  { D := {3, 8, 10, 11, 13, 17}, bundles := [(0, ([1] : List (Fin 27))), (1, ([3, 4] : List (Fin 27))), (2, ([8] : List (Fin 27))), (4, ([9] : List (Fin 27))), (5, ([10, 13] : List (Fin 27))), (6, ([15] : List (Fin 27))), (7, ([16] : List (Fin 27))), (9, ([11, 19] : List (Fin 27))), (12, ([24] : List (Fin 27))), (14, ([25] : List (Fin 27))), (15, ([21, 22] : List (Fin 27))), (16, ([26] : List (Fin 27)))] },
  { D := {3, 11, 13, 14, 15, 16}, bundles := [(0, ([2] : List (Fin 27))), (1, ([4] : List (Fin 27))), (2, ([8] : List (Fin 27))), (4, ([9, 12] : List (Fin 27))), (5, ([10, 13] : List (Fin 27))), (6, ([15] : List (Fin 27))), (7, ([17] : List (Fin 27))), (8, ([18] : List (Fin 27))), (9, ([11, 20] : List (Fin 27))), (10, ([21] : List (Fin 27))), (12, ([23] : List (Fin 27))), (17, ([25, 26] : List (Fin 27)))] },
  { D := {0, 1, 4, 11, 13, 14}, bundles := [(2, ([6, 8] : List (Fin 27))), (3, ([9] : List (Fin 27))), (5, ([13] : List (Fin 27))), (6, ([0, 15] : List (Fin 27))), (7, ([17] : List (Fin 27))), (8, ([3, 18] : List (Fin 27))), (9, ([20] : List (Fin 27))), (10, ([1] : List (Fin 27))), (12, ([5] : List (Fin 27))), (15, ([22] : List (Fin 27))), (16, ([2, 12] : List (Fin 27))), (17, ([25] : List (Fin 27)))] },
  { D := {1, 2, 6, 9, 11, 16}, bundles := [(0, ([0, 2] : List (Fin 27))), (3, ([11] : List (Fin 27))), (4, ([6, 12] : List (Fin 27))), (5, ([7, 13] : List (Fin 27))), (7, ([14] : List (Fin 27))), (8, ([3] : List (Fin 27))), (10, ([19] : List (Fin 27))), (12, ([5] : List (Fin 27))), (13, ([8, 15] : List (Fin 27))), (14, ([20] : List (Fin 27))), (15, ([22] : List (Fin 27))), (17, ([26] : List (Fin 27)))] },
  { D := {1, 2, 4, 6, 10, 14}, bundles := [(0, ([0, 1] : List (Fin 27))), (3, ([9] : List (Fin 27))), (5, ([7] : List (Fin 27))), (7, ([14, 17] : List (Fin 27))), (8, ([3] : List (Fin 27))), (9, ([19, 20] : List (Fin 27))), (11, ([4] : List (Fin 27))), (12, ([5] : List (Fin 27))), (13, ([8, 15] : List (Fin 27))), (15, ([21] : List (Fin 27))), (16, ([12] : List (Fin 27))), (17, ([25] : List (Fin 27)))] },
  { D := {1, 2, 5, 7, 10, 17}, bundles := [(0, ([1] : List (Fin 27))), (3, ([10] : List (Fin 27))), (4, ([6] : List (Fin 27))), (6, ([14] : List (Fin 27))), (8, ([3, 16] : List (Fin 27))), (9, ([19] : List (Fin 27))), (11, ([4, 13] : List (Fin 27))), (12, ([5, 24] : List (Fin 27))), (13, ([8] : List (Fin 27))), (14, ([17, 25] : List (Fin 27))), (15, ([21] : List (Fin 27))), (16, ([26] : List (Fin 27)))] },
  { D := {0, 2, 5, 7, 9, 12}, bundles := [(1, ([5] : List (Fin 27))), (3, ([10, 11] : List (Fin 27))), (4, ([6] : List (Fin 27))), (6, ([0, 14] : List (Fin 27))), (8, ([16] : List (Fin 27))), (10, ([1, 19] : List (Fin 27))), (11, ([13] : List (Fin 27))), (13, ([8] : List (Fin 27))), (14, ([17, 20] : List (Fin 27))), (15, ([23] : List (Fin 27))), (16, ([2] : List (Fin 27))), (17, ([24] : List (Fin 27)))] },
  { D := {0, 3, 8, 13, 15, 17}, bundles := [(1, ([3] : List (Fin 27))), (2, ([8] : List (Fin 27))), (4, ([9] : List (Fin 27))), (5, ([10] : List (Fin 27))), (6, ([0, 15] : List (Fin 27))), (7, ([16] : List (Fin 27))), (9, ([11] : List (Fin 27))), (10, ([1, 21] : List (Fin 27))), (11, ([22] : List (Fin 27))), (12, ([23, 24] : List (Fin 27))), (14, ([25] : List (Fin 27))), (16, ([2, 26] : List (Fin 27)))] },
  { D := {1, 4, 6, 9, 11, 17}, bundles := [(0, ([0] : List (Fin 27))), (2, ([6] : List (Fin 27))), (3, ([9, 11] : List (Fin 27))), (5, ([13] : List (Fin 27))), (7, ([14] : List (Fin 27))), (8, ([3] : List (Fin 27))), (10, ([19] : List (Fin 27))), (12, ([5, 24] : List (Fin 27))), (13, ([15] : List (Fin 27))), (14, ([20, 25] : List (Fin 27))), (15, ([22] : List (Fin 27))), (16, ([12, 26] : List (Fin 27)))] },
  { D := {3, 8, 13, 14, 15, 16}, bundles := [(0, ([2] : List (Fin 27))), (1, ([3] : List (Fin 27))), (2, ([8] : List (Fin 27))), (4, ([9, 12] : List (Fin 27))), (5, ([10] : List (Fin 27))), (6, ([15] : List (Fin 27))), (7, ([16, 17] : List (Fin 27))), (9, ([11, 20] : List (Fin 27))), (10, ([21] : List (Fin 27))), (11, ([22] : List (Fin 27))), (12, ([23] : List (Fin 27))), (17, ([25, 26] : List (Fin 27)))] },
  { D := {3, 4, 6, 7, 12, 15}, bundles := [(0, ([0] : List (Fin 27))), (1, ([5] : List (Fin 27))), (2, ([6] : List (Fin 27))), (5, ([10] : List (Fin 27))), (8, ([16] : List (Fin 27))), (9, ([11] : List (Fin 27))), (10, ([21] : List (Fin 27))), (11, ([22] : List (Fin 27))), (13, ([15] : List (Fin 27))), (14, ([17] : List (Fin 27))), (16, ([12] : List (Fin 27))), (17, ([24] : List (Fin 27)))] }
]

/-- Bitmask of a list of edge indices (bit `j` set iff `j` occurs in the list). -/
def bmask (l : List (Fin 27)) : Nat :=
  l.foldr (fun (j : Fin 27) m => m ||| (1 <<< (j : Nat))) 0

instance : LeftCommutative (fun (j : Fin 27) (m : Nat) => m ||| (1 <<< (j : Nat))) :=
  ⟨fun a b c => by ac_rfl⟩

/-- Bitmask of a finite set of edge indices. -/
def maskOf (s : Finset (Fin 27)) : Nat :=
  s.val.foldr (fun (j : Fin 27) m => m ||| (1 <<< (j : Nat))) 0

/-- `chk s` holds iff some certificate set has no bundle entirely contained in
the edge-index set `s`. The membership tests are performed on bitmasks, which
keeps the kernel computation cheap. -/
def chk (s : Finset (Fin 27)) : Bool :=
  certs.any (fun c => c.bundles.all (fun p => (bmask p.2 &&& maskOf s) != bmask p.2))

/-- Enumeration of all `k`-element subsets of `{i, …, n-1}` (as `Finset`s), with
a final check at every leaf. `fuel` is `n - i`. -/
def go {n : Nat} (chk : Finset (Fin n) → Bool) : Nat → Nat → Nat → Finset (Fin n) → Bool
  | 0, _, k, s => if k = 0 then chk s else true
  | fuel + 1, i, k, s =>
      if k = 0 then chk s
      else if h : i < n then
        go chk fuel (i + 1) (k - 1) (insert ⟨i, h⟩ s) && go chk fuel (i + 1) k s
      else true

/-! ## The vertex side: no 5-set dominates -/

/-- Neighbour bitmasks of the 18 vertices (bit `u` set iff `u` is adjacent). -/
def nb : V → Nat :=
  ![66624, 6400, 8240, 560, 65548, 2060, 8321, 16704, 8322, 17416, 33281, 32802, 163842, 324, 131712, 7168, 131089, 86016]

lemma nb_spec : ∀ v u : V, G.Adj v u ↔ (nb v).testBit u := by
  decide

/-- `dominatesB s` holds iff the vertices of `s` dominate `G`. -/
def dominatesB (s : Finset V) : Bool :=
  decide (∀ v : V, v ∈ s ∨ ∃ u ∈ s, (nb v).testBit u)

/-- Negation of `dominatesB`. -/
def notDomB (s : Finset V) : Bool := !(dominatesB s)


/-- Boolean correctness check for one certificate. -/
def certOk (c : Cert) : Bool :=
  decide (c.D.card = 6) &&
  decide (∀ v : V, v ∈ c.D ∨ ∃ u ∈ c.D, G.Adj v u) &&
  c.bundles.all (fun p =>
    decide (p.1 ∉ c.D) &&
    decide (∀ j : Fin 27, j ∈ p.2 ↔ ∃ u ∈ c.D, eOf j = s(p.1, u))) &&
  decide (∀ x : V, x ∉ c.D → ∃ p ∈ c.bundles, p.1 = x)


end DsBatch.P09
