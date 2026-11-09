PASS

# Fidelity audit: P15 (arXiv 2610.22783)

Auditor: independent fidelity audit of the frozen-target statements in
`DsBatch/P15/Statement.lean` against the paper and the queue scope. Build,
grep, and axiom checks all green.

## Verdicts by point

1. **Definition fidelity — PASS.** `CatVertex`/`catAdj`/`catGraph` (Defs.lean:39-87)
   formalize `Cat(p₁,…,pᵣ)` exactly as the paper's Section 2: path vertices
   adjacent iff consecutive, pendant leaves attached to their own path vertex,
   no other edges. `T3 = Cat(8,7,25)` (`shape3`, Defs.lean:104-119) is the
   paper's `T₃` with `a=inl 0`, `b=inl 1`, `c=inl 2`. `inducedWeight`
   (Defs.lean:137-140) is the sum of incident edge labels `(L e).val + 1`, i.e.
   a bijection `E → {1,…,m}`. `IsLocalAntimagic`/`IsAntimagic`/`weightImage`
   (Defs.lean:144-157) match the paper's local antimagic, antimagic, and `C(f)`.
   `chiLa` (Defs.lean:162-164) is `sInf` over `|C(f)|` for local antimagic
   labelings — the paper's minimum, and non-vacuously well-defined for trees of
   order ≥ 3 (Haslegrave's existence theorem, relied on only inside
   `LeafConjecture`'s hypothesis). `leafCount` (Defs.lean:167-168) counts
   degree-1 vertices. `IsCaterpillar` (Defs.lean:174-181) is the paper's
   "tree whose internal vertices induce a path": an injective enumeration of
   exactly the non-leaves with adjacency iff consecutive. `LeafConjecture`
   (Defs.lean:185-187) is exactly Conjecture (leaf conjecture): every tree of
   order ≥ 3 has `χ_la ≤ ℓ + 2`. No weakening, no Prop-field interface, no
   vacuity in the quantified hypothesis.

2. **Statement fidelity — PASS.**
   - `t3_caterpillar_statement` (Statement.lean:16-18): `IsCaterpillar T3` plus
     `|V|=43, |E|=42, ℓ=40, d(a)=d(b)=9, d(c)=26` — the paper's setup for `T₃`.
   - `t3_weight_separation_statement` (Statement.lean:24-25): every *local
     antimagic* bijection has 43 distinct induced weights — the paper's
     separation argument (Proposition on `S={a,b,c}`: `I₄₂(9)=[45,342]`,
     `I₄₂(26)=[351,767]`, both above 42, `a,c` the only nonadjacent internal
     pair, so `|C(f)| = ℓ+|S| = 43`).
   - `t3_chiLa_statement` (Statement.lean:28-29): `chiLa T3 = 43 ∧
     chiLa T3 = leafCount T3 + 3` — exactly `χ_la(T₃) = 43 = ℓ(T₃)+3`.
   - `leaf_conjecture_false_statement` (Statement.lean:32-33): `¬ LeafConjecture`
     — negates the leaf conjecture over *all* finite trees of order ≥ 3.
   All four are the paper's notions, not weakened or alternate ones. The
   docstring/comment citations now use the paper's actual section numbering
   (Theorem 4.1 for `T₃`, Proposition 3.2 separation criterion, Corollary 3.3
   maximum weights, Conjecture 2.2 leaf conjecture).

3. **Non-vacuity — PASS.** Statement.lean:39-54 compiles the `example`s:
   `Fintype.card V3 = 43`, `|edgeSet| = 42`, `leafCount = 40`, degrees `9,9,26`,
   and `∃ L, IsLocalAntimagic T3 L` via `t3Labeling` (labels `ab=1, bc=2`,
   a-leaves `3..10`, b-leaves `11..17`, c-leaves `18..42`; weights `53,101,752`).
   The hypothesis of `t3_weight_separation_statement` is satisfiable, so the
   targets are not vacuous.

4. **Queue paraphrase error — verified independently; formalization is faithful.**
   (a) The collision in NOTES.md is real (checked by hand and by script):
   `f(ab)=7`, `f(bc)=16`, a-leaves `1,8,21,22,23,25,27,30` (sum 157),
   b-leaves `6,9,15,20,24,26,41` (sum 141); then `f⁺(a)=7+157=164` and
   `f⁺(b)=7+16+141=164`. The 17 explicit labels are distinct and the remaining
   25 labels `{2,3,4,5,10,11,12,13,14,17,18,19,28,29,31,32,33,34,35,36,37,38,39,40,42}`
   complete a valid bijection. Adjacent `a,b` share weight 164, so this bijection
   is not even local antimagic; hence the queue's literal clause "every bijection
   has pairwise distinct induced vertex weights" is **false** for `T₃`, and the
   paper never asserts it for `T₃`.
   (b) The paper's Corollary ("every bijection is antimagic") requires
   `I_m(d(u)) ∩ I_m(d(v)) = ∅` for *every* pair of distinct internal vertices.
   For `T₃`, the adjacent pair `a,b` both have `I₄₂(9)=[45,342]`, so the clause
   fails; Proposition (separation criterion) only needs disjointness for
   *nonadjacent* pairs, and adjacency supplies the separation of `a,b`.
   The paper's `T₃` theorem is exactly `χ_la(T₃)=43=ℓ+3`; the "every bijection
   is antimagic" property is proved only for the (optional) `H_{r,t}` family.
   **Judgment:** stating `t3_weight_separation` (local-antimagic version) plus
   `t3_chiLa` plus `¬LeafConjecture` is the faithful and honest formalization of
   the required mathematical goal (`χ_la(T₃)=43=ℓ+3` and the conjecture false),
   *not* an unjustified weakening. The queue's "every bijection" clause is a
   paraphrase error conflating `T₃` with the Section-5 family; it is mathematically
   false and unprovable, and NOTES.md records it plainly rather than papering over it.

5. **Formal sanity — PASS.**
   - `lake build DsBatch` succeeds (9051 jobs, no errors).
   - grep for `sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|debug.skipKernelTC`
     over `DsBatch/P15/*.lean` and `projects/P15/*.{md,json,lean}` finds only two
     comment hits (docstrings in Statement.lean:6 and Main.lean:3); no forbidden
     construct in code.
   - `project.json` targets correspond exactly: `t3_caterpillar`,
     `t3_weight_separation`, `t3_chiLa`, `leaf_conjecture_false` are theorems in
     Main.lean:442,446,451,455 with matching `*_statement` defs in Statement.lean:16,24,28,32.
   - `#print axioms` for each target = `[propext, Classical.choice, Quot.sound]`.

## Defects found

None. The only nit from the first pass (comment/docstring citation numbering
in Defs.lean, Statement.lean, Main.lean, NOTES.md) has been fixed to the
paper's actual numbering (`Conjecture 2.2`, `Proposition 3.2`, `Corollary 3.3`,
`Theorem 4.1`). Verified by `git diff` that these are comment/docstring-only
changes; no code, statement, or proof changed, and `lake build DsBatch` still
succeeds (9051 jobs).
