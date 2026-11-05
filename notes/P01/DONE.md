# DONE — P01

Paper: arXiv:2608.15281, *A Ten-Vertex Counterexample to a Conjecture on Unstable Graphs*
(Theorem 1, refuting Mizzi's conjecture on unstable graphs).

Status: `bash infra/eval.sh P01` reports `main_status: proved` (final run 2026-11-05T12:35:06Z).

## What is proved

Both targets are proved, `sorry`-free, and depend only on the standard axioms
`{propext, Classical.choice, Quot.sound}` (checked by `#print axioms` in `infra/eval.sh`):

1. `DsBatch.P01.counterexample : counterexample_statement` — the paper's Theorem 1 for the
   explicit graph `G` on `Fin 10` (paper vertices `1..10` ↔ `Fin` values `0..9`, edges
   `12, 1·10, 24, 34, 36, 45, 57, 5·10, 6·10, 79, 8·10`):
   - `G.Connected`;
   - `VertexDetermining G` (the ten open neighbourhoods are pairwise distinct);
   - `IsNontriviallyUnstable G`, witnessed by the explicit pair
     `α = Equiv.swap 0 5 = (1 6)`, `β = Equiv.swap 1 2 = (2 3)` with `α ≠ β`;
   - `¬ ContainsOddDoubleCycle G`: there is no odd `k` with both `C_k` and `C_{2k}`.
2. `DsBatch.P01.mizzi_conjecture_false : mizzi_conjecture_false_statement` —
   `¬ MizziConjecture`; the conjecture "every finite nontrivially unstable graph contains
   `C_k` and `C_{2k}` for some odd `k`" is false, with `G` as the counterexample.

Proof route (the paper's own argument):

- Connectedness: every vertex reaches vertex `1` by a short explicit walk
  (`reachable_zero`), so `G.Reachable` relates all vertices.
- Non-bipartiteness: the odd cycle `1,2,4,5,10,1` admits no proper 2-colouring
  (`five_cycle_not_two_colorable`).
- Vertex-determining: checked by kernel `decide` over all pairs of neighbourhoods.
- Two-fold automorphism: the neighbourhood identities for `α = (1 6)`, `β = (2 3)` are
  checked by kernel `decide`.
- Cycle exclusion: any cycle of `G` has at most `10` vertices, so an odd `k` with both
  `C_k` and `C_{2k}` must be `3` or `5`. There is no triangle (`no_cycle_3`, from a
  `decide`-checked triangle-free fact), and there is no 10-cycle (`no_cycle_10`): a
  10-cycle would contain the leaf `9` (index `8`), whose two cycle-neighbours would both
  have to be its unique graph-neighbour `7` (index `6`), contradicting injectivity.
  `no_odd_double_cycle` combines these with `omega` and `interval_cases`.

Non-vacuity is checked inside the frozen `Statement.lean`: the explicit nontrivial
two-fold automorphism, a 5-cycle and a 6-cycle in `G`, and a 3-vertex edgeless graph with
no 3-cycle.

## Metrics

- Lean line count: **319** total — `Defs.lean` 93, `Statement.lean` 52, `Main.lean` 174.
- Spend: **1.039 CNY** at the final evaluation, of the 3.0 CNY cap (`projects/P01/state/ledger.jsonl`).
- Wall time: about **16 minutes** (2026-11-05T12:17:53Z to 2026-11-05T12:34Z), one chunk.
- Build: `lake build DsBatch` succeeds; `infra/scan.py` finds 0 forbidden tokens;
  frozen SHA-256 hashes in `project.json` match.

## Errors or gaps in the paper

- No mathematical error was found. The author's `papers/2608.15281/verify_counterexample.py`
  reproduces the same graph, the same two-fold automorphism `α=(1 6)`, `β=(2 3)`, and the
  cycle lengths `5,5,6`.
- **Definitional gap.** The paper never defines "nontrivially unstable"; it cites Mizzi
  (arXiv:2603.27559v2), which is not present in `papers/`. We read the term off the paper's
  own Verification section, where connectedness and non-bipartiteness are checked because
  "it satisfies the paper's exclusions of the two classes called trivially unstable": thus
  `IsTriviallyUnstable G := ¬G.Connected ∨ G.IsBipartite` and
  `IsNontriviallyUnstable G := IsUnstable G ∧ ¬IsTriviallyUnstable G`. The independent
  audit (`AUDIT.md`, PASS) accepted this reading as the one the text dictates. If Mizzi's
  exact definition were narrower (e.g. additionally requiring vertex-determining), the
  refutation still applies: our counterexample also satisfies the extra conditions.
- **Scope note on the cycle spectrum.** The abstract states that the complete set of simple
  cycle lengths is `{5,5,6}`. We formalized what Theorem 1 and the required scope need:
  no odd `k` with both `C_k` and `C_{2k}`, together with a 5-cycle and a 6-cycle (and no
  `C_3`, no `C_10`). We did **not** formalize the full statement "every cycle of `G` has
  length `5` or `6`" (the theta-graph argument); it is not needed for the target and is
  not claimed here.
- Theorem 1's literal wording says only "connected and nontrivially unstable"; the abstract
  and the Verification section additionally state vertex-determining. Our statement includes
  `VertexDetermining G` — a strengthening of Theorem 1, not a weakening, and a property the
  paper proves. The audit noted this as acceptable.
