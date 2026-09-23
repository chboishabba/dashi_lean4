# TOE handoff — Millennium proof work (P vs NP, Hodge, BSD)

## Use of this archive

Extract this archive into the Aristotle project and treat both source trees as
reference material.  Copy or adapt only the source needed for the proof being
attempted; do not mistake the archive itself, source-written status flags, or a
cross-prover interface for a proof of a Clay problem.

The requested focus for this round is **not** Navier–Stokes, Riemann Hypothesis,
or Yang–Mills.  Work on the literal P-vs-NP, Hodge, and BSD frontiers below.

`PROGRAMME_FRONTIERS.md` is the user-supplied current overview and is the
priority reading order.  It is included verbatim.

## Exact source provenance

* `dashi_agda/` is based on
  `eb87aeed9d7dee71ac9a65e270e94744da3ae369`
  (`origin/agent/pr1006-three-lane-continuation`), the newest continuation of
  the #1006 Millennium stack.  It includes the current global SAT tableau
  work.  `Docs/ProjectMap.md` and `scripts/build_project_map.py` are added as
  navigation sidecars from `c0048dc8359464796d3f854a3bfc87cf3a84d7ba`; they
  are deliberately not accompanied by the unrelated Digital-ESD branch on
  which that documentation commit sits.
* `dashi_lean4/` is from Lean PR #10 head
  `b588384521bdaa73324ed0bf587c77d66730c8e4`
  (`origin/agent/millennium-three-lane-lean-assist`).  The source tree excludes
  `ImportedLeans/` and `artifacts/` solely to keep the archive practical; the
  complete current Lean project source otherwise remains available for
  reference.

No fresh Agda or Lean kernel claim is made by this handoff.  The local Lean
`Synthesis` build is presently blocked before DASHI code by a pinned
Batteries/Mathlib versus Lean API mismatch; do not infer a programme failure
from that environmental error.

## Requested theorem work

Prioritise one genuinely payable literal theorem.  Preserve exact same-object
carriers and quantify the remaining mathematical hypothesis explicitly rather
than replacing it with a Boolean/status receipt.

1. **P vs NP:** global time placement, endpoint clauses, SAT assignment iff
   valid accepting tableau, and polynomial variable/clause bounds for the
   actual Cook–Levin reduction.
2. **Hodge:** prove that the canonical realization unit
   `∂Δ³ → Sing |∂Δ³|` induces the required degree-two rational homology
   isomorphism; use it to close the literal `CP¹` case if the existing
   same-object transports suffice.
3. **BSD arithmetic:** build the actual elliptic `E[2]` / trivial
   `(Z/2)^2` Galois representation equivalence, then the Galois-H¹ / square
   class and explicit-Selmer / cohomological-Selmer comparison.
4. **BSD analytic:** prove the same-object coefficient identity
   `c_(4m+1)^η = a_(4m+1)(E)` and only then transport the existing eta
   continuation and functional equation to the literal elliptic L-series.

Do not work on NS, RH, or YM in this pass unless a narrowly necessary imported
lemma is genuinely shared infrastructure.
