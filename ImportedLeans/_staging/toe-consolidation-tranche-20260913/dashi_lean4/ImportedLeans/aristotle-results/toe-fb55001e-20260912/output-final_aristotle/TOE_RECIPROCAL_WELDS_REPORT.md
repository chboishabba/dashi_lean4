# Reciprocal welds, narrow bridges, and the integrated 2026-09-06 Agda tranche

This session did three things: it integrated the supplied Agda tranche archive
into the corpus tree, it built the reciprocal half of the cross-domain garden
layer as checked Lean (seven welds plus three narrow bridges), and it ran the
only Agda-side validation available here — a static import-resolution audit,
since no Agda toolchain is installed in this environment.

Everything called "proved" below is a Lean theorem that elaborates in this
toolchain with no `sorry`, no project axiom and no `native_decide`; the axiom
audit for all of it runs during `lake build Integration`.

---

## 1. Archive integration

`toe-dashi-agda-tranche-20260906-from-f2eb0e61.tar.gz` (base
`f2eb0e61…`, target `49f5193e…`) had **not** been unpacked into the tree in the
previous session: of its 1 085 paths, 1 063 were absent and 22 existed with
older content.  It is now integrated at the repository-relative layout the
tranche declares, with `Agda/` as the `dashi_agda` root:

| archive path | placed at | files |
| --- | --- | --- |
| `DASHI/**` | `Agda/DASHI/**` | 1 043 |
| `Docs/**` | `Agda/Docs/**` | 21 |
| `scripts/**` | `Agda/scripts/**` | 10 |
| `.github/workflows/**` | `Agda/.github/workflows/**` | 5 |
| `tools/**` | `Agda/tools/**` | 2 |
| `Fixtures/**` | `Agda/Fixtures/**` | 2 |
| `TOE_TRANCHE_20260906.md` | `Agda/Docs/TOE_TRANCHE_20260906.md` | 1 |

Before overwriting the 22 pre-existing files, each was diffed against the
archive version.  Exactly one repository-only line existed in any of them (a
re-ordering of `ContextualFractranArgumentTransportExact` in
`Cognition/PNF/ContextualFractranHyperformalismEverything.agda`), so no earlier
repository work was lost by taking the archive versions.  The Agda tree went
from 14 541 to 15 562 `.agda` files.

*Scope note.*  Sixty-six of the archive's files sit under `DASHI/Physics/YangMills`
(25) and `DASHI/Physics/Closure/NSTriadKN…` (41).  Those directories were
already present in the corpus (2 239 and 4 886 files respectively), so nothing
was reintroduced; the files were placed mechanically and **no Yang–Mills or
Navier–Stokes material was read, edited, analysed or built on** in this session,
and none of the new Lean work touches either lane.

*Not possible here.*  Bringing PR #724 forward onto `2a9ff15a…` and re-running
its Agda/kernel workflow needs the upstream repository and a checker, neither of
which exists in this environment.  What is supplied instead is §3: a mechanical
import audit of the merged tree that flags exactly the import edges a rebase
would have to resolve.

---

## 2. The reciprocal layer, in Lean

The pre-existing kernel owned the *generic forms* (`BraidedTrace`,
`LineageEdge`, `DeclaredRealised`, `Reopen`, `QueryResidual`, `Loop`,
`EvidenceDependence`, `Quotient`).  The deficiency was reciprocity: nothing in a
donor lane consumed them.  Seven new modules under
`Lean/Integration/Kernel/Welds/` supply the consumers, and three under
`Lean/Integration/Kernel/Bridges/` keep three further motifs alive at bridge
size without flattening them into the weld layer.

### 2.1 Welds (7 first-order modules, 80 theorems, 1 318 lines; plus 2
second-order modules, 15 theorems, 226 lines — see frontier item 5)

| weld | module | consumes | headline theorem |
| --- | --- | --- | --- |
| textile → braided evidence → runtime provenance | `Welds.RuntimeBraidedProvenance` | `BraidedTrace`, `EvidenceDependence` | `pooling_destroys_independence` |
| amplification lineage → evidence dependence | `Welds.AmplifiedObservationCount` | `LineageEdge`, `EvidenceDependence` | `twenty_observations_are_three_sources` |
| operational realisation → remedy/runtime feedback | `Welds.RemedyRuntimeFeedback` | `DeclaredRealised`, `Reopen` | `runtime_success_does_not_close_the_remedy` |
| situated mediation → two real carriers | `Welds.SituatedMediationCarriers` | `Quotient` | `carriers_are_not_relabellings` |
| residual salience → active search scheduler | `Welds.ResidualSalienceScheduler` | `Quotient` | `salience_scheduler_beats_magnitude_scheduler` |
| deliberative moves → the action loop | `Welds.DeliberativeMoves` | `Loop`, `ResidualFibre`, `Reopen` | `listening_can_do_what_no_probe_can` |
| commuting provenance → source summaries | `Welds.CommutingProvenanceSquare` | `Quotient` | `whole_trajectory_agreement_is_not_a_projection` |

What each actually establishes, beyond re-exposing a generic form:

* **Runtime braided provenance.**  A trace is a list of events each stamped with
  a lane and its provenance roots.  `laneRoots_extract` proves extraction is
  lane-local (a lane can be handed to a consumer without recomputing the braid);
  `no_lawful_crossing_of_disjoint_lanes` instantiates the lawful-crossing
  firewall with the lane's own root set as the invariant, so a runtime step
  cannot carry one lane's authority onto another's evidence; and
  `pooling_destroys_independence` shows the flat log reports dependence exactly
  where the braided trace proves independence.
* **Amplified observation count.**  A twenty-node lineage in which node `i` is
  amplified from node `i − 3`.  Its root-propagation law is *discharged*, not
  postulated; `amplified_from_rootNode` proves by induction that every node
  descends from its acquisition by amplification alone; the count comes out as
  20 observations = 3 roots + 17 amplified descendants, with same-class pairs
  proved never independent and cross-class pairs proved independent.
* **Remedy/runtime feedback.**  Two consumers over one `DeclaredRealised.Episode`.
  Selective reopening is driven by *which* consumer failed:
  the runtime-only certificate survives an unrealised-but-acknowledged episode,
  the remedy-only and joint certificates reopen, and a fully realised episode
  reopens nothing.
* **Situated mediation.**  Mediation becomes an interface (`Mediates`) carrying
  the non-determination as a proof obligation; the obligation is discharged by a
  process-integration carrier and by a situated legal/social carrier, and
  `carriers_are_not_relabellings` proves no situation relabelling plus injective
  outcome relabelling carries one onto the other — the reason to keep two
  carriers rather than one abstraction.
* **Residual salience scheduler.**  Salience is `splitCount`, how much a residual
  separates the live hypotheses.  Inert residuals make no progress whatever
  their magnitude; separating residuals strictly narrow on every reading;
  salience does not descend through (magnitude, cost) and is not a function of
  the residual alone but of the (residual, live set) pair; and on one queue the
  magnitude-greedy scheduler picks the inert residual while the salience-greedy
  scheduler picks the small one that narrows.
* **Deliberative moves.**  `ask`/`listen`/`reformulate` are constructors of an
  `EpistemicMove` type extending `Loop.Move`; the embedding is injective and
  proper, and `strategyE_extends_strategy` makes the extension conservative.
  With a semantics on the (fibre, consumer) pair: all three narrowing moves
  refine, listening strictly narrows where every probe of the policy is inert,
  and reformulation closes a question with the fibre untouched.
* **Commuting provenance.**  `IsProjection` is the square; a claim carrying it
  transports along the whole pipeline (`ProjectionClaim.transports`), while
  agreement now — and even agreement along an entire observed trajectory — does
  not supply it, and for the fixture no coarse step commutes at all.

### 2.2 Bridges (3 modules, 18 theorems, 269 lines)

| rose | module | what it establishes |
| --- | --- | --- |
| quorum sensing ↔ thresholded collective transition | `Bridges.QuorumThreshold` | the transition is a threshold not a gradient; the collective state is no individual's property; **a quorum by headcount is not a quorum by independent provenance** |
| process stacks ↔ where information is first lost | `Bridges.InformationLossLocus` | a collapsed distinction is never restored downstream (so the question is well-posed), and the locus of loss is a property of the pair, not of the stack |
| Bragg phase coherence ↔ corroboration beyond source count | `Bridges.CorroborationPhase` | support is signed: a further report can lower it, no function of the count returns it, and count is legitimate exactly in the in-phase case |

Three roses were **not** implemented and remain open by choice: ALD
self-limitation ↔ self-limiting deliberative protocols; feature charging/history
↔ path-dependent institutional response; proof fabric ↔ append-only event
sourcing (this last one is already largely owned by
`Integration.Kernel.AppendOnlyHistory`, which proves non-retroactivity, that a
correction does not erase, that in-place rewriting is not an extension, and that
a state snapshot is a quotient of the log — so a further bridge would need a new
question, not a restatement).

### 2.3 Wiring

Both directories are imported by `Lean/Integration.lean` (registry entries 51ap
and 51aq) and every theorem listed above has a `#print axioms` line in
`Lean/Integration/AxiomAuditKernel.lean`.  `lake build Integration` completes
(8 275 jobs); the audit reports only `propext`, `Classical.choice` and
`Quot.sound` for the new material, and no `sorryAx` anywhere in the build log.

---

## 3. Agda-side validation available here

No Agda binary exists in this environment, so nothing Agda-side is claimed to
typecheck.  `scripts/agda_import_check.py` performs the mechanical part that can
be done without a checker: it collects every module name present as a file in
`Agda/` and resolves every `import`/`open import` line under `Agda/DASHI`.

Post-integration figures:

* 14 021 `DASHI` source files, 105 701 import lines parsed;
* 15 561 module files present, 141 distinct external (standard-library) module
  names — all reported as external, never as broken;
* **241 unresolved `DASHI.*` imports in 67 files.**

Breakdown of the 241 by target lane: `Moonshine` 113, `Physics` 91 (of which 65
are `YangMills`/`NavierStokes`-named and are out of scope here), `Cognition` 14,
`Foundations` 11, `Algebra` 8, others 4.  Twenty-eight of the non-YM/NS
unresolved edges are in files the tranche itself added or modified — including
`Cognition/PNF/ContextualFractranHyperformalismEverything.agda`, whose new line
`import DASHI.Cognition.PNF.ContextualFractranPNFHyperfabric369Exact` names a
module that is not in the shipped cutset (the sibling
`DASHI.Interop.ContextualFractranPNFHyperfabric369Exact` is).

These are exactly the edges a rebase and re-check would have to settle: either
the named modules exist upstream and were excluded from the delivered cutset, or
the aggregate imports are wrong.  Distinguishing the two needs the upstream
tree, so this report states the fact and does not guess.  No aggregate was
edited to make the count smaller.

Run it with `python3 scripts/agda_import_check.py` (add `--json` for machine
output); it exits non-zero when any `DASHI.*` import is unresolved.

---

## 4. Frontier — exact remaining obligations

1. **Rebase and workflow receipt for #724** — impossible here; needs the upstream
   repository and CI.  The nine-file content diff is unaffected by anything in
   this session; the braided-evidence owner it adds has, from this side, a Lean
   counterpart with checked proofs (`Welds.RuntimeBraidedProvenance`) that the
   Agda owner could be reconciled against once a checker is available.
2. **241 unresolved Agda import edges** (§3), 176 of them outside the YM/NS
   lanes.  Each is a one-line fact: file → missing module name.  Resolving them
   requires the upstream tree.
3. **No Agda typechecking anywhere in this corpus in this environment.**  Every
   Agda-side statement in every report remains source-reading only.
4. **Three roses unimplemented** (§2.2), deliberately.
5. **Second-order crossings: two done, the rest open.**  Both crossings named
   as the obvious next step are now proved.
   `Welds.LaneProjectionSquare` shows the lane extraction of
   `RuntimeBraidedProvenance` satisfies the commuting-square discipline of
   `CommutingProvenanceSquare` — `laneRoots_append` supplies the recurrence,
   `lane_extraction_is_a_projection` the square, and `lane_roots_transport` the
   consequence that the lane reading is correct after any number of appends;
   the flat log fails the first obligation of a projection claim.
   `Welds.SalienceOverLineage` measures salience against provenance classes
   rather than hypotheses and proves the two measures come apart in exactly one
   direction: a reading can split twenty observations 10/10 and separate none of
   the three provenance classes, while any class-separating reading separates
   observations.  What remains open at this level is every *other* pairing —
   e.g. deliberative moves constrained by append-only history (does `listen`
   have to be recorded as an event?), or the remedy/runtime reopening driven by
   lineage rather than by edge sets.
6. **All finite, all stipulated.**  Every carrier introduced here is a finite
   label type or a list/`Finset` over one, and every table (process effects, rule
   effects, edge kinds, thresholds) is a definition in the file.  Nothing in this
   session is an empirical claim about fabrication, biology, law, cognition or
   any physical process, and nothing here supports a theory-of-everything claim.
