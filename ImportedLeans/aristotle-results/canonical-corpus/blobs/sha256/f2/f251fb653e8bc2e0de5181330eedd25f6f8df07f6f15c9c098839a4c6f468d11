# The Aristotle / Wikidata reciprocal garden

*Integration record, dependency and provenance map, and honest frontier for the
round that instantiated the generic reciprocal-garden kernels on the concrete
Wikidata evidence semantics of the Aristotle archive.*

No Yang–Mills or Navier–Stokes material was read, edited, imported or built on
in this round.

---

## 1. Archives: integrated, then removed

Two archives were present at the project root at the start of the round.

| Archive | Disposition |
|---|---|
| `toe-dashi-agda-tranche-20260906-from-f2eb0e61.tar.gz` (2.4 MB, 1 085 paths) | Already unpacked into `Agda/` by the previous round; verified path-by-path this round — **1 083 of 1 085 paths present**, the two missing being the tranche note and its patch. `Agda/TOE_TRANCHE_20260906.md` was extracted; the 6.4 MB `.patch` was not retained, its content being exactly the already-applied tranche. Archive deleted. |
| `ae06ae06-…-aristotle (2).tar.gz` (14 MB, 5 414 paths, 86 MB expanded) | **Not previously unpacked.** Integrated this round under `Lean/DASHI/output-final_aristotle/`, the layout the archive itself declares. Archive deleted. |

What was integrated from the Aristotle archive: all **189** `RequestProject/**.lean`
files (109 571 lines), the lakefile/toolchain/manifest, `scripts`, `docs`
(including the generated reports), `data` (`*.wdkb` corpora), `site`, `web`,
`pages`, `examples`, `hf`, `p2p`, `toolforge`, `archive`, `.github`, and the two
markdown overviews. What was deliberately **not** copied: `.wikidata-cache`
(46 MB) and `.enrich-cache` (2.1 MB), which are regenerable HTTP caches, and
`docs/__pycache__`. Integrated size: 43 MB.

One name collision was handled without loss: the tree already carried a
`RequestProject/Main.lean` that imports Yang–Mills and Navier–Stokes closure
modules. That file was left exactly as it was; the archive's own root aggregate
was placed beside it as `RequestProject/MainArchive.lean`. Nothing else in the
integrated tree existed beforehand except `RequestProject/SpectralClosure.lean`,
which is repository-only and was kept.

**The archive now builds.** A new `AristotleArchive` library in `lakefile.toml`
(`srcDir = Lean/DASHI/output-final_aristotle`) declares the 42 modules that
this round's work consumes together with their transitive imports — including
`Core`, `Engine`, `Properties`, `PropertyEngine`, `Reachability`, `Ranks`,
`Snaks`, `Provenance`, `Schemas`, `Merge`, `Sync`, `Publish`, `Archive`,
`Reports` and `Worklist` — and is in `defaultTargets`. The CLI, generated-corpus and wiki
tranches of the archive are present as sources and are not built.

This matters for the honesty of everything below: the Wikidata semantics used in
this round is **the archive's own executable definitions**, elaborated in this
toolchain, not a paraphrase of them.

---

## 2. What was built: ten Lean owners, sorry-free

All under `Lean/Integration/Kernel/Aristotle/`, all imported by the `Integration`
aggregate (registry entry `51as`) and audited in
`Lean/Integration/AxiomAuditAristotle.lean` (62 `#print axioms` lines, every one
axiom-free or a subset of `{propext, Classical.choice, Quot.sound}`).

### 2.1 `PropertyFamilyQueryFibre` — (Q,P) coverage × query-compatible fibre

Donor kernels: `Integration.Kernel.PartialIdentification`.
Archive donor: `RequestProject.Ranks` (`group`, `bestRankNat`, `isTruthy`,
`truthyValues`).

* `truthyValues_congr_of_group_eq` — **general** (all claim sets, all `(Q,P)`):
  the truthy consumer factors through the statement family. This is the load
  bearing lemma and it is a theorem about the archive's definitions.
* `consumer_closed_on_nonsingleton_family_fibre` — *whole item unresolved ∧ the
  specific `(Q,P)` consumer closed*: the fibre of the family observation is not
  a singleton, and every world in it returns the same truthy value.
* `uncovered_family_does_not_close_the_consumer` — the converse discipline: two
  worlds agreeing on every observed normal-rank row, differing in the answer
  because of an unobserved *preferred* sibling.

### 2.2 `RankVisibilityCommutingProvenance` — rank × visibility × the square

Donor kernels: `Integration.Kernel.Welds.CommutingProvenanceSquare`.
Archive donor: `RequestProject.Ranks`.

* `rank_does_not_determine_visibility`, `visibility_is_not_a_function_of_the_statement`
  — visibility is non-local: it depends on the sibling group.
* `no_visibility_step_commutes` — for the retraction step there is **no** coarse
  step on visibilities making the square commute, although two worlds agree at
  the moment of observation.
* `family_projection_commutes` / `family_projection_transports` — the positive
  half: the family reading *is* a projection, for every incoming statement and
  every world, hence correct after any number of appends.
* `visibility_is_a_function_of_the_family` — why the family is the right coarse
  state.

### 2.3 `SnakAbsenceInformationLoss` — absence semantics × loss locus

Donor kernels: `Integration.Kernel.Bridges.InformationLossLocus`.
Archive donor: `RequestProject.Snaks` (`Satisfies`, `Models`, `Entails`,
`valuesOf`, `entails_noValue_iff`).

* `empty_result_does_not_entail_novalue` — the firewall, through the archive's
  model theory rather than by stipulation.
* `value_projection_collapses_absence` + `downstream_cannot_restore_novalue` —
  the collapse and its irreversibility for *every* downstream function.
* `locus_is_pair_relative_for_snak_absence`, `absence_collapse_persists`.

### 2.4 `ReliableSourceConsumerAdequacy` — `full ⊇ sourced ⊇ reliable`

Donor kernels: `Integration.Kernel.EvidenceDependence`,
`Integration.Kernel.Bridges.QuorumThreshold`.
Archive donor: `RequestProject.Provenance` (`RefKind`, `Ref`, `RKB`,
`select`/`full`/`sourced`/`reliable`).

* `counts_come_apart` — visible 3, source-bearing 2, independent roots 1.
* `two_visible_refs_are_not_independent`, `headcount_quorum_is_not_reliable_quorum`.
* `pattern_in_full_absent_in_reliable` — a derived fact asserted in `full`, still
  present in `sourced`, gone in `reliable`, because an `imported from Wikimedia
  project` note is not a source. A typed residual, not a confidence discount.
* `adequacy_policy_separates` — adequacy is a property of the (evidence, policy)
  pair.

### 2.5 `PrunedGraphPromotionTransport` — sound ≠ complete, in the chain

Donor kernels: `Integration.Kernel.PromotionTransport`.
Archive donor: `RequestProject.Provenance`'s `KB.isSubclassOf_mono` /
`KB.isInstanceOf_mono` and the derivation engine.

* `pruned_is_sound_for_instances` / `…_for_subclasses` — soundness for **all**
  pairs, from the archive's monotonicity lemmas; not a spot check.
* `pruned_is_not_complete`, `soundness_receipt_is_not_completeness_receipt`,
  `absence_in_pruned_is_not_absence_in_full`.
* `positive_answer_promotes` (a full four-obligation `Receipt`) versus
  `negative_answer_does_not_promote` (`IsEmpty` of the corresponding receipt).

### 2.6 `WikibaseZelphBraidedPromotion` — the capstone

Donor kernels: `Integration.Kernel.PromotionTransport` (and the braided-strand
motif).
Archive donors: `RequestProject.Ranks` (native plane) and the engine (graph
plane).

* `strand_assignment_compiles_to_receipt` — four typed strand-local obligations
  (native / graph / review / policy) compile into an ordinary receipt.
* `native_receipt_does_not_give_graph_completeness`.
* `graph_soundness_does_not_give_native_semantics` — the graph derives a typing
  for which *no truthy* native statement exists (the only one asserting it is
  deprecated).
* `peer_exact_does_not_give_policy_authority` — with `PolicyAuthority`
  **stipulated** empty for this fixture (see §5).
* `full_receipt_does_not_determine_provenance_assignment` — no function from
  receipts to assignments is a left inverse of compilation: two distinct
  discharging assignments compile to the same receipt.

### 2.7 `SchemaCoverageProfile` — named coverage schema, per-query closure

Donor kernels: `Integration.Kernel.PartialIdentification`.
Archive donor: `RequestProject.Schemas` (`Shape`, `conformsB`, `conformsB_iff`,
`specOkB_iff`).

* `conformance_gives_query_coverage` — general in base, schema, item and query.
* `schema_complete_for_one_query_is_not_complete_for_every_query`.
* `coverage_closes_a_consumer_on_a_nonsingleton_fibre`.

### 2.8 `CoverageResidualSalience` — which residual is worth resolving

Donor kernels: `Integration.Kernel.Welds.ResidualSalienceScheduler`.
Archive donor: `RequestProject.Ranks` (the consumer whose closure defines
salience).

Seven concrete residual kinds; the fixture is "many peer rows, one missing
family-coverage receipt".

* `magnitude_greedy_picks_the_inert_residual` versus
  `salience_greedy_picks_the_coverage_residual`.
* `consumer_closes_after_coverage` — salience here *is* closure of the truthy
  consumer, not a heuristic score.
* `salience_is_live_set_relative`; `selection_is_not_payment` and
  `salience_does_not_imply_admission` — the scheduler firewall.

### 2.9 `ContentIdentityRevisionSync` — four identity coordinates

Donor kernels: `Integration.Kernel.AppendOnlyHistory`.
Archive donors: `RequestProject.Archive` (`digestOf`), `RequestProject.Publish`
(`jsonlOfKB`), `RequestProject.Sync` (`KB.Equiv`).

* `same_canonical_content_gives_same_content_identity` (the only implication
  that holds).
* `semantic_equivalence_does_not_give_content_identity` — two replicas entailing
  each other with different digests.
* `content_identity_does_not_give_revision_identity`.
* `later_receipt_is_not_earlier_possession` — non-retroactivity of alignment
  receipts, and `correction_appends_rather_than_rewrites`.

### 2.10 `WorklistDeliberativeMoves` — report status as a deliberative move

Donor kernels: `Integration.Kernel.Welds.DeliberativeMoves`.
Archive donors: `RequestProject.Reports` (`Severity`, `Status`, `Row`),
`RequestProject.Worklist` (`Task`, `tasks`, `Task.errors`, `Task.provenFixes`).

The archive already separates *reportable* (`Severity`) from *repairable*
(`Status`), and within repairable separates a fix **proved** to change no
derived fact from a mechanical one that changes the data from one that needs a
human.  That is what licenses the weld.

* `statusMove` — `provenFix ↦ reformulate` (a fix that changes no derived fact
  re-presents the question without touching the live fibre), `suggestedFix ↦`
  a search/test move, `needsReview ↦ ask`; `statusMove_injective` and the two
  "not a search move" separations quoted from the weld.
* `severity_does_not_determine_move` and `move_does_not_determine_severity` —
  the two coordinates are independent in both directions.
* `task_counts_separate` — on the fixture the archive's own `Task.errors` and
  `Task.provenFixes` give `(2,2,1)` and `(1,0,1)`: size, severity profile and
  repairability profile are three different readings of one queue.
* `worklist_membership_is_not_information_gain` — a queue of proven fixes is
  entirely reformulation, and reformulation leaves the fibre unchanged, so
  membership supplies no narrowing and no authority.

The mapping `statusMove` is flagged in the file as a modelling choice argued
from the archive's docstrings, not derived from them.

---

## 3. Dependency and provenance map

```
RequestProject.Ranks ─────────────┬─→ Aristotle.PropertyFamilyQueryFibre ──→ Kernel.PartialIdentification
   (truthy semantics)             ├─→ Aristotle.RankVisibilityCommutingProvenance ──→ Welds.CommutingProvenanceSquare
                                  ├─→ Aristotle.CoverageResidualSalience ──→ Welds.ResidualSalienceScheduler
                                  └─→ Aristotle.WikibaseZelphBraidedPromotion ──┐
RequestProject.Snaks ─────────────→ Aristotle.SnakAbsenceInformationLoss ──→ Bridges.InformationLossLocus
RequestProject.Provenance ────────┬─→ Aristotle.ReliableSourceConsumerAdequacy ──→ Kernel.EvidenceDependence
   (RefKind/RKB/full/sourced/     │                                          └──→ Bridges.QuorumThreshold
    reliable, KB monotonicity)    └─→ Aristotle.PrunedGraphPromotionTransport ──┬→ Kernel.PromotionTransport
RequestProject.Schemas ───────────→ Aristotle.SchemaCoverageProfile ──→ Kernel.PartialIdentification
RequestProject.{Archive,Publish,Sync} → Aristotle.ContentIdentityRevisionSync ──→ Kernel.AppendOnlyHistory
RequestProject.{Reports,Worklist} ────→ Aristotle.WorklistDeliberativeMoves ──→ Welds.DeliberativeMoves
```

Authority tiers are respected in the direction the archive audit sets out: the
archive's **T1** generic laws (`conformsB_iff`, `specOkB_iff`, `isInstanceOf_mono`,
`entails_noValue_iff`, `valuesOf_eq_nil_of_noValue`, the `sourced`/`reliable`
inclusions) are used as theorems; the archive's **T2/T3** pinned corpus facts and
worked fragments are *not* used at all — every fixture in this round is defined
in its own file. No `native_decide` was used; no fact about the pinned generated
corpus was promoted to a law.

---

## 4. The Agda return

Five reverse owners, one validation owner and one additive rollup were written:

* `Agda/DASHI/Core/AristotlePropertyFamilyQueryFibreBidiExact.agda`
* `Agda/DASHI/Core/AristotleSnakAbsenceInformationLossBidiExact.agda`
* `Agda/DASHI/Core/AristotleReliableSourceConsumerAdequacyBidiExact.agda`
* `Agda/DASHI/Core/AristotlePrunedGraphPromotionTransportBidiExact.agda`
* `Agda/DASHI/Core/AristotleWikibaseZelphBraidedPromotionBidiExact.agda`
* `Agda/DASHI/Core/AristotleWikidataReciprocalGardenValidation.agda`
* `Agda/DASHI/EverythingAristotleWikidataReciprocalGarden.agda`

**Status, stated exactly.** These are *Agda source*. No Agda toolchain exists in
this environment, so **no Agda kernel receipt is claimed for any of them**, and
no Lean receipt is transported into Agda: each Agda obligation is discharged by
its own Agda term, which remains unchecked until an exact-head Agda build runs.
Each file says so in its header. The rollup is additive: no historical aggregate
was edited to accommodate it.

Mechanically checkable facts about them: `scripts/agda_import_check.py` resolves
every import line of the seven new files against the shipped module set, and the
corpus-wide unresolved count is **unchanged** at 241 in 67 files (14 028 files,
105 718 import lines scanned, 15 568 module files present).

---

## 5. Claim boundaries

* Every fixture (`worldA`, `cohort`, `prunedModule`, `layerA`, the four live
  worlds, the two replicas, the strand table) is a finite object defined in its
  own file. Nothing asserts anything about live Wikidata content, and the
  Q/P identifiers are labels.
* `PolicyAuthority` in the capstone is a **stipulated** empty carrier: the
  fixture grants no migration authority. This is a modelling choice, not a
  derived fact, and it is the one place in the tranche where a firewall rests on
  a stipulation rather than on the archive's semantics.
* `Inhabits`, `Holds` and the promotion obligations are the kernel's stipulated
  predicates; a promotion receipt in this development is a proof term of a
  finite structure, not a claim about any external artefact.
* The Lean results are *not* Agda results. Cross-language transport remains an
  open obligation for the whole corpus.

---

## 6. Frontier: exact remaining obligations

1. **No Agda kernel receipt.** The seven new Agda files, and the corpus at
   large, remain unchecked here. Needed: an Agda toolchain and an exact-head
   build. Until then the Agda tranche is source, not proof.
2. **Several archive subsystems remain unexploited.** `RepairWorkflow`,
   `RepairReview`, `Defects`, `Diagnostics`, `Matching`, `SoftIdentity`,
   `Taxonomy` and the ontology-topology tranche are integrated and unread by
   this round. `Reports`/`Worklist` were read and used (§2.10), but only their
   status/severity layer: the repair-workflow state machine, which is where an
   *executable* versus *authorised* distinction would have to come from, is
   untouched, so nothing here says anything about execution authority beyond
   "membership is not narrowing".
3. **Sync's merge is used only through `Equiv`.** If `Sync`'s merge lattice is
   to instantiate the commuting-square discipline (a provenance-preserving
   merge), that is an unmet obligation: `sync_least`, `sync_assoc_equiv` and
   friends are available but nothing yet exhibits the square.
4. **Coverage residuals are not connected to the query-residual compiler.**
   `Integration.Kernel.QueryResidual` computes first residual → obligation →
   producer; the Wikidata residual kinds of §2.8 are not yet wired into that
   compiler, so "reopen only the failed promotion stage" is still generic.
5. **No quantitative statement anywhere.** No degree-of-identification scalar,
   no confidence, no aggregation arithmetic across strands. The tranche
   deliberately keeps "more identified" structural (nested fibres, closure of a
   named consumer) rather than numeric.
6. **The unresolved Agda import edges are unchanged**: 241, of which 65 are
   YM/NS-named and out of scope, 113 point into `Moonshine` and 91 into
   `Physics` (archive-boundary effects), with 13 `Cognition`, 11 `Foundations`,
   8 `Algebra` and four singletons. Nothing was edited to make that number
   smaller.
7. **The contextual-Fractran edge, classified rather than repaired.**
   `DASHI/Cognition/PNF/ContextualFractranHyperformalismEverything.agda` imports
   both `DASHI.Cognition.PNF.ContextualFractranPNFHyperfabric369Exact` (absent)
   and `DASHI.Interop.ContextualFractranPNFHyperfabric369Exact` (present, and
   itself importing three `Cognition.PNF` siblings). Because the aggregate
   imports *both*, the evidence points to a module genuinely absent from this
   cutset rather than to a rename or a move, so the honest classification is
   **actually missing, pending upstream**. No stub was manufactured and the
   aggregate was not edited.

---

## 7. Build and audit record

* `lake build` (all default targets, now including `AristotleArchive`):
  **8 540 jobs, no errors.**
* The previously documented failure — the `AgdaMirror` root aggregate importing
  the excluded `AgdaMirror.Physics.YangMills` — is fixed by restoring the
  lakefile glob to `AgdaMirror.+` (submodules only), which is what the comment
  beside it always said. No YM/NS file was read or added.
* `Integration.AxiomAuditAristotle`: 62 `#print axioms` lines, every one either
  axiom-free or a subset of `{propext, Classical.choice, Quot.sound}`.
* `rg` over `Lean/Integration/Kernel/Aristotle/`: no `sorry`, no `axiom`
  declaration, no `native_decide`, no `implemented_by`.
