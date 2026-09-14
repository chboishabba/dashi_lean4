# TOE consolidation round — 2026-09-13

Executable artefacts first; this file only explains them.

| artefact | what it is |
| --- | --- |
| `Lean/Integration/ProvenanceIdentifier.lean` | typed DOI/QID/Dewey/ISBN/arXiv/module identifiers, source-acquisition status, the seven proof-status classes, and the **identity/authority firewall theorems** |
| `Lean/Integration/LineageLedger.lean` | the Lean↔Agda lineage ledger (`Agda owner → Lean carrier → Lean adapter → Lean consumer → status → provenance`) with decided policy theorems |
| `Lean/Integration/CanonicalSpineRegistry.lean` | the canonical-spine registry, checked against the ledger |
| `Lean/Welds/NSRateBlockPiWeld.lean` | NS ⟶ Spine weld: the documented `Fin 3 → ℂ` carrier seam, closed |
| `Lean/Welds/ReachabilityCarrierWeld.lean` | chemistry ⟷ reachability-carrier weld, both directions |
| `Lean/Welds.lean` | opt-in weld rollup with `#print axioms` receipts |
| `NSCutset` lake library | opt-in build surface for the preserved NS rate-block cutset (30 modules, donor payload, not copied) |
| `LINEAGE_LEDGER_20260913.csv` | the ledger, serialised from the Lean module by `scripts/lineage_ledger_csv.lean` |
| `CONSOLIDATION_INTAKE_20260913.csv` / `.json`, `CONSOLIDATION_ADOPTION_20260913.csv` | per-path intake and adoption disposition for the delivered bundle |

## 1.  Delivery

`toe-agda-lean-consolidation-20260913.tar.gz`, sha256
`bf25f24ac5b129e1383290495ead4ef592e2302370d5701742d7245b560a41d6`, unpacked to
`dashi_agda/` (`96511f784`, `master`) and `dashi_lean4/` (`ff0b3a02`, `main`)
plus `HANDOFF.md` and `TOE_CONSOLIDATION_BRIEF.md`, both preserved verbatim under
`Provenance/consolidation-20260913/`.

**One delivery gap, reported rather than smoothed.**  The handoff declares
"adjacent `SOURCE_MANIFEST.txt`", "adjacent `SHA256SUMS`" and
"`ARCHIVE_SHA256SUM.txt`".  None of the three was delivered with the bundle or
is present in this tree, so *no manifest/checksum verification of this delivery
was possible*.  What is recorded instead is the sha256 of the archive as
received (above) and a full per-path sha256 index of the unpacked payload
(`CONSOLIDATION_INTAKE_20260913.csv`).  Every earlier tranche in this corpus was
verified against its own receipts; this one could not be.

## 2.  Intake, measured

`scripts/consolidation_intake_20260913.py` hashes every delivered `.agda` and
`.lean` against the corpus:

| side | identical | divergent | absent locally | local-only |
| --- | --- | --- | --- | --- |
| Agda | 16 023 | 137 | **952** | 1 363 |
| Lean | 183 | 13 | 8 259 | 8 828 |

The Lean numbers are path-shift artefacts of the vendored
`ImportedLeans/aristotle-results/` trees (the donor even ships a copy of this
project's own previous output, `toe-fb55001e-20260912`); excluding
`ImportedLeans/`, the donor brings exactly **two** new first-party Lean modules,
and all thirteen divergent Lean files are aggregates/audits where **our version
is the superset** except for the two imports below.

`scripts/consolidation_adopt_20260913.py` then applies the standing policy —
adopt new modules verbatim; adopt a divergent donor only when it is a superset
of the local declarations and imports; otherwise keep local and preserve the
donor verbatim:

* **952 Agda modules adopted** (Physics 334 — including the Balaban YM rounds and
  the centered NS route —, Wikimedia 225, ComputerScience 120, Culture 110,
  Biology 39, Reasoning 20, Law 16, and eleven smaller lanes);
* **97 divergent Agda files adopted as donor supersets**;
* **40 kept local**, donor version preserved under
  `Provenance/consolidation-20260913/donor-version/` with both hashes and the
  local-only declaration names recorded in `CONSOLIDATION_ADOPTION_20260913.csv`;
* **2 Lean modules adopted**: `Synthesis/MonsterCharacterDetermination.lean` and
  `Synthesis/MonsterCharacterMultiplicityRegression.lean`, now imported by
  `Synthesis.lean` and audited in `Synthesis/AxiomAudit.lean` (all four headline
  theorems: `[propext, Classical.choice, Quot.sound]`).

No Agda typechecker exists in this environment, so every Agda statement here is
a source reading or a hash comparison, never a kernel receipt.

## 3.  Consumers unlocked

### 3.1  The NS rate-block cutset now builds here

The 2026-09-12 tranche delivered `SlotKernelAntiParallel`,
`SpineRateBlockAdapter` and `GramConsumerFactorisation`, and the previous round
reported them as import leaves with **no build surface** in this project.  Their
transitive closure is 30 modules with exactly three external dependencies —
`Mathlib`, `Spine.RateBlockSchur`, `Proposed.FibreRoutingProjectionAdapter` —
all present here, and the donor pins the same toolchain (`v4.28.0`) and the same
Mathlib revision.  A new opt-in `NSCutset` library points `srcDir` straight at
the preserved donor payload (no copy, no parallel definition) and

```
lake build NSCutset     →  Build completed successfully (8058 jobs)
```

so for the first time the NS adapter chain has a kernel receipt in this tree.
This also gives `Proposed.FibreRoutingProjectionAdapter` — previously "a checked
prototype with no named consumer" — its first real consumer,
`RequestProject.NavierStokes.GramConsumerFactorisation`.

### 3.2  The `Fin 3 → ℂ` carrier seam, closed

`SpineRateBlockAdapter` records a mismatch it deliberately does not repair: the
inner-product form of the Spine kernel does not apply to the NS cells, because
`Fin 3 → ℂ` carries Mathlib's sup-norm `Pi` instance, and "repairing the
mismatch would mean transporting the lane to `EuclideanSpace ℂ (Fin 3)`, which
is a separate (and much larger) refactor of every NS file."

`Spine.RateBlockSchurPiCarrier` already owned the `WithLp.toLp 2` transport.
`Welds.NSRateBlockPiWeld` welds the two and shows the refactor is not needed:

* `herm_eq_hermPi`, `nsq_eq_nsqPi`, `nrm_eq_nrmPi` — the lane's pairing, mass and
  norm **are** the carrier's, by `rfl`;
* `ns_herm_eq_euclidean_inner`, `ns_nrm_eq_euclidean_norm` — hence they are the
  `EuclideanSpace ℂ (Fin 3)` inner product and norm.  The sup-norm instance is
  never used, so no NS file changes;
* `gramOperatorBound_of_pair_estimate` — the factorisation the donor lacked: the
  viscous-rate massaging, which was written inline twice (in `RateBlockGramBound`
  and again in `SpineRateBlockAdapter`), isolated once as a lemma taking the pair
  estimate as hypothesis;
* `gramOperatorBound_viaPiCarrier` — the literal consumer
  `ClayNS.Schur.GramOperatorBound nu modes G k (32·m)` paid along the Euclidean
  route;
* `spineAdapter_consumer_refactored`, `gramOperatorBound_routes_agree` — the
  donor's own consumer theorem re-derived from the factorisation, and all three
  routes shown to prove the same proposition, so two of the three copies are
  redundant rather than parallel.

Receipts (printed by `Welds`): all seven headline theorems depend on exactly
`[propext, Classical.choice, Quot.sound]`.  **No Clay obligation is closed and
none is claimed**; the bound is still the cancellation-free one, degrading
linearly in the block multiplicity.

### 3.3  Cross-lane reuse: reachability

Two independent encodings existed: the carrier
`Integration.ReachabilityBarrier` (`ActionSystem` + `Reachable` + language
monotonicity + the invariant barrier), through which
`Integration.LanguageReachability` already factors, and
`Integration.ChemistryReachability`, a decidable bounded procedure stated
against `Relation.ReflTransGen`.  Nothing joined them.

`Welds.ReachabilityCarrierWeld` supplies the transport
(`reachable_ofStep_iff_reflTransGen`, an iff, not an analogy) and then both
directions of reuse: the chemistry procedure becomes a producer for the carrier,
decides it at the lane's own fixpoint hypothesis, and — the reverse direction —
the carrier's invariant barrier and language index transport into the chemistry
vocabulary, where neither was statable before.  The retained negative
(`reachB_accept_not_language_free`) keeps the language-relativity honest.

### 3.4  `AgdaMirror` root aggregate

`Lean/AgdaMirror/Physics/YangMills.lean` had its module doc comment *before* its
imports, which is not legal Lean; this had made the whole `AgdaMirror` root
aggregate unbuildable for several rounds while the five submodules elaborated
fine.  Comment moved, aggregate confirmed to elaborate, `AgdaMirror` root
promoted into the library glob.  `lake build` over all seven default targets now
succeeds.

## 4.  Registry, ledger, and the identity/authority firewall

`Integration.ProvenanceIdentifier` makes the identifier layer typed, and proves
what it is *not*:

* `provenance_does_not_determine_status` — no function computes proof status
  from provenance;
* `status_invariant_under_reprovenance` — re-attribution changes nothing;
* `wellFormed_provenance_does_not_determine_status` — a fully well-formed
  DOI/QID/Dewey provenance is compatible with having no Lean receipt;
* `receipt_without_provenance`, `acquisition_does_not_determine_status` — and a
  proved theorem may cite nothing.

The Agda owner of this discipline,
`DASHI.Interop.CrossLaneProofArchaeologyLedgerExact`, states it as `Bool` fields
pinned by `refl` (`sourceIdentityCoordinateOnly`, `qidCoordinateOnly`,
`deweyCoordinateOnly`, `firstLinkCreatesTheoremImplication = false`,
`funnelRankCreatesAuthority = false`).  Those pins are now theorems.

`Integration.Lineage.ledger` carries the lineage rows; `Integration.SpineRegistry.registry`
carries canonical ownership.  Both are checked, not asserted:

| theorem | what it enforces |
| --- | --- |
| `Lineage.canonical_ownership`, `SpineRegistry.registry_key_determines_carrier` | **no parallel definitions**: one carrier per structure key |
| `Lineage.proved_rows_name_a_receipt` | a status that asserts Lean content names a Lean declaration (structural: the constructor holds the name) |
| `Lineage.receipted_rows_have_a_consumer` / `…_carrier` | nothing is filed as closed without a consumer and a carrier |
| `Lineage.payments_have_no_receipt`, `false_pins_record_payments` | open/false-pinned/conjectural rows carry no receipt, and a pin is never bare |
| `SpineRegistry.ledger_carriers_registered`, `registry_keys_in_ledger` | ledger and registry agree in both directions |
| `SpineRegistry.reachability_carrier_is_shared`, `declared_carrier_is_shared` | the measured reuse: three lanes each |

The registry is deliberately *not* a whole-garden build target: `Spine`,
`Synthesis`, `Cuisine`, `Integration`, `Promoted`, `AgdaMirror`,
`AristotleArchive` are the default targets; `Welds` and `NSCutset` are opt-in.

## 5.  Status ledger, by class

From `LINEAGE_LEDGER_20260913.csv` (23 rows):

* **proved theorem** (9): `euclidean-pi-carrier`, `gram-ledger-two-presentations`,
  `monster-order-factorisation`, `declared-carrier-exhaustiveness`,
  `publication-fail-closed`, `reachability-closure`,
  `language-indexed-reachability`, `identifier-authority-firewall`,
  `attributed-source-non-promotion`;
* **conditional compiler** (7): the NS rate-block chain
  (`rate-block-schur-kernel`, `gram-consumer-from-pair-estimate`,
  `slot-kernel-anti-parallel`, `gram-profile-consumer-factorisation`),
  `gronwall-comparison`, RH `taper-second-moment`,
  `character-determines-simple`;
* **no-go** (1): `channel-dependent-provenance`;
* **false-pinned** (3): `nested-slot-class-norm-payment-584`
  (`round584AnyLiveNestedSlotClassNormPaymentConstructed = false`,
  `round584ClayPromotion = false`), `clay-terminal-cutset-504`
  (`round504ClayPromotion = false`), `ym-clay-promotion`
  (`clayYangMillsPromoted = false`);
* **open payment** (2): `centered-partner-difference-route`,
  `ym-quantitative-clustering`;
* **conjectural** (1): `rh-statement` — RH remains unproved, and the Agda
  Lean-return receipt is provenance, not transported proof.

## 6.  Ranked unresolved seams

Ranked by `real consumers unlocked × duplicate structure removed × genealogy
clarity ÷ new abstraction cost`.

1. **NS truncation-uniform constant from signed cancellation.**  Every route to
   the Gram consumer is cancellation-free, so the constant degrades linearly in
   the block multiplicity; `gramOperatorBound_fails_on_comparable_shells` is a
   proved obstruction, not a gap.  A cancellation-aware carrier is the single
   highest-value next payment, and it would be consumed immediately by all three
   existing routes.
2. **Centered partner-difference route (`NSTriadKNCenteredPartnerDifferenceAdapterExact`,
   `…PartnerSlotDefectExact`, adopted this round).**  No Lean carrier exists; the
   Agda material is typed and current.  Transporting the slot-defect identity is
   the obvious next Lean carrier.
3. **R582/R584 vector class-norm budget.**  Still false-pinned; the transport
   requires material not present in either tree.
4. **YM quantitative clustering → mass gap.**  126 Balaban modules arrived this
   round, including `BalabanClayDirectQuantitativeClusteringRound274Exact` and
   `BalabanPairwiseClusteringStandardMassGapRound305Exact`; there is no Lean
   carrier for any of it, and the CMP98/109/116 source-object binding is the
   declared blocker in the Agda router.
5. **RH explicit-cutoff near/far transport onto the Agda carrier.**
   `Spine.RiemannBridge` owns the taper second-moment inequalities; the
   near/far cutoff transport is the named next step in the Agda `rhRouter`.
6. **NS outer-spectator / weight spacetime seam** and **R145 intra-shell L²
   aggregation** — unchanged and untouched.

## 7.  New reverse-reuse opportunities recorded

* `Integration.DeclaredCarrier` (exhaustive-of-declared-carrier transfer) is
  already shared by cuisine, education and Wikidata; the 225 newly adopted
  `DASHI/Wikimedia/*` modules are atlas-shaped and are candidates for the same
  adapter.
* `Integration.ReachabilityBarrier` now serves chemistry, cognition and biology
  shapes; the adopted `DASHI/ComputerScience/Godel*` frontier modules are
  reachability/diagonalisation-shaped and should be checked against it before
  any new encoding is written.
* `Spine.RateBlockSchurPiCarrier` is stated for arbitrary `n`; any other lane
  working in `Fin n → ℂ` with a hand-rolled Hermitian form can drop its private
  Cauchy–Schwarz the same way the NS lane just did.
* `Integration.ProvenanceIdentifier` should absorb the remaining `String`-typed
  identifier fields in `Cuisine.SourceAtlas` and the Wikidata mirrors; those are
  bookkeeping rows today.

## 8.  Boundaries

No Clay problem is advanced in any direction, and none is claimed.  No physical
or empirical claim is made.  Every Lean statement above is backed by a build in
this tree; every Agda statement is a source reading, since no Agda toolchain
exists here.  No `sorry`, `admit`, `axiom` or `native_decide` was added; all new
modules are `sorry`-free and their axiom receipts are printed by the `Welds`,
`Integration.AxiomAudit` and `Synthesis.AxiomAudit` modules.
