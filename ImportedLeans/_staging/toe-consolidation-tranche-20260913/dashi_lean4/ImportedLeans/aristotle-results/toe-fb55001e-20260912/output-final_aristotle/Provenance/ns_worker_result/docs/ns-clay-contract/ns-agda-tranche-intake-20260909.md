# NS Agda source tranche — intake, review and selective import (2026-09-09)

This record supersedes `source-tranche-audit.md`, which recorded that the announced
tranche was **absent** from the project. On this pass the archive **is** present and
has been unpacked, checked and selectively imported.

## 1. Attachment, as received

| item | value |
|---|---|
| archive | `ns-agda-tranche-20260909.tar.gz` (4,719,847 bytes), at the project root |
| tar entries | 3,234 (3,229 regular files + 5 directory entries) |
| regular files | 3,229 = **3,226 `.agda` sources** + `HANDOFF.md` + `SOURCE_MANIFEST.txt` + `SHA256SUMS` |
| manifest lines | 3,226 — one per `.agda` source, matching the extracted set exactly |
| checksums | `sha256sum -c SHA256SUMS` → **3,226/3,226 verified, 0 mismatches** |
| **HANDOFF source commit** | **`74c7bee33ddd4877181ab332628909a9e6425b63`** (`chboishabba/dashi_agda`, 2026-09-09) |
| tree shape | `dashi_agda/DASHI/{Core (2), Physics (1), Physics/Closure (3,223)}` |
| build output | none — source-only, as `HANDOFF.md` states (no `.agdai`, no caches) |

The archive was unpacked **beside** the project (outside the returned tree) and nothing
in the working tree was overwritten before the file-by-file review in §2 was complete.

## 2. Review before import

Comparing the 3,226 donor sources against the project's existing Agda tree
(13,306 `.agda` files before intake):

- **3,067** donor files were already byte-identical in the project;
- **159** donor files were **new** (NS-lane rounds **395–530**, plus
  `DASHI/Core/ClayCrossDomainLiteralFrontierExact.agda`,
  `DASHI/Physics/NSYMLiteralFrontierSchedulerExact.agda`, two citation-audit modules);
- **138** files existed in both but **differed**.

Mechanical safety review of the 159 new files:

- `postulate` declarations: **0**;
- `{-# TERMINATING #-}` / `NON_TERMINATING` / `primTrustMe` / `--type-in-type` /
  `--no-positivity`: **0**;
- promotion bookkeeping: **no** `PackageAClosed = true` and **no** `ClayPromotion = true`
  anywhere in the new material (every occurrence is `= false`).

The 138 differing files were split by whether they lie in the transitive import closure
of the new material (37 do, 101 do not), and each of the 37 was diffed by hand.
Two directions of divergence were found, and they go **opposite ways**:

- the donor carries repairs the project lacks — e.g. in
  `NSTriadKNAdverseEpisodeSignedForcingRound106Exact` and
  `NSTriadKNInteriorEpisodeBudgetEquivalenceExact` the donor replaces
  `Tactic.RingSolver` `solve` calls by explicit `Data.Rational.Properties` chains;
- **the project carries repairs the donor lacks** — in
  `NSTriadKNFiniteRadialTransferExteriorRound102Exact` and
  `NSTriadKNThreeRadiusTransferExteriorRound102Exact` the project copy carries an
  explicit repair note replacing `solve` calls whose first argument was a list of
  *record projections* (`solve (eigenvalue x ∷ energy x ∷ …)`) — a form
  `Tactic.RingSolver.solve` rejects — by ring identities over genuine free variables
  threaded with `trans`/`cong`. The donor still has the rejected form.

## 3. What was imported, and what was not

| tier | count | action |
|---|---|---|
| new donor modules (rounds 395–530 and friends) | 159 | **imported** |
| differing modules inside the new material's import closure | 35 | **updated to donor** |
| `DASHI/Physics/Closure/Everything.agda` (donor is a strict superset: 84 imports vs 13, no project-only entry, all 84 resolve after intake) | 1 | **updated to donor** |
| project-repaired modules the donor would regress (§2) | 2 | **kept as-is** |
| differing modules outside the closure | 101 | **kept as-is** — not needed for the new material, and adopting them was not reviewed here |

Result: the project's Agda tree goes from 13,306 to **13,465** `.agda` files.

## 4. Dependency completeness of the imported set

`import` graph of the 159 new modules resolved against the post-intake tree: **7**
referenced modules exist in neither the tranche nor the project —

```
DASHI/Analysis/RiemannAristotleRHFinalAllowanceLeafSchedulerExact.agda
DASHI/Analysis/RiemannG2PoleQuotientFinalCutReconciliationExact.agda
DASHI/Core/LiteralFrontierSchedulerExact.agda
DASHI/Core/ProofSearchExperimentalParetoCrossPollinationExact.agda
DASHI/Core/QueryPromotionResidualBidiExact.agda
DASHI/Physics/Plasma/MHDMagneticVectorPotentialHelicalObserverExact.agda
DASHI/Wikimedia/ScientificCitationQidBindingsExact.agda
```

12 of the 195 imported/updated modules depend on one of these transitively and are
therefore **not** dependency-complete even in principle:
`ClayCrossDomainLiteralFrontierExact`, `NSYMLiteralFrontierSchedulerExact`,
`NavierStokesCitationIdentityAuditExact`, `NavierStokesSourceEntityQidBindingsExact`,
`NSTriadKNLiteralFrontierSchedulerRound443Exact`,
`NSTriadKNMHDRadiusReciprocalToNormalizedDirectionRound464Exact`,
`NSTriadKNPhysicalNormalizedAntiParallelComplementRound467Exact`,
`NSTriadKNPhysicalHHAndNestedRadiusCompilerRound468Exact`,
`NSTriadKNCauchyResolvedTerminalEverythingRound479Exact`,
`NSTriadKNCauchyResolvedProofSearchRound481Exact`,
`NSTriadKNCauchySignedFluxProofSearchRound485Exact`,
`NSTriadKNCanonicalClayProofSearchRound486Exact`.

None of them is in the R423 signed-companion family of §5; that family is
dependency-complete against the post-intake tree.

## 5. The R423 / cutoff-uniform signed-companion family

Imported (all dependency-complete):

```
NSTriadKNQuadraticCompanionSignedHeatToBarrierRound423Exact   -- the R423 target itself
NSTriadKNFixedOutputPaymentsToR423Round487Exact
NSTriadKNR423FixedOutputProducerProofSearchRound488Exact
NSTriadKNR423LocalPaymentPrerequisiteRound489Exact
NSTriadKNStrictFixedOutputCompanionToR423Round492Exact
NSTriadKNStrictR423ProofSearchRound493Exact
NSTriadKNDirectResolventCompanionToR423Round501Exact
```
together with the direct-resolvent companion chain R496–R503, the Cauchy-resolved
chain R477–R485, and the Gram-operator consumer/payment pair R471/R472.

**What R423 actually is.** `QuadraticCompanionSignedPayment` is a *record of
hypotheses*: the cutoff-uniform budget
`4 · ∫ companionCross(cutoff, terminal) ≤ bound(terminal)` is a **field**, not a
derived result. The module's content is the plumbing — that such a payment transports
to `R421`'s barrier and then to the `Round104` uniform critical family — plus a
`SchurCriticalProducer → QuadraticCompanionSignedPayment` converter that is one
`ℚP.≤-trans`. Nothing in the family produces the budget.

The donor's own bookkeeping says exactly this, and it agrees with our frontier:

```
round489SignedSpacetimeEstimateClosed        = false
round489CutoffUniformBudgetSumClosed         = false
round492R423SignedCompanionBudgetClosed      = false
round493StrictR423ProducerClosed             = false
round501DirectCompanionBudgetClosed          = false
round501RemainingNovelLeafIsCutoffUniformDirectCompanionBudget = true
round471PhysicalOuterCellGramBoundClosed     = false
round472FirstPhysicalScalarPolarizationBoundClosed  = false
round472SecondPhysicalScalarPolarizationBoundClosed = false
```

Where the donor marks a *compiler* closed, our Lean side already has the corresponding
reduction as a real theorem rather than a flag: `round471TwoPolarizationCompilerClosed`
and `round472TwoPolarizationToR432CompilerClosed` correspond to the transverse-frame
split in `RequestProject/NavierStokes/TransverseFrameSplit.lean`, which reduces the
vector Gram form to two scalar polarization channels. What is open on both sides is
the same object: the physical, truncation-uniform bound on those channels.

One flag *does* move in the reconciled state: in
`NSTriadKNForcingSlotKernelRound307Exact` the donor sets
`round307PhysicalProjectedNSForcingTransversalityWeldClosed = true` where the project
copy had `false`, but the same donor file simultaneously introduces
`round307AllOuterCellsMeetCompilerHypotheses = false`. The flip is therefore a
*conditional compiler* claim, not a physical one, and `round307PackageAClosed` and
`round307ClayPromotion` remain `false`. It is imported as donor provenance and is
**not** relied on anywhere.

The exact lists of what was imported and what was reconciled are in
`build-support/ns-agda-tranche-20260909-imported.txt` (159 paths) and
`build-support/ns-agda-tranche-20260909-reconciled.txt` (36 paths).

## 5b. What kind of material the 159 new modules are

A coarse classification by content (counting `record` declarations, top-level
`Bool` flags, and uses of `Data.Rational.Properties` / `RingSolver`):

| kind | count |
|---|---|
| conditional interfaces: a `record` whose fields *are* the estimates, plus transport lemmas between such records | 97 |
| Boolean bookkeeping only (flags plus their `refl` witnesses) | 40 |
| modules carrying real rational-arithmetic derivations | 22 |

The 22 arithmetic-bearing modules are genuine but elementary — e.g.
`NSTriadKNRationalPhysicalPairRatePositivityRound400Exact` constructs, rather
than assumes, positivity of the R291 pair rate on a nonzero output fibre from
positivity of the viscosity and the inverse-square mode law. None of them
supplies a cutoff-uniform bound; that leaf stays a record field everywhere it
appears.

## 6. Status of the imported material — no kernel receipt

**No Agda kernel was run on any of this.** No Agda toolchain is present in this
environment, and none of the checks above is a substitute for type checking: they are
a text-level provenance, safety and dependency review. Nothing in §1–§5 is a receipt,
and the imported Booleans and record types are bookkeeping and conditional interfaces,
not proofs.

## 7. Frontier preserved

The Lean NS frontier is unchanged by this intake. The whole project was rebuilt after
the import: **8,197 jobs, build completed successfully, no errors and no warnings**,
and `RequestProject/` contains no `sorry`, no `axiom` and no `@[implemented_by]`.
The standing non-closure claims are untouched:

- `ClayNS.RateBlocks.gramOperatorBound_of_rateBlockMultiplicity` — the truncation-uniform
  Gram-operator bound holds with `A = 32·m` *under* a dyadic rate-block multiplicity
  bound `m`, by a cancellation-free Schur test;
- `ClayNS.RateBlocks.gramOperatorBound_fails_on_comparable_shells` — with no
  multiplicity hypothesis the bound is false: on comparable shells the required
  constant is forced above any `N`;
- `ClayNS.RateBlocks.gramOperatorBound_of_cluster_cancellation` /
  `cluster_cancellation_of_gramOperatorBound` — at a degenerate rate cluster the bound
  is *equivalent* to cancellation of the aggregated cells.

So the physical remaining payment is still the truncation-uniform outer-cell
Gram-operator bound (equivalently the two scalar polarization bounds), which is
precisely the leaf the donor also marks open. **Package A and the literal periodic
Clay regularity target remain unclosed, and nothing here claims otherwise.**
