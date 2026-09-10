# Full-source cross-pollination intake — donor `1d3cb03c`, 2026-09-10

This round replaces the topic-filtered 2026-09-09 cutset policy. Every path in
the delivered archive is indexed and preserved, whatever its lane: Yang–Mills,
Navier–Stokes, exotic gravity, plasma, law and legal provenance, ecology and
water, photosynthesis/optics, Moonshine and the J-invariant, Gödel/Turing, game
theory, cognition, cuisine and the rest. Nothing is discarded for subject
matter, and nothing is discarded for a missing import closure; where a module
cannot be wired into an aggregate, it is *deferred with the exact missing edge
recorded*, not refused.

Nothing in this document is a kernel receipt for Agda. There is no Agda
toolchain in this environment, so every Agda-side statement below is a
text-level fact about file presence, hashes, import lines and declaration
names. The one thing that *is* machine-checked is the Lean work in §7.

---

## 1. Delivery verification

| item | value |
|---|---|
| archive | `toe-full-crosspollination-agda-state-20260910.tar.gz` (22,152,497 bytes, project root) |
| archive sha256 | `8a48678a163d6ed0eaab72559ab88f8a9c2f32d3be677d9d5b7378247193b325` |
| declared source | `chboishabba/dashi_agda` master `1d3cb03c1dec2d1b1293ada9684b168fd963da8f` |
| `SOURCE_MANIFEST.txt` | 15,956 payload entries = **15,952 `.agda`** + 4 NS-worker files |
| extracted payload | 15,956 files — matches the manifest **exactly**, no extra, none missing |
| `SHA256SUMS` | 15,958 lines (payload + `HANDOFF.md` + `SOURCE_MANIFEST.txt`) |
| `sha256sum -c SHA256SUMS` | exit 0, **15,958/15,958 `OK`**, 0 failed, 0 missing |
| build products in archive | none (no `.agdai`, `.olean`, `.lake`, caches, git metadata) |

The archive was unpacked **beside** the project and compared file-by-file before
anything in the working tree was touched.

Unlike the previous delivery, `ns_worker_result/` is present, listed and hashed:
four files (three markdown reports, one Lean source). They are preserved
verbatim under `Provenance/ns_worker_result/` and discussed in §6.

## 2. Disposition of all 15,952 donor Agda paths

Comparison is by sha256 against `Agda/` (14,158 `DASHI/**.agda` before intake).

| disposition | count | action |
|---|---|---|
| byte-identical to the local file | 12,350 | nothing to do |
| absent locally | **1,822** | **adopted** (copied in) |
| divergent, donor preserves every local top-level declaration **and** every local `DASHI.*` import | **1,752** | **reconciled to donor**, pre-intake local sha256 recorded |
| divergent, donor would drop local declarations or imports | **28** | **local kept**; donor version preserved under `Provenance/donor-1d3cb03c1dec/` with the exact dropped names |
| local-only (in the tree, not in the donor) | 1,568 | untouched, retained |

Post-intake the tree carries **15,980** `DASHI/**.agda` files (17,520 modules
including the vendored `cubical`, `bishop` and `dchott` trees).

Per-path artefacts, all regenerable from `scripts/xpoll_index.py`,
`scripts/xpoll_intake.py`, `scripts/xpoll_frontier.py`:

| file | contents |
|---|---|
| `XPOLL_INDEX.csv` | one row per donor path: sha256 (donor and local), status, lane, module name, line/byte counts, import and declaration counts, `data`/`record`/`postulate`/`TERMINATING`/`primTrustMe`/hole markers, Boolean-ledger and `→ ⊥` counts, dependency completeness |
| `XPOLL_IMPORT_EDGES.csv` | every import edge (122,382 lines; 68,159 `DASHI.*`), each marked `both` / `donor-only` / `local-only` / `unresolved` / `external` |
| `XPOLL_LEDGER.csv` | per-path adoption ledger: action, donor sha256, pre-intake local sha256, donor commit, reason |
| `XPOLL_DIVERGENCES.csv` | all 1,780 same-path divergences, with the local declarations/imports the donor drops |
| `XPOLL_FRONTIER.csv` | the 1,822 adopted modules with dependency status and blocking edges |
| `XPOLL_MISSING_TARGETS.csv` | the 108 module names still imported but absent, with their importers |
| `XPOLL_RELOCATIONS.csv` | the eight missing modules that have a same-basename file elsewhere in the tree, with declared module name, hash and why each is deferred |
| `XPOLL_HUBS.csv` | modules imported from ≥3 lanes — the corpus's actual cross-lane kernels |
| `XPOLL_SHARED.csv` | top-level declaration names occurring in ≥3 lanes |
| `XPOLL_INDEX_SUMMARY.json`, `XPOLL_FRONTIER.json` | aggregate counts |

## 3. What the adopted material is

Mechanical content scan of the 1,822 newly adopted modules (268,271 lines):
**5,054 `data`**, **3,669 `record`**, **0 `postulate`**, **0 `TERMINATING`**,
**0 `primTrustMe`**, **0 open holes**, 2,208 Boolean `… ≡ true` ledger
obligations and 3,689 `… → ⊥` boundary statements.

Adopted-by-lane: Physics 802, Law 180, Cognition 177, Core 143, Biology 79,
Moonshine 71, ComputerScience 59, Culture 59, Interop 54, Environment 51,
Economics 37, Analysis 26, GameTheory 25, Wikimedia 13, Statistics 9, Policy 6,
Governance 5, Chemistry/Foundations/Topology 4 each, Reasoning 3, Crypto 1, plus
8 root-level `Everything*`/cross-pollination modules.

Among the 1,752 **reconciled** files, seventeen carry markers worth naming
explicitly (all were already in the tree in some form; the donor version is the
one now held): eleven with `postulate` — seven `DASHI/Crypto/MLKEM*`, two
`DASHI/Foundations/UBP/*`, `DASHI/Physics/IsotropyInvariant`,
`DASHI/Physics/MaskedCone` — three with `{-# TERMINATING #-}` —
`DASHI/Physics/Closure/NSTriadKNCanonicalTriadOrbitQuotient`,
`…/NSTriadKNSafeCanonicalTriadOrbitQuotientRound34Exact`,
`DASHI/Physics/Toy/ScalarContinuum` — and three whose text matches the
(heuristic) hole pattern. These are **assumptions and pragmas, not proofs**, and
are recorded as such rather than being silently adopted as results.

Across the 15,952 donor paths as delivered: 124 files contain a `postulate`, 8
a `TERMINATING` pragma, 0 use `primTrustMe`. Across the whole indexed tree
after intake (17,521 Agda files), `CORPUS_INVENTORY.md` reports 162 modules
with a `postulate` block — that inventory was itself re-run this round with its
Yang–Mills/Navier–Stokes read-exclusion **retired**, so for the first time every
lane is actually opened and counted (6,402 of the files read are
path-identified YM/NS material, previously counted but never read).

## 4. Dependency/provenance map

Static import resolution over the whole tree (no typechecking):

| quantity | before intake | after intake |
|---|---|---|
| `DASHI/**.agda` files | 14,158 | **15,980** |
| import lines parsed under `Agda/DASHI` | 106,856 | 122,756 |
| files with an unresolved `DASHI.*` import | 67 | **34** |
| unresolved edges | 241 | **153** |
| distinct missing module names | 151 | **103** |
| transitively dependency-incomplete modules | — | **90** of 17,521 |

(Two measures are in play and are kept distinct throughout. The table counts
only what the Agda include root sees — `include: .` and `bishop`, i.e.
`Agda/DASHI/**` — which is what `scripts/agda_import_check.py` reports: 34
files, 153 edges, 103 names. `scripts/xpoll_frontier.py` walks *everything*
under `Agda/`, including the non-root staging areas `Agda/src/` and
`Agda/temp-DOWNLOADED/`, and so reports 108 missing names; the five extra are
modules imported only from inside those staging areas, listed in
`XPOLL_RELOCATIONS.csv`.)

Of the 1,822 adopted modules, **1,821 are dependency-complete** against the
post-intake tree. Exactly one is not, and it is the only deferral:

* `DASHI.Papers.NavierStokes.Everything` — blocked by
  `DASHI.Papers.NavierStokes.CurrentTheoremInterfaceRound29` and
  `DASHI.Papers.NavierStokes.DependentFlowOwnerAnalysisRound29`, neither shipped.
  The module is kept, indexed and hashed; it is simply not imported by the
  rollup. (Note the reason is a missing dependency, not its lane: 802 Physics
  modules including the Yang–Mills and NS closure lanes *were* adopted and
  *are* in the rollup.)

The additive aggregate is `Agda/DASHI/EverythingCrossPollination20260910.agda`
— 1,821 import lines grouped by lane, with donor commit, archive checksum, the
deferral and the status caveats in its header. It modifies no existing
aggregate.

**Cross-lane kernels actually in use** (`XPOLL_HUBS.csv`, 573 modules imported
from ≥3 lanes; `Everything*` aggregates are excluded as importers, since they
import whole lanes by construction). The top of that list is the honest picture of what the corpus
shares: `DASHI.Core.Prelude` (45 lanes), `DASHI.Core.IntersectionalNonFactorability`
(22), `DASHI.Foundations.SSPTritCarrier` (21), `DASHI.Algebra.Trit` (20),
`DASHI.Core.AttributedSourceCore` (16), `DASHI.Core.ObserverRefinementLatticeExact`
(14), `DASHI.Core.GenericReceipt` (13), `DASHI.Core.TypedDependencyCore` (12),
`DASHI.Core.ProjectionCategory` (12), `DASHI.Core.CandidateOnlyCore` (12),
`DASHI.Interop.SensibLawResidualLattice` (11), `DASHI.Core.FibreRestrictionCore`
(11), `DASHI.Geometry.SSP369Ultrametric` (10), `DASHI.TrackedPrimes` (10). The
trit/369 carrier and the residual/observer/receipt kernels are the two genuine
cross-lane spines; everything else is more local than the names suggest.

## 5. Cross-pollination findings

### 5.1 The ten missing generic kernels have arrived

The previous round's headline frontier item was: the ten
`DASHI.Interop.Aristotle*BidiExact` owners are thin instantiations of ten
generic `DASHI.Core.*BidiExact` kernels **absent from every earlier handoff**.
All ten are in this archive, all were absent locally, all are adopted:

| generic kernel (`Agda/DASHI/Core/…`) | lines | sha256 (first 16) |
|---|---|---|
| `QueryCompatibleFibreConsumerClosureBidiExact` | 111 | `79bf6d48183f085f` |
| `PairIndexedInformationLossLocusBidiExact` | 124 | `8a626fac850cf0e1` |
| `ProvenanceSensitiveConsumerAdequacyBidiExact` | 97 | `409836115b4ec0a3` |
| `PromotionTransportChainBidiExact` | 113 | `12358b52259277c2` |
| `BraidedPromotionTransportBidiExact` | 86 | `e4c4e234450dabae` |
| `CommutingProvenanceBidiCrossPollination2026Exact` | 51 | `d81568949df4744f` |
| `TemporalPromotionNonRetroactivityBidiExact` | 82 | `57df195f3f8fb804` |
| `ResidualSalienceBidiCrossPollination2026Exact` | 62 | `79e63ef96ca25252` |
| `ResidualSalienceSchedulerBidiExact` | 53 | `ed8efaa406bdeded` |
| `AskListenObservationProducerBidiExact` | 107 | `5c6f3dae9832f645` |
| `DeliberativeCyberneticLoopBidiExact` | 90 | `d3bae945770a1aa6` |

(Eleven rows: the worklist owner needs two of them.) Consequence, mechanically
checked at the level of import resolution: **all ten
`DASHI.Interop.Aristotle*BidiExact` owners are now dependency-complete**, where
last round all ten were dependency-incomplete. Their content is genuine Agda —
records, definitions and proof terms, e.g.
`QueryCompatibleFibreConsumerClosureBidiExact` defines `ConsumerClosedAt` and
`PointIdentifiedAt` over a `QueryCompatibleProblem` record and derives
`pointIdentificationClosesConsumer` by `cong` — but *unchecked here*, and the
kernels' own headers say they are Agda reconstructions of the Lean kernel
extraction, with no theorem transported in either direction.

### 5.2 Still-missing generic kernels — the exact remaining frontier

103 module names are imported and absent inside the include root (34 files, 153
edges); the wider walk over all of `Agda/`, staging areas included, gives 108
(`XPOLL_MISSING_TARGETS.csv`). By lane of the *missing* module, over the wider
walk:

| lane of missing module | count | shape of the gap |
|---|---|---|
| Moonshine | 76 | the level-2 / `P11` Brandt–Hecke–Eichler–Deuring arithmetic-geometry family (`P11*`, `DuncanSwisherDwork*`, `Legendre*`, `PositiveSchreier*`, `ClassicalFiniteHeckeCorrespondenceCore`) — a whole sub-library referenced by present `…Everything`/`…Regression` aggregates |
| Cognition | 14 | `DASHI.Cognition.PNF.*` — consumer-restriction intertwiners, occurrence identity, edit transport, sparse frontier topology, contextual-Fractran hyperfabric |
| Physics | 8 | two Balaban Yang–Mills modules, one exotic-gravity proof-search module, plus NS `Papers` interfaces |
| Algebra | 4 | local-valuation sharpness/residue-unit/separated-leading/simple-root modules feeding the Moonshine sharpness chain |
| Foundations | 3 | matched dihedral SO(3) restriction, phase-3 root-character weld, SSP prime-lane depth/phase bridge |
| Data / Arithmetic / Geometry | 3 | `DASHI.Data.RationalExact`, `DASHI.Arithmetic.VpDepthStrictMinimumBridgeExact`, `DASHI.Geometry.LCP.Nat` |

**Eight of the missing names have a same-basename file somewhere in the tree**
(`XPOLL_RELOCATIONS.csv`), and none of the eight is a free fix:

* three are *relocations* — the file exists but declares a different module, so
  the import name and the declaration disagree:
  `DASHI.Physics.ExoticGravity.NegativeGGravitationalWavePhaseProofSearchExact`
  ↔ `DASHI/Physics/GR/…`, `DASHI.Foundations.SSPPrimeLane369DepthPhaseBridge`
  ↔ `DASHI/Physics/Closure/…`, and
  `DASHI.Cognition.PNF.ContextualFractranPNFHyperfabric369Exact` ↔
  `DASHI/Interop/…`. The last of these revises an earlier round's finding: the
  contextual-Fractran module was classified as genuinely absent, and a
  same-named module does in fact exist, under `Interop`. Resolving any of the
  three means a rename or a re-export shim, which cannot be validated without a
  toolchain, so all three are deferred with the evidence recorded.
* five are *outside the Agda include root* (`Agda/src/`,
  `Agda/temp-DOWNLOADED/`), where their declared module name already matches the
  imported name — but their importers are outside the root too, so no in-root
  edge depends on them. They were provisionally promoted into
  `Agda/DASHI/**` during this round and then **reverted**: nothing in the
  include root needs them, and promoting unvetted staging material into the
  canonical tree is not an improvement. They stay indexed where they are.

This is the honest cross-lane frontier: the corpus's *analytic-number-theory
side* (Moonshine ↔ Algebra valuation ↔ Arithmetic depth) and its *PNF cognition
side* are the two places where a named generic kernel is still absent from
every delivery to date. Nothing here can be repaired by writing a stub, and no
stub was written.

### 5.3 Shared vocabulary and duplicate-kernel candidates

`XPOLL_SHARED.csv` lists 290 top-level declaration names that occur in three or
more lanes. Most of the head of the list is ordinary generic vocabulary (`sym`,
`pow`, `cong`, `iterate`, `listCount`, `append`, `half`) and is *not* evidence
of a shared kernel. The names that do look like unowned generics — each
re-declared lane-locally rather than imported from one place — are, with their
lanes:

* `canonicalCrossPollinationBoundary` — 9 lanes (Analysis, Biology, Codec,
  Cognition, Core, Culture, Interop, Law, Physics);
* `sourceCountRegression` — 6; `producerForResidual` — 4 (Biology, Cognition,
  Law, Wikimedia); `legalAuthorityRouteRejected` — 4; `existingNDimBoundary` — 4;
  `canonicalAuthorityBoundary` — 4;
* the `candidateOnlyCoreAdapter*` / `authorityNonPromotionCoreAdapter*` triples
  — Culture, Interop, Promotion;
* `canonicalRegistryBoundary`, `canonicalPromotionBoundary`,
  `canonicalSourceAttributionBoundary`, `canonicalGeometryPromotionBoundary`,
  `proofSearchBoundary`, `counterfactualBoundary` — 3 lanes each;
* `forgetAfterClassify` / `classifyAfterForget` — Arithmetic, Foundations,
  Moonshine (a retraction pair stated three times);
* `conjugationInvolutive` — Biology, Mathematics, Moonshine;
  `complement-involutive` — Biology, Codec, DNA.

These are *bridge opportunities*, not bridges: name coincidence is not a shared
definition, and each pair would have to be compared type-by-type before any
common owner is written. They are recorded here so the comparison can be made,
and deliberately not acted on in this round.

## 6. The NS worker supplement, now genuinely delivered

`Provenance/ns_worker_result/` (4 files, hashes in `XPOLL_LEDGER.csv`):

* `docs/ns-clay-contract/ns-agda-tranche-intake-20260909.md` (205 lines) — the
  R395–R530 reconciliation: 3,226 donor sources, 159 new modules, 36 donor
  reconciliations, two RingSolver-repair versions **kept local** because the
  donor would regress them, seven modules referenced by nobody's tree, and its
  own explicit "no Agda kernel was run on any of this". Its Agda-side flags are
  bookkeeping: `round489…Closed = false`, `round492R423SignedCompanionBudgetClosed
  = false`, `round501DirectCompanionBudgetClosed = false`,
  `round471PhysicalOuterCellGramBoundClosed = false`, and the one flag that
  flips (`round307…TransversalityWeldClosed`) is simultaneously conditioned by
  `round307AllOuterCellsMeetCompilerHypotheses = false`.
* `docs/ns-clay-contract/rate-block-gram-bound.md`, `source-tranche-audit.md`.
* `RequestProject/NavierStokes/RateBlockGramBound.lean` (738 lines).

**The Lean file is not buildable in this checkout**, and this is a delivery
fact, not a policy: it opens with `import RequestProject.NavierStokes.TransverseFrameSplit`
and `open ClayNS.Waleffe ClayNS.Resolvent ClayNS.TTStar ClayNS.Schur`, and none
of those modules exists in this tree or in any handoff received here. It is
preserved verbatim, unmodified, outside the Lean library roots so that it
neither builds nor breaks the build.

What the file claims, as read (not as verified here): a positive
`gramOperatorBound_of_rateBlockMultiplicity` with `A = 32·m` under a dyadic
rate-block multiplicity bound; a matching negative
`gramOperatorBound_fails_on_comparable_shells`; and an equivalence at a
degenerate rate cluster between the bound and cancellation of the aggregated
cells. Its own conclusion, which this report adopts unchanged: the physical,
truncation-uniform outer-cell Gram bound is **open**, and Package A and the
literal periodic Clay regularity target are **not closed**.

## 7. The one machine-checked result of this round

Rather than leave the NS Lean source as an unbuildable artefact, its
**lane-independent core** was extracted, generalized and proved here:
`Lean/Spine/RateBlockSchur.lean`, wired into the `Spine` aggregate and the
spine axiom audit. It mentions nothing from the Navier–Stokes lane — no wave
lattice, no viscosity, no cell family — and quantifies over an arbitrary index
type.

* `Spine.RateBlockSchur.schur_form_le_blockMultiplicity` — if `lam : ι → ℝ` has
  each index of a finite `S` in a dyadic window `[4^b, 4^{b+1})` and each window
  carries at most `m` indices, then for **every** pairing `a` dominated by a
  product of nonnegative masses, `a p q ≤ n p * n q`,
  `∑_{p,q∈S} a p q / (lam p + lam q) ≤ 16·m·∑_{p∈S} (n p)²/lam p`.
  Cancellation-free: a Schur test against the Cauchy kernel, with geometric
  across-block decay (`pair_term_le`, `amgm_block`) and a row sum bounded by
  `4m` uniformly in `S` (`rowsum_le`, `sum_half_pow_natAbs_le`).
* `Spine.RateBlockSchur.schur_gram_le_blockMultiplicity` — the inner-product
  instance: for a family `G : ι → E` in any complex inner-product space, the
  real part of the Gram pairing obeys the same bound with `n p = ‖G p‖`. This is
  the exact shape the NS lane consumes; the lane supplies only `lam` and `G`.
* `Spine.RateBlockSchur.schur_form_ge_half_mul_multiplicity` — the matching
  lower bound: a single dyadic block of `m` indices with unit rates and a
  constant pairing forces the constant to be at least `m/2`. So the kernel's
  constant is `Θ(m)` and **no cancellation-free argument can remove the growth
  in the block multiplicity** — which is precisely why the NS obligation stays
  open.

Receipts: `lake build` over all default targets completes — **8,541 jobs, no
errors**; the file contains no `sorry`, no `axiom`, no `native_decide`; and
`Lean/Spine/AxiomAudit.lean` prints, for each of the seven exported results,
dependence only on `propext`, `Classical.choice`, `Quot.sound`.

One pre-existing build defect was repaired: the `AgdaMirror` library glob was
`AgdaMirror.*`, which pulled in the root aggregate `Lean/AgdaMirror.lean` and
hence `AgdaMirror.Physics.YangMills` — a Lean mirror module that has never been
shipped to this checkout, in this or any earlier archive. The glob is now
`AgdaMirror.+` (submodules only), as its own comment always described, and the
comment now states the real reason: a missing file, deferred, not a topic
exclusion.

## 8. Conflicts kept, with reasons

28 same-path divergences were **not** reconciled because the donor version drops
declarations or imports the local version has; the local file is kept and the
donor file preserved under `Provenance/donor-1d3cb03c1dec/<path>`. Full detail
in `XPOLL_DIVERGENCES.csv`. The shape of the 28:

* **5 aggregates/rollups** whose donor version imports strictly fewer modules —
  `DASHI/Analysis/Everything` (3 `RiemannG2*` imports dropped),
  `DASHI/Culture/Everything`, `DASHI/Culture/MissingDeceasedOpenScienceEverything`,
  `DASHI/EverythingAristotleWikidataReciprocalGarden` (drops the five
  `DASHI.Core.Aristotle*BidiExact` owners returned by an earlier round) and
  `DASHI/Environment/LESFluidPhysicsCouplingExact` (drops the
  `Papers.NavierStokes` theorem interface). Taking the donor would silently
  unwire working modules.
* **9 Analysis/Riemann modules** where the donor drops named local results
  (`sourceAnchorWeldStillLive`, `gibbsUniquenessExactCutset`,
  `evaluationLeafNotYetSchedulable`, `finiteNearEvaluationSchedulable`, …).
* **10 Yang–Mills / NS-closure modules** (7 Balaban YM, 3 `Physics/Closure`
  NS rounds) where the donor drops a local declaration or a local YM import —
  e.g. `BalabanPath13FourAxisPhysicalPoincareExact` drops
  `sumZeroMeanFibrePoincare` and its `…ZeroMeanFibrePoincareExact` import, and
  three of the seven drop only an import. This is the same discipline the NS
  worker applied to its two RingSolver repairs, applied here symmetrically.
* **4 others**: `Core/AristotleWikidataReciprocalGardenValidation` (drops six
  regression names), `Core/ConsumerRelativeReductionKernelExact` (drops `run`),
  `Foundations/UBP/RationalCertificateTransport` (drops the eight canonical
  π/Y bound definitions) and
  `Governance/SexedHistoricalCoConstitutionHyperfabricExact` (drops
  `feminine`/`masculine`).

Reconciling any of these is a *semantic* decision — it needs the donor's intent
for the dropped names — and is deferred with the names listed, not resolved by
guesswork.

## 9. Claim boundaries

* No Agda file in this repository has been typechecked, in this round or any
  previous one. Import resolution, declaration counts and hashes are text-level
  facts. The rollup aggregate is a source index.
* Boolean `… ≡ true` ledgers, route/compiler interfaces and
  records-whose-fields-are-the-estimates are **conditional bookkeeping**. 2,208
  such ledger obligations came in with the adopted material; none is a proof.
* No physical, Clay, Yang–Mills, Navier–Stokes, Riemann, Monster/Moonshine or
  theory-of-everything closure is claimed. The NS frontier is unchanged and
  explicitly open (§6), and §7's lower bound is a reason it stays open, not a
  step towards closing it.
* The only proved results this round are the seven Lean statements of §7, over
  Lean definitions given in the same file, with the axiom audit shown.
