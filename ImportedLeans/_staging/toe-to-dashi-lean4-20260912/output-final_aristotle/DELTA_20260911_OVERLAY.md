# 2026-09-11 current-master Agda delta — verification, overlay, index, frontier

Scope of this round: verify the attached overlay, apply it, index both files,
and assess its fibre-routing / consumer-relative projection material as a
candidate reusable Spine adapter.  **No build was requested and no Agda or Lean
library build was run.**  Everything below is either a checksum, a mechanical
index fact, a source fact, or an explicitly-labelled proposal.

---

## 1. Delivery verification (done before anything was written)

| item | value |
|---|---|
| archive | `toe-agda-master-delta-20260911.tar.gz` |
| archive sha256 | `28087139cd7b6a8cd99683bd05bca2811f94d374f365fccfff94d55ca0592f98` |
| entries | 5 (`HANDOFF.md`, `SOURCE_MANIFEST.txt`, `SHA256SUMS`, 2 payload paths) |
| `sha256sum -c SHA256SUMS` | **4/4 OK**, 0 failed, 0 missing |
| manifest vs payload | exact match, both payload paths listed and present |
| base Agda commit | `a866c675f60ad2ee5cd5a96f213cdd3e7e50cf26` |
| target Agda commit | `4c8ebfb733f5768ce7ed61388cc5272ececd5d0d` |
| build products shipped | none (source-only, as declared) |

Payload checksums, re-verified against the files now in the tree:

| path | sha256 |
|---|---|
| `dashi_agda/DASHI/Reasoning/FibreRoutingGrokkingMoEBrainCrossPollinationExact.agda` | `0f80173ee5fa3510993a51a440982fa34c7b53112cea577dbeace4c002d1e215` |
| `dashi_agda/DASHI/Reasoning/Everything.agda` | `828182dbdcc0ee31380205c85d6aea5210c0293faffb56bb479612c36c8231a8` |

The donor sources, `HANDOFF.md`, `SOURCE_MANIFEST.txt` and `SHA256SUMS` are
preserved verbatim under `Provenance/delta-20260911/`.

## 2. Disposition

| donor path | disposition | prior local sha256 | note |
|---|---|---|---|
| `DASHI/Reasoning/FibreRoutingGrokkingMoEBrainCrossPollinationExact.agda` | **new-module-adopted** | — (no prior copy) | first appearance in this corpus |
| `DASHI/Reasoning/Everything.agda` | **adopted-donor** | `c62f687c35fd33d5e0aaed4a9ff809f796af6153fd9bb125d8a454c98e8962d6` | donor is strictly additive: one new `import` line, all 113 prior imports retained in order |

The Everything diff is exactly one added line, so adopting the donor loses no
local content; the prior local text also remains in git history.  Machine-readable
form: `DELTA_20260911_LEDGER.csv`, plus rows upserted into `SPINE_INDEX.csv`,
`SPINE_INTAKE_LEDGER.csv`, `SPINE_IMPORT_EDGES.csv`, `XPOLL_INDEX.csv`,
`XPOLL_LEDGER.csv`, `XPOLL_IMPORT_EDGES.csv` by
`scripts/delta_overlay_20260911.py` (idempotent; re-running rewrites the same
rows rather than duplicating them).

## 3. Index of the new module

`DASHI.Reasoning.FibreRoutingGrokkingMoEBrainCrossPollinationExact`
— 296 lines, 18 top-level declarations, 6 `data`, 4 `record`, **0 `postulate`**,
0 holes, 0 `TERMINATING`, 0 `primTrustMe`, 10 Boolean-ledger equations
(`≡ true` / `≡ false`), 1 `→ ⊥` boundary, `dependency_complete = yes`.

### 3.1 Import edges (11 imports, 7 internal, all resolving in-tree)

```
DASHI.Reasoning.FibreRoutingGrokkingMoEBrainCrossPollinationExact
  -> DASHI.Core.Prelude                                             (both)
  -> Agda.Builtin.Bool / Equality / String, Data.Empty              (external)
  -> DASHI.Biology.SparseExpertRoutingCoalition                     (both)   MoE lane
  -> DASHI.Biology.SpectralGrokkingLatticeExact                     (both)   grokking lane
  -> DASHI.Reasoning.DASHIgGrokkingEmpiricalBridgeExact             (both)   empirical provenance
  -> DASHI.Reasoning.StructuralMetaphorTaskCompressionExact         (both)   compression kernel
  -> DASHI.Reasoning.RelationRepresentationRealizationExact         (both)   realization firewall
  -> DASHI.Physics.Closure.LilaE8RootEnumerationNoDuplicatesSurface (both)   E8 carrier status
```

Every referenced upstream name was checked to exist, with matching arity, in the
local copy of the corresponding module: `sensoryRouteCount`, `allExpertCount`,
`sensoryRouteIsSparse`, `reflectiveRouteCount`, `reflectiveRouteIsSparse`,
`literalBrainMoEArchitecturePromoted(IsFalse)`,
`canonicalSparseExpertCoalitionBoundary`; `irregularComponentCount`,
`symmetryAdaptedComponentCount`, `cleanupPhase`,
`cleanupRemovesIrregularComponents`, `cleanupRetainsThreeSymmetryModes`;
`InternalEmpiricalSource.repository/commit`, `canonicalDASHIgPhase2Source`;
`CompressionFailureWitness` / `compressionFailureWitness`;
`RepresentationRealizationWitness`, `representationRealizationWitness`,
`representationCollisionBlocksRealization`;
`LilaE8NoDuplicatesSurfaceStatus` and its single constructor
`executableIndexedNoDuplicatesAvailableCompletenessBlocked`.

### 3.2 Incoming edges / reachability

`DASHI.Reasoning.Everything -> …FibreRoutingGrokkingMoEBrainCrossPollinationExact`
is the only incoming edge in the whole Agda tree.  `DASHI.Reasoning.Everything`
is imported by `DASHI.EverythingHierarchy`, so the new module is transitively
reachable from that aggregate.  It is **not** in
`DASHI.EverythingCrossPollination20260910`, which is a dated 2026-09-10 snapshot;
that file was left untouched rather than back-dated.

### 3.3 Declaration inventory, by kind

**Interfaces / records (no inhabitant supplied in this module unless noted).**

* `FibreRoutingCarrier Input Fibre Weight` — `routeWeight`, a `Bool` flag
  `overlappingMembershipPermitted`, a `String` reading.  Inhabited here by
  `flySoftRoutingCarrier`.
* `FibreCompositionCarrier Input Fibre Weight Contribution Representation` —
  routing, `localContribution`, `compose`, `encode`, and the commuting-square
  field `compositionCommutes`.  **No inhabitant anywhere in the corpus** (see
  §6, seam 1).
* `FlyRuntimeProducer` — repository / commit / owner / compiler / bounded
  reading.  Inhabited by `canonicalFlySoftCarrierProducer`
  (`github.com/chboishabba/dashiBRAIN`, commit
  `e44b3fe57aa6457d6ef543219f01e70395d6dce8`).  Provenance data, not a theorem.
* `FibreRoutingCrossPollinationBoundary` — 9 `Bool` fields each paired with a
  `≡ true` / `≡ false` obligation, inhabited by
  `canonicalFibreRoutingCrossPollinationBoundary` with `refl` in every slot.
  These are **ledger placeholders**: `refl` proves the flag equals the literal
  it was set to, and nothing more.  They record the owner's interpretation
  firewall (MoE is not literally brain architecture; grokking is not
  definitionally MoE; LILA/E8 does not explain the Fly result; held-out
  adequacy does not imply mechanism), but they do not derive it.

**Finite data.** `PaintedDomain` (2), `SoftMembership` (3),
`SelectedROISpecimen` (2), `HardPaintedIdentity` (1), `PaintedOverlapProfile`
(2), and the indexed family `ActiveMembership : SoftMembership → Set` with
constructors only for `halfMembership` / `fullMembership`.

**Definitions.** `paintedMembership`, `hardPaintedIdentity`,
`paintedOverlapProfile`, `flySoftRoutingCarrier`,
`canonicalFlySoftCarrierProducer`, `canonicalFibreRoutingCrossPollinationBoundary`,
`dashigPinnedProducerRepository`, `dashigPinnedProducerCommit`,
`lilaE8FiniteCarrierStatus`.

**Proof terms (source-level; see the verification caveat below).**

| name | content | character |
|---|---|---|
| `overlappingROIActivatesParentAndChild` | `ActiveMembership … × ActiveMembership …` | constructor pair; finite specimen |
| `hardWinnerLosesOverlapProfile` | `Compression.CompressionFailureWitness hardPaintedIdentity paintedOverlapProfile` | genuine collision witness (`refl` + absurd pattern) |
| `hardWinnerCannotRealizeOverlapProfile` | `RepresentationRealizationWitness … → ⊥` | **the one real negative result**: unique-maximum collapse admits no decoder for the overlap consumer; discharged by the upstream `representationCollisionBlocksRealization` |
| `softOverlapProfileRealizesItself` | realization witness with `realize = id` | true but near-trivial: the identity always realizes itself |
| `sensoryRouteRemainsSparse`, `reflectiveRouteRemainsSparse` | `≤` facts | re-exports of existing MoE lemmas, unchanged |
| `brainMoERemainsAnalogyOnly` | `… ≡ false` | re-export of an existing Bool-ledger pin |
| `cleanupRemovesIrregularComponents`, `cleanupRetainsSymmetryModes` | `≡ 0`, `≡ 3` | re-exports of existing `refl`-computed facts |

**Verification caveat.** No Agda binary is available in this environment, so
none of the above was typechecked here.  What was checked is: every import
resolves to a file in the tree; every referenced upstream name exists with the
arity used; the constructor applications match the upstream record/`data`
signatures; and `DASHI.Core.Prelude` supplies `_×_`, `_,_`, `≤`, `_≡_`, `refl`,
`⊥` so that the module's re-opening of `Agda.Builtin.Bool/Equality/String` and
`Data.Empty` names the same entities rather than ambiguous ones.  That is a
resolution argument, not a kernel receipt.

### 3.4 Inventory refresh

`scripts/corpus_inventory.py` was re-run, so `corpus_index.json`,
`corpus_lanes.csv` and `CORPUS_INVENTORY.md` now cover the tree as it actually
stands: 26,540 source files (17,522 Agda, 9,018 Lean) against the 22,634 of the
committed inventory, which predated the 3,889-path vendored `Lean/ImportedLeans`
provenance corpus and the `AgdaMirror` additions of the 2026-09-10 intake.  The
rise in the reported `sorry` count for the *unbuilt* Lean archive (6,271 →
36,586) is entirely that vendored corpus becoming visible to the counter; it is
not a regression, and none of it is in a build target.  `DASHI/Reasoning` moves
from 216 to 217 files.  `Lean/Proposed` appears as a new one-file lane with
`build_target = false`.

## 4. Proposed shared adapter

The reusable content of the overlay is one shape:

> a routing layer assigns each fibre a context-relative weight; each fibre makes
> a local contribution; a composition operator turns (weights, contributions)
> into a representation; a consumer evaluates the representation.

The corpus already owns the consumer half of that shape in Lean:

* `Integration.ContextIndexedRole` — `FactorsThrough`,
  `NonFactorabilityWitness`, `Determines`,
  `witness_rules_out_every_factorisation`;
* `Integration.RealisationAdequacy` — `Pipeline`, `ConsumerSpec`,
  `RepresentationAdequate` / `RealisationAdequate` / `AdequateFor` /
  `AdequateGlobally`, all phrased as `Determines`;
* `AgdaMirror.NonFactorabilityKernels` — the Lean mirror of
  `DASHI.Core.IntersectionalNonFactorability`.

**Proposed adapter.**  A `FibreCompositionCarrier` is exactly a `Pipeline` whose
`represent` is the *fibre profile* `i ↦ (routeWeight i, localContribution i)`
and whose `realise` is `fun p => compose p.1 p.2`; its `compositionCommutes`
field is precisely the datum that makes `encode` factor through that profile.
Consumers are then `ConsumerSpec`s, and hard-winner collapse is a
`NonFactorabilityWitness` against a named consumer.

A **checked prototype** of the adapter is committed at
`Lean/Proposed/FibreRoutingProjectionAdapter.lean`.  It elaborates standalone
with the project toolchain (`lean` on the file, zero errors, zero warnings;
`#print axioms` reports no axioms beyond `propext`, which enters through
`deriving DecidableEq`).  It is Mathlib-free and therefore restates
`FactorsThrough` / `Determines` / `ProjectionCollision` locally instead of
importing them; that duplication is deliberate and documented in the file, with
the mechanical migration to `Integration.RealisationAdequacy` spelled out.

It contains:

* `FibreCompositionCarrier.encodeFactorsThroughProfile` and
  `profile_determines_encode` — the adapter theorem, for an arbitrary carrier;
* `QueryIndexedAdequacy` with `FactorsThrough.ofQuery` and
  `query_collision_blocks_adequacy` — one collision at one query refutes
  adequacy for the whole query family;
* the Fly specimen: `hardWinner_not_factorising`, `hardWinner_not_determines`
  (the Agda module's negative result, re-proved in Lean),
  `softMembership_determines` (the soft carrier retains what the hard winner
  erases), and `flySoftCompositionCarrier` — **an actual inhabitant** of the
  Lean mirror of `FibreCompositionCarrier`, its commuting square discharged by
  case analysis.

**Status of the proposal.**  `Lean/Proposed` is outside every `lakefile.toml`
glob, so this file is not a build target and nothing depends on it.  It is a
proposal, not a reuse claim: the corpus rule that reuse requires a *named
current consumer*, a carrier/factor-through argument and explicit hypotheses is
satisfied only for the middle item.  There is no current consumer.  Promotion
would require (i) naming one, (ii) replacing the three local generic shapes with
`import Integration.RealisationAdequacy`, and (iii) a round in which a Lean
build is allowed, since the `Integration` library imports Mathlib and no Lean
artefacts are built in this checkout.

## 5. Corpus posture

Nothing was narrowed.  All previously indexed lanes remain in the tree and in
the indices: NS/YM/RH/GRQ, Monster/Moonshine/Base369/J-invariant,
Wikidata/DOI/QID/Dewey, Fly/MoE/brain, law, ecology, culture/cuisine.  This
round added rows; it removed none.  No YM or NS material was touched.

## 6. Honest frontier — exact remaining obligations

1. **`FibreCompositionCarrier` is an uninhabited interface in Agda.**  The
   module defines the record with its `compositionCommutes` obligation and then
   never instantiates it: `flySoftRoutingCarrier` inhabits only the weaker
   `FibreRoutingCarrier`.  So the Agda text does not yet exhibit any composition
   commuting square.  *Obligation:* an Agda term of type
   `FibreCompositionCarrier SelectedROISpecimen PaintedDomain SoftMembership C R`
   for some concrete `C`, `R`.  The Lean prototype shows the obligation is
   dischargeable on the finite specimen (`flySoftCompositionCarrier`), but a Lean
   term is not an Agda term.
2. **No consumer.**  Nothing in Agda or Lean imports the new module except the
   `Reasoning.Everything` rollup.  Status preserved as delivered, per the
   handoff instruction; no reuse is claimed.
3. **The boundary record is Boolean ledger, not proof.**  All nine fields of
   `FibreRoutingCrossPollinationBoundary` are `Bool` + `refl`.  Upgrading any of
   them to a theorem requires a statement about the underlying carriers, which
   this module does not have.
4. **`softOverlapProfileRealizesItself` is the identity realization.**  It
   establishes that the overlap profile realizes itself, which is trivially
   true for any function; it is not evidence that the soft carrier realizes a
   biological target.  The non-trivial content of the pair is the negative
   result `hardWinnerCannotRealizeOverlapProfile`.
5. **LILA/E8 status is unchanged and still blocked.**
   `lilaE8FiniteCarrierStatus` re-exports
   `executableIndexedNoDuplicatesAvailableCompletenessBlocked`; the upstream
   completeness obligations (`missingIntegerTwoSparseCompleteness`,
   `missingHalfEvenParityCompleteness`, `missingCombinedE8Completeness`,
   `missingUpstreamE8RootEnumerationCompletePromotion`,
   `missingExecutableMembershipToNativeMembership`) remain open.
6. **No kernel receipt for the Agda half.**  No Agda typechecker exists in this
   environment, so the two overlay files are indexed and resolution-checked but
   not machine-verified here.  Same for every Lean library: the checkout has no
   built artefacts, so `Lean/Proposed/FibreRoutingProjectionAdapter.lean` was
   verified only as a standalone Mathlib-free file.
7. **Empirical provenance is pinned, not verified.**  The dashiBRAIN commit
   `e44b3fe5…` and the DASHIg commit `013962fb…` are `String` fields.  Nothing
   in the corpus checks that those commits exist or that the pipelines named in
   `functionalOwner` / `compiler` produce the described carrier.
