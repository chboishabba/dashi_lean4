# Combined Lean + Agda consolidation tranche — intake, index and frontier
### 2026-09-10 · source-only · no local build run

---

## 1. Delivery verification (first, as requested)

| item | value |
|---|---|
| archive | `toe-lean-agda-spine-handoff-20260910.tar.gz` (35 346 946 bytes, project root) |
| archive sha256 | `b532063341a20942738d7637da984e7a2ed98ef7033fd6b782ddd9fd3138d35b` |
| declared Lean source commit | `c5b9a0722f149144b94bdaca9052417446de0aa7` (`chboishabba/dashi_lean4`) |
| declared Agda source commit | `a866c675f60ad2ee5cd5a96f213cdd3e7e50cf26` (`chboishabba/dashi_agda`) |
| `SOURCE_MANIFEST.txt` entries | **20 074** |
| payload files actually extracted | **20 074** — `diff` of the sorted manifest against the sorted file list is **empty** (no extra, no missing, no path mismatch) |
| `SHA256SUMS` entries | **20 076** (the 20 074 payload paths plus `HANDOFF.md` and `SOURCE_MANIFEST.txt`) |
| `sha256sum -c SHA256SUMS` | exit 0 — **20 076 `OK`**, 0 failed, 0 missing |

The archive was unpacked **beside** the project (`/workspace/unpack_20260910_spine`,
outside the returned tree) and every file was compared against the tree before
anything was written.

Payload composition by extension:

| ext | count | ext | count |
|---|---|---|---|
| `.agda` | 15 952 | `.toml` | 3 |
| `.lean` | 4 087 | `.json` | 3 |
| `.md` | 14 | `.pdf` | 1 |
| `.py` | 5 | `.keep-post644` | 1 |
| `.txt` | 4 | `.agdai` | **1** |
| `lean-toolchain` | 3 | | |

**One delivery anomaly, recorded not smoothed:** `HANDOFF.md` states the tranche
"deliberately excludes … `.olean`, `.agdai`, build outputs", yet
`dashi_agda/DASHI/Geometry/LCP/Nat∞.agdai` (21 187 bytes) is present and is
checksummed. It is *not* injected into the Agda source tree; it is staged at
`Provenance/spine-20260910/donor-artifact/agda/DASHI/Geometry/LCP/Nat∞.agdai`
and recorded in the ledger.

---

## 2. What the tranche actually is

Compared file-by-file against the tree **before** intake:

| | identical | divergent | absent locally |
|---|---|---|---|
| Agda payload (15 965 files) | 15 930 | 28 | 7 |
| Lean payload (4 109 files) | 187 | 15 | 3 907 |

Two facts follow immediately, and they shape everything below.

1. **The Agda half adds no new module.** Every one of the 15 952 delivered
   `.agda` files already exists here; the 7 absent paths are five prose notes,
   a `.keep` marker and the stray `.agdai`. Relative to the 2026-09-10
   full-source state (donor `1d3cb03c…`, 15 980 `DASHI/**.agda` in the tree),
   commit `a866c675…` is *behind*: in **all 28** divergences the donor version
   drops declarations or `DASHI.*` imports that the local file has.
2. **The Lean half is where the new material is**, and 3 889 of the 3 907 new
   paths are a single new subtree, `ImportedLeans/`, a vendored multi-repository
   dump. The genuinely new first-party Lean material is 18 paths.

---

## 3. Per-path disposition

Policy applied uniformly, machine-executed by `scripts/spine_intake_apply.py`,
one ledger row per delivered path in **`SPINE_INTAKE_LEDGER.csv`**:

| disposition | Agda | Lean | meaning |
|---|---|---|---|
| `identical-no-action` | 15 930 | 187 | byte-identical, recorded |
| `adopted-new` | 6 | 3 907 | written at the natural local path |
| `retained-local-donor-preserved` | 28 | 15 | local kept; **donor version preserved verbatim** under `Provenance/spine-20260910/donor-version/`, both sha256 in the ledger |
| `staged-donor-artifact` | 1 | 0 | the `.agdai` above |
| **total** | **15 965** | **4 109** | **20 074** |

Nothing was overwritten. Nothing was refused on topic grounds: YM, NS, RH,
Monster/Moonshine/Base369/J-invariant, DOI/QID/Dewey/Wikidata, law, ecology,
optics and the rest are all indexed and all retained.

### 3.1 The 18 first-party Lean adoptions

| path | what it is | build exposure |
|---|---|---|
| `Lean/Spine/JMD.lean`, `Lean/Spine/JMD/MonsterMoonshine.lean`, `…/FactorVecSheaf.lean`, `…/ArchitectureDynamics.lean`, `Lean/Spine/README.md` | the promoted JMD Monster/CRT, FactorVec valuation-sheaf and encode–select–prune–diagonal lane | inside the `Spine` library glob (`Spine.*`) — **not build-verified this round** |
| `Lean/AgdaMirror/Physics/YangMills.lean` + 5 modules under `…/YangMills/` | the Yang–Mills mirror surface (see §7.3) | inside the `AgdaMirror` glob — **not build-verified this round** |
| `Lean/YangMillsClosure.lean`, `Lean/YangMillsContinuumGap.lean`, `Lean/NavierStokesClosure.lean` | root closure files | outside every library glob → no build exposure |
| `Lean/DASHI/output-final_aristotle/RequestProject/{YangMillsClosure,NavierStokesClosure}.lean` | same two files inside the Wikidata archive package | the `AristotleArchive` library lists its modules explicitly; these are not among them → no build exposure |
| `Lean/DASHI/Klüver’s Form Constants_aristotle/{YangMillsClosure,NavierStokesClosure}.lean` | same two files inside the Klüver package | that library declares no globs (root module only) → no build exposure |

`Lean/ImportedLeans/**` (3 889 paths) is matched by no `lean_lib` glob in
`lakefile.toml`, so adopting it adds no build target.

### 3.1b One mechanical edit to adopted vendored files: `axiom` declarations commented out

153 of the 3 889 adopted `Lean/ImportedLeans/**` files declare Lean `axiom`s —
419 of them in total (`MonsterGroup`, `bott_periodicity_theorem`,
`thompson_hauptmodul`, `univalence`, `circuit_sound`, `hille_yosida_core`,
`gronwall_variance_decay`, …). This project does not introduce `axiom`
declarations, and dropping the files would violate the preservation
instruction, so each declaration is **commented out line-by-line** with a
marker naming the intake, leaving the text verbatim inside the comment. The
files are in no build target, so nothing downstream changes.

The edit is mechanical, auditable and reversible:
`scripts/spine_axiom_neutralise.py` wrote
**`SPINE_AXIOM_NEUTRALISATION.csv`** with, for every affected path, the axiom
names, the exact line ranges commented, and the sha256 before and after; the
unmodified donor bytes are the ones recorded in `SPINE_INDEX.csv` and
`SPINE_INTAKE_LEDGER.csv` and are reproducible from the archive. No
`@[implemented_by]` attribute occurs anywhere in the tranche. Nothing outside
`Lean/ImportedLeans/` was touched: the 18 first-party Lean adoptions declare no
axiom, and no pre-existing file was modified.

### 3.2 The six Agda adoptions

`DASHI/Physics/YangMills/BalabanTheorem2ProofDossier.md`,
`DASHI/Physics/YangMills/BalabanPropagatorSourceLedger.md`,
`DASHI/Governance/SafeJustConsumerAdequacyResidualNote.md`,
`DASHI/Governance/SafeJustAuthorityChainReceipt.md`,
`DASHI/Governance/IndigenousEnvironmentalAuthorityRound2Notes.md`,
`DASHI/Physics/YangMills/.keep-post644`. Prose and a marker: no Agda module,
no aggregate change.

---

## 4. Retained divergences, with provenance

All 43 are listed in **`SPINE_DIVERGENCES.csv`** with the exact declarations and
imports at stake, and the donor bytes are on disk under
`Provenance/spine-20260910/donor-version/`.

**Agda (28).** Every one fails the reconciliation test in the same direction —
the donor would remove local content. Examples:

* `Analysis/NonArchimedeanSpectralOriginalGoalCapstoneExact.agda` — donor drops
  9 named results (`totalVariationRouteClosedPositive`,
  `sizeExponentHalfReadingRejected`, …);
* `Core/AristotleWikidataReciprocalGardenValidation.agda` — donor drops the ten
  reciprocal-garden regression names *and* the five
  `DASHI.Core.Aristotle*BidiExact` imports that the previous round established;
* `Physics/YangMills/BalabanCMP109DirectBetaSourceRegression.agda`,
  `Physics/Closure/NSTriadKN…Round{282,413,424}Exact.agda` — donor drops
  round-level declarations;
* `Culture/Everything.agda`, `Analysis/Everything.agda`,
  `EverythingAristotleWikidataReciprocalGarden.agda` — donor aggregates list
  fewer modules.

**Lean (15).** Same direction:

* `Cuisine.lean` (donor drops 16 imports), `Cuisine/AxiomAudit.lean` (3),
  `Synthesis.lean` and `Synthesis/AxiomAudit.lean` (both drop
  `Synthesis.ContractRepair`), `Spine.lean` (donor is a 15-line root that omits
  15 of the 19 spine modules), `AgdaMirror/LoomRelationAlgebra.lean` (donor
  drops 7 theorems);
* `MoonshineFractran.lean` and `AgdaMirror/MoonshineEarn.lean` — donor is
  *token-for-token* the local file with every `by decide` replaced by
  `by native_decide`. Declaration-preserving, but strictly weaker: it moves
  the file from kernel-checked to `Lean.ofReduceBool`. Retained local.
* `AgdaMirror/{Core,Analysis,Algebra}.lean` — cosmetic (docstring moved above
  the imports); local retained for stability, donor preserved.
* `lakefile.toml`, `DASHI/output-final_aristotle/{lakefile.toml,README.md,ARISTOTLE_SUMMARY.md}`
  — non-source; the local versions are the live build configuration and the
  accumulated round history (111 KB vs the donor's 2.9 KB summary).

So: **no local declaration was lost this round, and every donor byte is
recoverable from `Provenance/spine-20260910/`.**

---

## 5. Dependency frontier (post-intake)

Recomputed over the tree by `scripts/spine_frontier_post.py`
(**`SPINE_FRONTIER_POST.csv` / `.json`**).

### 5.1 Agda — unchanged, as it must be

17 521 files, 141 057 import lines, 70 327 internal `DASHI.*` edges.
**108 imported-but-absent module names in 158 edges across 37 files**; 103 of
the 108 are absent from the tree under any path. This is bit-for-bit the
frontier of the previous round: the tranche shipped no new Agda module, so it
could not move. Composition of the 108: **76 Moonshine** (the level-2 `P11`
Brandt–Hecke family), **14 `Cognition.PNF`**, 8 Physics, 4 Algebra,
3 Foundations, 1 each Arithmetic / Data / Geometry.

### 5.2 Lean — two very different numbers, both reported

9 017 files, 26 574 import lines, 18 775 internal edges.

* Under **strict single-root resolution** (every module resolved against
  `Lean/` alone): 1 213 unresolved targets in 7 273 edges. This number is
  dominated by the vendored corpora, which are separate packages with their
  own source roots.
* Under **any-source-root resolution** (the module is present somewhere in the
  tree, possibly under another package root): only **31 targets in 177 edges**
  are absent from the tree at all. Four of those 31 (`bases`, `is`, `this`,
  `to`) are artefacts of the line-regex catching the word *import* in prose;
  the substantive remainder is the `Zeta23.*` explicit-formula family and
  `YangMills.{RG,ClayCore,P7,P8}` referenced by the vendored `Zeta23` and YM
  checkouts, plus `RequestProject.TaoFramework`.

**The receipt that matters for the build graph:** across the six declared
libraries (`Synthesis`, `Spine`, `Integration`, `Promoted`, `Cuisine`,
`AgdaMirror`) there are now **13 unresolved-by-strict-root imports and zero
absent-from-tree imports** — all 13 are legitimate cross-package references
(`Integration.Kernel.Aristotle.*` → `RequestProject.*` in the
`AristotleArchive` package; `Synthesis.CodecBridge` → `TriadicKernelAlgebra` in
the Klüver package).

**A real gap closed.** `Lean/lakefile.toml` has carried, for several rounds, a
comment that the `AgdaMirror` root aggregate could not be built because
`AgdaMirror.Physics.YangMills` "has never been shipped to this checkout". That
module and its five submodules arrived in this tranche and are now in the tree,
so the import resolves. (Whether the aggregate *elaborates* is a separate
question that a build must answer; see §8.)

---

## 6. Cross-lane structure

### 6.1 Declarations shared across three or more lanes

**`SPINE_SHARED_DECLS.csv`** is the raw donor-payload table (6 312 names).
**`SPINE_SHARED_DECLS_FOCUSED.csv`** is the honest one
(`scripts/spine_shared_decls.py`): `Everything`/aggregate modules excluded,
30 language-generic names excluded, and — on the Lean side — the vendored
mirror corpora excluded, because they are byte copies of each other and
counting them would report *copying* as *sharing*.

*Agda — 237 names in ≥ 3 lanes.* The substantive ones are the corpus's own
cross-domain vocabulary, not arithmetic:

| declaration | lanes | occurrences |
|---|---|---|
| `listCount` | 13 | 170 |
| `canonicalCrossPollinationBoundary` | 9 | 13 |
| `trueNotFalse` / `falseNotTrue` | 8 / 6 | 17 / 15 |
| `observe` | 8 | 14 |
| `activeBidiBoundary` | 6 | 11 |
| `sourceCountRegression` | 6 | 8 |
| `encode` / `decode` | 6 / 6 | 7 / 6 |
| `promote`, `residual`, `producerFor`, `historyBoundary` | 6,6,5,5 | 7,7,12,9 |

*Lean — only 12 names in ≥ 3 first-party lanes*, and all of them are generic
(`of`, `restrict`, `Q`, `P`, `Functional`, `chain`, `refl`, `Status`, `add`,
`join`, `reflect`, `the`). The Lean lanes are **not** re-proving each other's
theorems under different names — with exactly one exception, §6.3.

### 6.2 Hubs

487 `DASHI.*` modules are imported from three or more lanes (aggregates
excluded). The two genuine cross-lane spines are unchanged and are exactly the
structures the reusable `Spine` is meant to own:

| hub | lanes | imports |
|---|---|---|
| `DASHI.Core.Prelude` | 43 | 3 661 |
| `DASHI.Core.IntersectionalNonFactorability` | 21 | 315 |
| `DASHI.Foundations.SSPTritCarrier` | 20 | 123 |
| `DASHI.Algebra.Trit` | 19 | 244 |
| `DASHI.Core.AttributedSourceCore` | 16 | 71 |
| `DASHI.Core.GenericReceipt` | 13 | 112 |
| `DASHI.Core.ObserverRefinementLatticeExact` | 12 | 72 |
| `DASHI.Core.TypedDependencyCore` | 12 | 67 |
| `DASHI.Geometry.SSP369Ultrametric` | 10 | 38 |
| `DASHI.Core.FibreRestrictionCore` | 10 | 36 |

### 6.3 The one real duplication this intake creates

A content-hash sweep of all first-party Lean files finds exactly **two**
byte-identical pairs, both introduced by this tranche:

```
Spine/JMD/ArchitectureDynamics.lean  ==  Promoted/JMD/ArchitectureDynamics.lean   (132d1f12…)
Spine/JMD/FactorVecSheaf.lean        ==  Promoted/JMD/FactorVecSheaf.lean          (743bb5a1…)
```

`Lean/Imported/PROMOTION_STATUS.csv` records that both were already promoted
into the `Promoted` library from the JMD archive, and that
`MonsterMoonshine.lean` was **held out of `Promoted` because it uses
`native_decide`**. The third new file, `Spine/JMD/MonsterMoonshine.lean`, is
sha256-identical (`a8a9bb45…`) to the archive original at
`Lean/Imported/JMD - Full Stack Architecture_aristotle/RequestProject/MonsterMoonshine.lean`,
so the promotion is a verbatim relocation with a checkable provenance chain —
and it carries that `native_decide` into a default build target.

Both copies declare the *same* namespaces and the *same* declaration names
(`FactorVecSheaf.factorVec`, `ArchitectureDynamics.prune`, …). No module in the
tree imports both `Promoted.JMD.*` and `Spine.JMD.*` — only `Promoted.lean`
imports `Promoted.*` — so there is no clash today; there would be one the
moment any aggregate imported both. This is the exact "do not duplicate generic
theorems" situation, and §7.1–7.2 propose the fix.

---

## 7. Concrete proposed Spine adapters

Each is stated with its hypotheses and with the evidence that the hypotheses
hold. **None of them is written into the tree this round**, because this round
was asked not to run a build and an unbuilt adapter is not evidence of
anything. They are ordered by how much they are already earned.

### 7.1 Remove the `native_decide` from the JMD Monster claim, via the existing kernel-checked one

`Spine.JMD.MonsterMoonshine.monster_primeFactors_eq_supersingular`
(`monsterOrder.primeFactors = supersingularPrimes`) is proved `by native_decide`.
The same arithmetic fact is **already proved kernel-checked** in this tree:
`Synthesis.MonsterOrder.monsterOrderNumeral_primeFactors`
(`monsterOrderNumeral.primeFactors = Finset.univ.image AgdaMirror.MonsterOntos.toNat`),
audited in `Synthesis/AxiomAudit.lean` at `propext, Classical.choice, Quot.sound`.

Proposed adapter (three statements, no new hypotheses):

```lean
theorem monsterOrder_eq_numeral :
    MonsterMoonshine.monsterOrder = Synthesis.MonsterOrder.monsterOrderNumeral
theorem supersingularPrimes_eq_base :
    MonsterMoonshine.supersingularPrimes
      = Finset.univ.image AgdaMirror.MonsterOntos.toNat
theorem monster_primeFactors_eq_supersingular' :
    MonsterMoonshine.monsterOrder.primeFactors = MonsterMoonshine.supersingularPrimes
```

Evidence the first two are routine: `monsterOrder` is the literal product
`2^46*3^20*…*71` and `monsterOrderNumeral = exponentProduct monsterOrderExponents`
with the same exponent vector (`Synthesis/MonsterOrder.lean` proves the numeral
value by `norm_num`); `AgdaMirror.MonsterOntos.toNat` enumerates
`2,3,5,7,11,13,17,19,23,29,31,41,47,59,71` in exactly the order of
`MonsterMoonshine.supersingularPrimes` and of `FactorVecSheaf.basisPrime`, so
the image identity is a `decide`. The third then follows by rewriting, with no
`native_decide`, which is what would let `Spine.JMD` be admitted to
`Spine/AxiomAudit.lean` — whose docstring currently asserts that nothing in the
spine uses `Lean.ofReduceBool`.

*Layering caveat, stated because it is real:* as written this makes `Spine`
depend on `Synthesis`, inverting the intended direction. The clean version
first moves the two generic ingredients
(`Synthesis.ExponentFibre.exponentProduct_primeFactors` and the base
enumeration) into `Spine`, and has both `Synthesis` and `Spine.JMD` quote them.

### 7.2 Single owner for the duplicated JMD modules

`Spine.JMD.FactorVecSheaf` / `Spine.JMD.ArchitectureDynamics` are byte-identical
to `Promoted.JMD.*` (§6.3). Proposal: `Spine` becomes the owner (it is the
declared shared home) and `Promoted/JMD/*.lean` become one-line re-exports
(`import Spine.JMD.FactorVecSheaf`). Hypotheses: none — the files are equal.
Cost: one build to confirm no downstream name resolution changes.

### 7.3 FactorVec ↔ the Monster prime base: a reindexing adapter, not a new theorem

`FactorVecSheaf.basisPrime : Fin 15 → ℕ` and
`AgdaMirror.MonsterOntos.toNat : SSP → ℕ` are the same 15 primes in the same
order. Proposed adapter:

```lean
def sspEquivFin15 : SSP ≃ Fin 15                      -- order-matching
theorem toNat_sspEquivFin15 (p : SSP) :
    FactorVecSheaf.basisPrime (sspEquivFin15 p) = AgdaMirror.MonsterOntos.toNat p
theorem factorVec_comp (n : ℕ) (p : SSP) :
    FactorVecSheaf.factorVec n (sspEquivFin15 p) = n.factorization (toNat p)
```

This is what makes `Spine.FiniteReindex` the right owner of the FactorVec
coordinate change, and it connects the JMD sheaf lane to the existing
`Synthesis.ExponentFibre` / `Cuisine.MdlPrimeModel` mask arithmetic **without**
asserting that the JMD document's "valuation sheaf" is a sheaf in any sense
beyond the three lemmas that file actually proves (additivity, functorial
restriction, componentwise extensionality).

### 7.4 Ternary phase: the measured cross-lane carrier

`DASHI.Algebra.Trit` (19 lanes) and `DASHI.Foundations.SSPTritCarrier`
(20 lanes) are, by the hub measurement, the corpus's most-shared carrier, and
`Spine.TritCarrier` already proves the equivariance
(`embed_rot`, `embed_inv`, `reflect_shift`) that makes the Lean mirror an
instance of `Spine.TernaryPhase` rather than a parallel encoding. The adapter
still missing is the *statement of the mirror hypothesis itself*: the Lean side
should carry an explicit, named assumption "`AgdaMirror.DASHIAlgebra.Trit`
faithfully mirrors `DASHI.Algebra.Trit`'s rotation semantics", discharged only
by an Agda kernel receipt, which does not exist here. Until then every
trit-lane transport is **conditional**, and should say so in its docstring.

### 7.5 Observer / residual: adapt the Agda hubs, don't restate them

`DASHI.Core.ObserverRefinementLatticeExact` (12 lanes) and
`DASHI.Core.TrajectoryResidueExact` (9 lanes) are the Agda-side analogues of
`Spine.Observer` (`MeanObserver`, with its two nondegeneracy witnesses) and of
`Integration.ResidualTaxonomy`. The narrow adapter is a Lean structure whose
fields are exactly the Agda record's obligations, instantiated by the existing
`Integration` residual kernels — one direction only (Lean instance ⇒ the Agda
interface's Lean shadow), because the converse would need the Agda proofs.

### 7.6 The adapter that is *not* proposed, and why

The newly arrived Yang–Mills mirror lane is **not** analytic content and no
`Spine.RateBlockSchur` / `Spine.TwoRegime` adapter to it is evidenced.
`AgdaMirror/Physics/YangMills/` consists of `ProofTargetSurface` records with
`String` labels (807 lines of them in `P01P33ProofSurfaces.lean`), a source
authority enumeration whose headline definition is
`clayYangMillsPromoted : Bool := false` (with
`clayYangMillsPromoted_false : clayYangMillsPromoted = false := rfl`), eleven
trivial numeric lemmas (`0 < 1`, `9271 < 10000`, `fourQ < 1`), and two
structure-level graph-distance inequalities. That is a bookkeeping surface for
an *open* problem, and the corpus says so itself. Claiming a Spine bridge here
would be inferring a connection from vocabulary.

---

## 8. Status of every class of item

**Machine-checked Lean (unchanged by this round).** Everything already built and
axiom-audited in `Synthesis`, `Spine`, `Integration`, `Promoted`, `Cuisine` —
including `Spine.RateBlockSchur` from the previous round. No first-party Lean
file was edited this round, so none of those receipts moved.

**Adopted Lean source, *not* build-verified.** The 18 first-party additions of
§3.1, of which 11 sit inside a library glob (`Spine.JMD*`,
`AgdaMirror.Physics.YangMills*`). This round was instructed not to run a local
build, so the honest status is: *present, statically consistent (all imports
resolve in the tree; no `sorry`, no `axiom`, no `@[implemented_by]` in any of
the 11), elaboration unverified*. One known risk is named rather than hidden:
`Spine/JMD/MonsterMoonshine.lean` uses `native_decide`, which the project's own
promotion policy has previously used as grounds to hold a file out of a built
library; §7.1 removes the need for it.

One deliberate non-edit: the audited root aggregate `Lean/Spine.lean` was **not**
changed to `import Spine.JMD`. The `Spine` library glob (`Spine`, `Spine.*`)
already covers the new lane, so the import would add no coverage, and leaving
it out keeps the claim in `Spine/AxiomAudit.lean` — that nothing it audits uses
`Lean.ofReduceBool` — literally true of the aggregate it audits. The wiring is
proposed, not performed, and should follow §7.1 in a round that can build.
`Lean/Spine/README.md` (also adopted) is documentation, not a module.

**Vendored Lean corpus, source-only by construction.** `Lean/ImportedLeans/`:
3 887 `.lean` files, **1 899 of them containing `sorry`** (30 308 occurrences),
153 that declared 419 `axiom`s before those were commented out on intake
(§3.1b), 123 using `native_decide`. It is a provenance dump of
77 imported Aristotle archives, not a proof library, and it is deliberately
outside every build target. Its own
`aristotle-results/canonical-corpus/manifest.json` reports 81 archives
discovered, 77 imported, 44 139 unique content blobs — but **only `README.md`
and `manifest.json` were shipped**: the `records/` shards and `blobs/sha256/`
store the README describes are not in this tranche. That is a named missing
edge, not an inconsistency in the index. (The 4 unimported archives are parton
distribution datasets — MSHT20, NNPDF40, CT18 ×2 — with no Lean or Agda
content.)

**Source-only Agda.** All 17 521 `.agda` files. No Agda toolchain exists here,
so hashes, import resolution and declaration counts are text-level facts.
Within the delivered payload: **0 `sorry`, 0 `axiom`, 124 files with a
`postulate`, 6 430 files carrying `… ≡ true` Boolean-ledger obligations.**

**Conditional interfaces.** Every Boolean `≡ true` ledger, every route/compiler
record and every record-of-hypotheses in both languages: bookkeeping whose
premises are asserted, not discharged. The trit mirror hypothesis of §7.4 is in
this class.

**Open frontiers.** 108 absent Agda modules in 158 edges (§5.1, dominated by
the Moonshine `P11` Brandt–Hecke family and `Cognition.PNF`); 31
absent-from-tree Lean modules (§5.2); the JMD duplication and its
`native_decide` (§6.3, §7.1); no Agda kernel receipt for anything; and the
mathematical problems themselves — Yang–Mills, Navier–Stokes and Riemann — are
untouched and open. This round proved no new theorem and closed no
mathematical obligation. Its output is an index, a disposition and a frontier.

---

## 9. Artefacts and how to regenerate them

| file | content |
|---|---|
| `SPINE_INDEX.csv` | one row per delivered path (20 074): hashes, size, lines, lane, module, imports, declarations, markers, **pre-intake** status and reconciliation verdict |
| `SPINE_IMPORT_EDGES.csv` | every import edge of the payload with its resolution |
| `SPINE_DIVERGENCES.csv` | the 43 divergences with the declarations and imports at stake |
| `SPINE_FRONTIER.csv` | imported-but-absent modules as seen from the donor payload |
| `SPINE_FRONTIER_POST.csv/.json` | the same, recomputed over the tree after intake, with strict vs any-source-root resolution |
| `SPINE_SHARED_DECLS.csv` | raw names in ≥ 3 lanes |
| `SPINE_SHARED_DECLS_FOCUSED.csv` | the de-noised table used in §6.1 |
| `SPINE_INTAKE_LEDGER.csv` | per-path disposition and both hashes |
| `SPINE_AXIOM_NEUTRALISATION.csv` | the 153 vendored files whose 419 `axiom` declarations were commented out, with names, line ranges and before/after hashes |
| `SPINE_INDEX_SUMMARY.json` | aggregate counts |
| `Provenance/spine-20260910/` | 43 donor versions + 1 staged artefact, verbatim |

```
python3 scripts/spine_intake_index.py   <tranche-root> .
python3 scripts/spine_intake_apply.py   <tranche-root> . [--apply]
python3 scripts/spine_frontier_post.py  .
python3 scripts/spine_shared_decls.py   .
python3 scripts/spine_axiom_neutralise.py <file-list> . [--apply]
```

---

## 10. Claim boundaries

No Agda file has been typechecked and no Lean build was run, by instruction.
Nothing here asserts a physical theory, a Clay result, or any Yang–Mills,
Navier–Stokes, Riemann or Moonshine closure; the corpus's own
`clayYangMillsPromoted = false` is the accurate summary of the YM lane's
status. Import resolution, declaration extraction and hashing are text-level
facts about source, and a source index is not a kernel receipt. The one
arithmetic identity this report leans on for §7.1 —
`monsterOrderNumeral.primeFactors = toNat '' SSP` — is a previously proved,
previously audited theorem of this repository about a natural number, and the
reading of that numeral as the order of the Monster group remains provenance,
not a theorem.
