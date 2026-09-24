# TOE overlay 2026-09-12 — verified intake, index, and NS reconciliation

This records the intake of `toe-overlay-output-20260912.tar.gz`, the indexing of
everything it delivers, and the Navier–Stokes Lean work that reuses it.
No `lake build` was run, by instruction; how the new material *was* checked is
stated explicitly in §5.

---

## 1.  Archive verification — the bundle is truncated

| item | value |
|---|---|
| file | `toe-overlay-output-20260912.tar.gz` (project root) |
| size | 32,059,392 bytes |
| sha256 | `929a902701b7d2aea06e6457cb4945a499cbdcb5f7e69bc2f5aa7b2cde2858a7` |
| tar/gzip status | **truncated** — `gzip: unexpected end of file`, `tar: Unexpected EOF in archive` |
| entries recovered | **9,218 regular files**, all under `output-final_aristotle/` |
| top-level manifest | **none** — the bundle carries no `SHA256SUMS`, `SOURCE_MANIFEST.txt` or `HANDOFF.md` at its root |

Recovered payload by type: **9,030 `.lean`**, 49 `.json`, 45 `.md`, 25 `.toml`,
21 `.csv`, 2 nested `.tar.gz`, plus `lean-toolchain` files.

Because there is no outer manifest, no checksum comparison against a declared
payload is possible at the outer level; the two **nested** archives do carry
manifests, and those were verified:

### 1a. `toe-agda-master-delta-20260911.tar.gz` — complete, verified

* `SHA256SUMS`: **4/4 entries `OK`**, 0 mismatches (`SOURCE_MANIFEST.txt` plus
  2 Agda payload files).
* Base Agda commit `a866c675f60ad2ee5cd5a96f213cdd3e7e50cf26`, target
  `4c8ebfb733f5768ce7ed61388cc5272ececd5d0d`.
* Payload: `DASHI.Reasoning.FibreRoutingGrokkingMoEBrainCrossPollinationExact`
  and the `DASHI.Reasoning.Everything` rollup.

### 1b. `toe-full-crosspollination-agda-state-20260910.tar.gz` — incomplete

This is the last member of the outer archive and is itself cut off.

* `SHA256SUMS` declares **15,958** payload entries.
* **5,136 verified `OK`**; **1 checksum mismatch** (the final, partially written
  file); **10,821 files not present at all**.
* So **68 % of the declared Agda payload of this bundle was not delivered.**

---

## 2.  What the delivered material is, against the project

### Lean (`output-final_aristotle/Lean/` vs the project's `Lean/`)

| status | count |
|---|---|
| byte-identical | 3,309 |
| divergent (both sides, different bytes) | 10 |
| bundle-only (new here) | 5,699 |
| project-only | 0 |

Full per-path table with both sha256 values: `LEAN_INDEX.csv`.
Bundle-only breakdown: `ImportedLeans/` 3,887, `Imported/` 1,341, `DASHI/` 193,
`Integration/` 187, `Promoted/` 58, `AgdaMirror/` 11, `Spine/` 9,
`Synthesis/` 8, plus `NavierStokesClosure.lean`, `YangMillsClosure.lean`,
`YangMillsContinuumGap.lean`, `Promoted.lean` and
`Proposed/FibreRoutingProjectionAdapter.lean`.

### Agda (delivered portion of the nested full-source archive)

| status | count |
|---|---|
| byte-identical | 4,122 |
| divergent | 318 |
| bundle-only (new here) | 695 |
| **delivered total** | **5,135** |

Full per-path table: `AGDA_INDEX.csv`.  The 695 new modules are
`DASHI/Physics/**` 624 (YangMills 209, Plasma 90, ExoticGravity 85,
QuantumVacuum 79, Semiconductor 74, Textile 28, GR 24, Optics 10, Materials 7,
Nuclear 6), `DASHI/Wikimedia` 40, `DASHI/Reasoning` 11, `DASHI/Statistics` 9,
`DASHI/Policy` 6, `DASHI/Topology` 4, one root module.  **None** is an
`NSTriadKN*` Closure module, and none of the 13 divergent
`DASHI/Physics/Closure*` files is an `NSTriadKN*` module either: **the NS Agda
lane is unchanged by this bundle.**

---

## 3.  The named NS frontier items — what is and is not here

| requested item | status in this bundle |
|---|---|
| **R582 / R584 class-norm budget transport** | **not delivered.**  `NSTriadKNClassNormBudgetToBonyGramPaymentRound582Exact.agda`, `NSTriadKNNestedSlotBonyClassNormBidiRound584Exact.agda` and the whole rounds-570–585 family (**29 modules**) are *named in the nested `SOURCE_MANIFEST.txt`* but fall inside the 10,821 truncated-away entries.  They are also absent from the project, whose NS Closure lane tops out at Round 530.  No Lean or Agda work on R582/R584 was therefore possible from supplied material; nothing was invented in their place. |
| **R145 anti-parallel slot-kernel factorisation** | present in the project already (`DASHI/Physics/Closure/NSTriadKNAntiParallelHelicitySlotKernelRound145Exact.agda`), and genuinely constructive (a `RingSolver` identity, no postulate).  **Worked**: a Lean carrier now exists — see §4.3 — including the endpoint corollary the Agda round marks `false`. |
| **comparable-shell, separately** | the lane's `gramOperatorBound_fails_on_comparable_shells` stands unchanged; the adopted Spine kernel supplies the matching domain-neutral lower bound `schur_form_ge_half_mul_multiplicity`, now quotable from the NS lane as `ClayNS.SpineAdapter.spine_multiplicity_lower_bound`. |
| **outer spectator / weight spacetime seam** | **not closed, not attempted here.**  No delivered Lean module addresses it; the R5xx Agda material that names it is in the truncated portion.  It remains the open analytic seam, together with the cancellation requirement recorded in §6. |

---

## 4.  Adopted, reused, and wired

### 4.1  Put on the build surface (previously vendored and inert)

The project's `Lean/` tree was matched by **no** `lakefile.toml` glob, so none of
the TOE Lean corpus could be imported.  Two single-module libraries were added,
so exactly the modules the NS lane consumes become importable and nothing else
in that tree is compiled:

```toml
[[lean_lib]] name = "Spine"    srcDir = "Lean" globs = ["Spine.RateBlockSchur"]
[[lean_lib]] name = "Proposed" srcDir = "Lean" globs = ["Proposed.FibreRoutingProjectionAdapter"]
```

### 4.2  `Lean/Spine/RateBlockSchur.lean` — adopted and consumed

Adopted byte-identical, sha256
`f24f666e9eee0f5269709b3d066de78379380e94974cab16adc95e80dcef10eb`.
It is the domain-neutral form of the dyadic rate-block Schur test the NS lane had
developed privately.  New adapter
`RequestProject/NavierStokes/SpineRateBlockAdapter.lean`:

| adapter theorem | exact dependency |
|---|---|
| `spine_dyadicRateBlocks_iff`, `spine_blockMultiplicity_iff` | `Iff.rfl` — the NS hypotheses **are** the Spine ones at `ι = Wave`; no transport needed |
| `sum_resForm_le_blockMultiplicity_ofSpine` | `Spine.RateBlockSchur.schur_form_le_blockMultiplicity` + `ClayNS.TTStar.herm_re_le_nrm_mul` + `ClayNS.Waleffe.nrm_sq` |
| `gramOperatorBound_of_rateBlockMultiplicity_ofSpine` | the above + `viscousPairRate nu p (k−p) ≥ nu·wsq p` |
| `gramOperatorBound_ofSpine_eq_local` | both routes prove the same proposition, so the lane's private kernel is redundant, not merely parallel |
| `spine_multiplicity_lower_bound` | `Spine.RateBlockSchur.schur_form_ge_half_mul_multiplicity` |

**The literal consumer `GramOperatorBound nu modes G k (32·m)` is now paid by a
proof that factors through the TOE Spine carrier.**

### 4.3  `RequestProject/NavierStokes/SlotKernelAntiParallel.lean` — R145 Lean carrier

Lean counterpart of the R145 Agda round on the lane's own `ℂ³` carrier:
`slotKernel_bacCab` (BAC–CAB), `slotKernel_factorsThrough_antiParallelDefect`
(the transverse factorisation through `Σ = P+Q`), and
`slotKernel_eq_zero_of_antiParallel` — **the endpoint the Agda ledger flags
`round145AntiParallelEndpointZeroNormalizationClosed = false`**, now a theorem,
with an explicit non-vacuity witness and a nonzero-defect/nonzero-kernel witness
so the vanishing is genuinely carried by the defect.
`round145IntraShellL2AggregationClosed` and `round145PackageAClosed` remain
false and nothing here changes them.

### 4.4  `Lean/Proposed/FibreRoutingProjectionAdapter.lean` — reused at a named NS consumer

The donor ships it as *proposed*, outside every build target, recording that no
Lean consumer of its fibre-routing material exists.  Its generic layer
(`FactorsThrough`, `Determines`, `ProjectionCollision`,
`determines_of_factorsThrough`, `collision_blocks_factorisation`,
`not_determines_of_collision`) is now used verbatim in
`RequestProject/NavierStokes/GramConsumerFactorisation.lean`:

* `gramConsumer_factorsThrough_gramProfile` / `gramConsumer_determined_by_gramProfile`
  — `GramOperatorBound` reads the cells only through their Gram profile;
* `massProfile_collision` / `massProfile_not_determines` — the mass profile
  alone does **not** determine the Gram form (explicit two-mode witness with
  identical masses and forms `1` and `0`), so no mass-only producer can pay the
  consumer.

The Fly/VFB painted-domain specimen of the prototype is *not* used and no claim
is inherited from it.

### 4.5  `Provenance/ns_worker_result/.../RateBlockGramBound.lean`

sha256 `e1f7445252e1e276c77d9dc2f36f8b1c91619b2001bad1822238f66a4b3c52d5` —
**byte-identical to the project's own
`RequestProject/NavierStokes/RateBlockGramBound.lean`.**  It is this project's
prior NS work returned as provenance; there is nothing to import from it.  Its
mathematical content is exactly what §4.2 now factors through the Spine copy.

### 4.6  Other source adopted (indexed, not yet consumed)

`Lean/Spine/{TransverseGram,SchurComplement,SchurBlock,FiniteReindex}.lean`,
`Lean/Spine/JMD{,/ArchitectureDynamics,/FactorVecSheaf,/MonsterMoonshine}.lean`,
`Lean/Integration/{ContextIndexedRole,RealisationAdequacy,CoordinateSufficiency,DeclaredCarrier}.lean`,
`Lean/NavierStokesClosure.lean`, and the Agda overlay module
`DASHI/Reasoning/FibreRoutingGrokkingMoEBrainCrossPollinationExact.agda`
(scanned: no `postulate`, no `TERMINATING`, no `trustMe`).

---

## 5.  How the new Lean material was checked

No `lake build` was run.  Each new or newly consumed module was type-checked
individually with the Lean frontend under the project's own environment
(`lake env lean`), together with its transitive project imports:

* `Lean/Spine/RateBlockSchur.lean` — no errors, no warnings;
* `Lean/Proposed/FibreRoutingProjectionAdapter.lean` — no errors, no warnings;
* the 27-module NS import chain up to
  `RequestProject.NavierStokes.RateBlockGramBound` — no errors, no warnings;
* the three new NS modules — no errors, no warnings.

`#print axioms` on every headline theorem listed above returns exactly
`[propext, Classical.choice, Quot.sound]`.  A scan of all five files finds no
`sorry`, no `axiom`, no `@[implemented_by]`.  `lake --no-build build` resolves
all five new targets, so the lakefile configuration is valid; the artefacts
themselves are of course not lake-traced, since no build was run.

---

## 6.  Retained mismatches

1. **Spine inner-product instance vs the NS carrier.**
   `Spine.RateBlockSchur.schur_gram_le_blockMultiplicity` is stated for `E` with
   `[NormedAddCommGroup E] [InnerProductSpace ℂ E]`, using `inner ℂ` and `‖·‖`.
   NS cells live in `Fin 3 → ℂ`, which carries Mathlib's **sup-norm** `Pi`
   instance, with the Hermitian form and Euclidean mass supplied by the lane's
   own `herm`/`nsq`.  That instance therefore does not apply.  The adapter goes
   through the carrier-free scalar form `schur_form_le_blockMultiplicity` and
   supplies Cauchy–Schwarz by hand.  Repair would mean transporting the lane to
   `EuclideanSpace ℂ (Fin 3)` — a refactor of every NS file, not done.
2. **`Spine/TransverseGram.lean`, `SchurComplement.lean`, `SchurBlock.lean`** are
   developed for a **real** inner product space (`⟪·,·⟫_ℝ`, `area2`).  The NS
   transverse frame split is over the reals but acts on `Fin 3 → ℂ` with the
   lane's custom pairing; consuming them needs a
   `Fin 3 → ℂ ≃ₗ EuclideanSpace ℝ (Fin 6)` transport that does not exist in
   either corpus.  Adopted as source, not consumed.
3. **`Lean/NavierStokesClosure.lean`** derives NS-1…NS-4 from an *assumed*
   enstrophy depletion inequality `Z' ≤ −2αZ` and an *assumed* BKM criterion.
   Both are named hypotheses of the theorems.  It is a conditional chain, not a
   producer for anything in this lane, and is adopted as provenance only.
4. **10 divergent Lean paths** (project version retained, donor version preserved
   verbatim under `Provenance/toe-overlay-20260912/donor-version/lean/`):
   `AgdaMirror/LoomRelationAlgebra.lean`, `AgdaMirror/MoonshineEarn.lean`,
   `Integration.lean`, `Integration/AxiomAudit.lean`, `MoonshineFractran.lean`,
   `Spine.lean`, `Spine/AxiomAudit.lean`, `Synthesis.lean`,
   `Synthesis/AxiomAudit.lean`, `Synthesis/EndToEnd.lean`.  The donor versions
   are rollup/audit aggregators listing the 5,699 modules not adopted here, so
   adopting them would break the project's import closure.  Both sha256 values
   are in `LEAN_INDEX.csv`.
5. **Agda `DASHI/Reasoning/Everything.agda`** — the donor rollup is a strict
   superset (114 imports vs 7) but is **not dependency-complete here**: 6 of its
   imports exist in neither corpus.  Project version retained; donor version
   preserved under `Provenance/toe-overlay-20260912/donor-version/agda/`.
6. **318 divergent Agda paths** retained at the project version, with both
   hashes in `AGDA_INDEX.csv`; none is an NS `NSTriadKN*` module.
7. **Agda Boolean route ledgers are not treated as Lean proofs anywhere.**  The
   R145 flags were read as *statements of what the round claims*, and the one
   flag this tranche moves (`…EndpointZeroNormalizationClosed`) was moved by
   proving the corresponding Lean theorem, not by copying the flag.

---

## 7.  What remains

* **Package A and the literal periodic Clay regularity target are not closed and
  nothing here claims otherwise.**  No target was weakened; no axiom, postulate,
  conditional bridge or placeholder was added.
* The Gram-bound frontier is unchanged in substance and sharper in form.  The
  positive route is cancellation-free and therefore linear in the rate-block
  multiplicity (`Spine.RateBlockSchur`, both directions); the consumer provably
  reads only the *signed* Gram profile and provably cannot be paid from masses
  alone (`ClayNS.GramConsumer`).  So a truncation-uniform constant must come
  from cancellation among the signed entries of the physical outer cells.
* The R145 lane now has a Lean carrier for its pointwise algebra, including the
  anti-parallel endpoint.  The intra-shell `L²` aggregation above it is
  untouched.
* The outer spectator / weight spacetime seam, and the R582/R584 class-norm
  budget transport, cannot be worked from what was delivered: those sources are
  in the truncated 68 % of the nested archive.  Re-delivering that archive intact
  is the precondition for taking them up.
