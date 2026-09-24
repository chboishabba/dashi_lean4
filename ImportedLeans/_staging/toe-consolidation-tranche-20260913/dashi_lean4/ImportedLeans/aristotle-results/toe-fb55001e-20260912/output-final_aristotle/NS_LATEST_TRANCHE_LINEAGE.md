# The 2026-09-12 NS Aristotle source tranche — verification, index, lineage, seams

Subject: `ns-latest-source-tranche-to-toe-20260912.tar.gz`
(sha256 `138da4e929580da6653eed9f69816a75ad5c05c1fdda8c29e3c730a73f96a670`,
35 515 196 bytes, at the project root).

This is the intake record for that delivery, its index against this corpus, the
bidirectional lineage of the four named Lean terms, and an exact statement of
what is *not* closed. **No build was run** — the delivery does not request one
and none was performed; every claim below is either a checksum/​byte comparison
or a source-level reading, and is labelled as such.

Generated artefacts (regenerate with `python3 scripts/ns_latest_index.py`; add
`--verify-archive` to re-check all 21 730 checksum lines from the tarball):

| artefact | contents |
|---|---|
| `NS_LATEST_INDEX.csv` | one row per preserved payload file: hash, lines, imports, declaration counts, `sorry`/`axiom`/`native_decide` counts |
| `NS_LATEST_DECLS.csv` | 2 848 top-level Lean declarations of the preserved payload |
| `NS_LATEST_IMPORT_EDGES.csv` | every `import` of the preserved Lean, classified and resolved |
| `NS_LATEST_DELTA.csv` | all 21 728 delivered files against this repository (identical / differs / absent, plus where the same content already lives here) |
| `NS_LATEST_LINEAGE.csv` | the 70 declarations of the four named modules against the public forced-blowup corpus and the first-party DASHI Lean corpus |
| `NS_LATEST_SUMMARY.json` | the counts quoted here |

---

## 1. Delivery verification

| check | result |
|---|---|
| `sha256sum -c SHA256SUMS` over the extracted archive | **21 730 / 21 730 OK**, 0 failed, exit 0 |
| `SOURCE_MANIFEST.txt` vs the extracted payload | **equal**: 21 728 paths on both sides, sorted diff empty |
| `SOURCE_MANIFEST.txt` vs the payload lines of `SHA256SUMS` | **byte-identical** |
| source-only, as declared | **yes**: 0 `.olean`, 0 `.git/` paths. 376 paths sit under a vendored `Zeta23Bridge/.lake/packages/Zeta23` tree, but all of them are `.lean`/text sources, not build products |
| re-verification after copying into this repository | **258 / 258** preserved files match their manifest hashes |

No delivery anomaly. The `HANDOFF.md` states the upstream raw result archive
sha256 (`0d6962b2…`); that archive is not part of this delivery, so that value
is recorded, not checked.

**Preserved in-tree** at `Provenance/ns-latest-20260912/`: the donor `HANDOFF.md`,
`SOURCE_MANIFEST.txt` and `SHA256SUMS`, plus a `payload/` subtree holding the
NS-relevant 258 files verbatim — the whole 174-module Lean NS lane, all 69
`docs/ns-clay-contract/` reports, the donor's `lakefile.toml`, `lean-toolchain`
and `ARISTOTLE_SUMMARY.md`, the 11-file `Provenance/toe-overlay-20260912/`
donor-version directory, and the one NS Agda module new to this corpus. The
remaining 21 470 delivered files are either already byte-identical here or are
out of NS scope (see §2); every one of them remains recoverable from the
committed tarball, and every hash is in `NS_LATEST_DELTA.csv`.

## 2. What the delivery is, measured against this corpus

Path-matched comparison (delivered `Lean/…` ↔ `Lean/…`, delivered `DASHI/…` ↔
`Agda/DASHI/…`, everything else at the same relative path; the preservation copy
itself is excluded from the repository side so it cannot match itself):

| status | files |
|---|---|
| byte-identical to this repository | 17 905 |
| path-matched but different bytes | 1 592 (1 579 `.agda`, 10 `.lean`, 2 `.md`, 1 `.toml`) |
| absent from this repository | 2 231 |
| *(content-level)* delivered content already present here under **some** path | 18 814 of 21 728 |

The 2 231 absent files break down as `Docs/` 889, `Zeta23Bridge/` 328 (326 of
them vendored `.lake/packages` sources), `monster/` 269,
`THE-ERIKSSON-PROGRAMME/` 249 (245 of them Yang–Mills), `RequestProject/` 174,
`docs/` 160 (69 of them `docs/ns-clay-contract`), `RiemannAnalytic/` 69,
`DASHI/` 62 (61 Yang–Mills, 1 Navier–Stokes),
`Provenance/toe-overlay-20260912/` 11, `cubical/` 8, `vendor/` 3, `AGENTS.md`.
Yang–Mills material is out of scope for this intake and was **not** imported.

Exactly **one** Agda module outside the YM lane is new here:
`DASHI/Papers/NavierStokes/ClayCarrierVacuityAudit.agda` (§5.3).

### 2.1 The ten divergent Lean paths are a clean round trip, not a conflict

The donor's vendored `Lean/` tree is an *older* TOE snapshot: for all ten
divergent Lean paths this repository's version is the superset (it carries the
later `Spine.*`, `Synthesis.*` and `Integration.*` imports, the audit lines for
them, and `decide` where the donor copy still has `native_decide`). The donor
did not overwrite them: it preserved this corpus' versions verbatim under
`Provenance/toe-overlay-20260912/donor-version/`, and all eleven of those files
(ten Lean, one Agda `DASHI.Reasoning.Everything`) are **byte-identical to the
versions now in this repository**. Nothing of ours was lost or silently edited
on the round trip, and nothing of the donor's older aggregates is adopted here.

The two TOE modules the NS lane actually *consumes* are byte-identical in both
directions:

| module | sha256 (both sides) |
|---|---|
| `Lean/Spine/RateBlockSchur.lean` | `f24f666e9eee0f5269709b3d066de78379380e94974cab16adc95e80dcef10eb` |
| `Lean/Proposed/FibreRoutingProjectionAdapter.lean` | `524330b73d31ee3241f600d698296092f80aef2f23d1e7620108f4cc0c996775` |

### 2.2 The 1 579 divergent Agda files

These are ordinary version drift between the donor's older Agda snapshot and
this corpus' newer one (e.g. `DASHI/Algebra/BalancedTernary.agda` differs only
in constructor-declaration layout). 124 of them are under
`DASHI/Physics/Closure`. None of the NS-lane modules relevant below is affected:
`NSTriadKNAntiParallelHelicitySlotKernelRound145Exact.agda` and
`NSTriadKNFeffermanPeriodicClayStatementExact.agda` are byte-identical on both
sides. This corpus' versions are retained throughout; per-path hashes for both
sides are in `NS_LATEST_DELTA.csv`.

## 3. The preserved Lean NS lane, as source

174 Lean files, 55 110 lines, 2 771 top-level declarations, 2 274 of them
`theorem`/`lemma`. Token scan over comment-stripped source: **0 `sorry`,
0 `admit`, 0 `axiom` declarations, 0 `native_decide`.** That is a lexical
result about the delivered sources; they were not elaborated here (the lane is
not on this project's build surface), so it is not a build receipt. The donor
reports per-module `lake env lean` checks and
`#print axioms` results of `[propext, Classical.choice, Quot.sound]`; those are
its claims, recorded here as claims.

Import edges of the lane: 241 intra-lane, 12 `Mathlib`, 1 `Spine.RateBlockSchur`,
1 `Proposed.FibreRoutingProjectionAdapter`, 0 unresolved.

## 4. The four named terms — exact consumers and transports

`RateBlockGramBound.lean` is **not new to this corpus**: it is byte-identical
(`e1f74452…`) to the copy already held at
`Provenance/ns_worker_result/RequestProject/NavierStokes/RateBlockGramBound.lean`.
It is re-delivered as the substrate of the other three. Its 24 declaration names
are exactly the 24 names `NS_LATEST_LINEAGE.csv` reports as shared with the
first-party DASHI Lean corpus — the overlap is that same file, not an
independent coincidence.

### 4.1 `SpineRateBlockAdapter` (6 declarations)

The literal consumer is `ClayNS.Schur.GramOperatorBound nu modes G k A`, defined
in `OperatorSchurBlockCancellation.lean:571` as

```
∑_{p,q∈modes} Re⟪G p, G q⟫ / (viscousPairRate ν p (k−p) + viscousPairRate ν q (k−q))
  ≤ A · (∑_{p∈modes} ‖G p‖² / |p|²) / (2ν)
```

| adapter term | what it does | transport used |
|---|---|---|
| `spine_dyadicRateBlocks_iff`, `spine_blockMultiplicity_iff` | identify the NS-lane hypotheses with `Spine.RateBlockSchur.DyadicRateBlocks` / `BlockMultiplicity` at `ι = Wave` | **none** — `Iff.rfl`. Confirmed at source level: the two definition bodies are literally the same formula (`4^(blk p) ≤ lam p ∧ lam p < 4·4^(blk p)`; `∀ b, {p ∈ S | blk p = b}.card ≤ m`), differing only in binder names |
| `sum_resForm_le_blockMultiplicity_ofSpine` | the NS pair estimate from the domain-neutral kernel | instantiate `Spine.RateBlockSchur.schur_form_le_blockMultiplicity` at `a p q = Re⟪G p,G q⟫`, `n p = ‖G p‖`; NS-side inputs `ClayNS.TTStar.herm_re_le_nrm_mul` (`SignedRemainderResolventBudget.lean:69`) and `ClayNS.Waleffe.nrm_sq` (`WaleffeAmplitude.lean:81`) |
| `gramOperatorBound_of_rateBlockMultiplicity_ofSpine` | **pays the literal consumer** with `A = 32·m` | the above plus `viscousPairRate ν p (k−p) ≥ ν·wsq p` from `viscousPairRate ν p q = ν·(wsq p + wsq q)` (`ResolventGramFlux.lean:322`) |
| `gramOperatorBound_ofSpine_eq_local` | the Spine route and the lane's private route prove the *same* proposition | none; conjunction of the two proofs |
| `spine_multiplicity_lower_bound` | quotes `Spine.RateBlockSchur.schur_form_ge_half_mul_multiplicity`, the matching `m/2` lower bound | none; direct re-export at `ι = ℕ` |

**Retained carrier mismatch — now partly repaired on the spine side.**
`Spine.RateBlockSchur.schur_gram_le_blockMultiplicity` — the inner-product-space
instance of the same kernel — is stated for `[NormedAddCommGroup E]
[InnerProductSpace ℂ E]`. NS cells live in `Fin 3 → ℂ` with Mathlib's
**sup-norm** `Pi` instance and the lane's own `herm`/`nsq`, so that instance does
not apply; the adapter goes through the carrier-free scalar form and supplies
Cauchy–Schwarz by hand.

This intake adds `Lean/Spine/RateBlockSchurPiCarrier.lean`, which owns that step
once on the spine side, for the scalar Gram form, at arbitrary `n` and arbitrary
index type:

| new spine term | statement |
|---|---|
| `Spine.RateBlockSchurPi.hermPi_eq_inner` | `⟪toLp 2 u, toLp 2 v⟫_ℂ = ∑ i, conj (u i) · v i` — the lane's pairing **is** the `EuclideanSpace ℂ (Fin n)` inner product |
| `Spine.RateBlockSchurPi.nrmPi_eq_norm` | `‖toLp 2 u‖ = √(∑ i, normSq (u i))` — the lane's mass **is** the Euclidean norm |
| `Spine.RateBlockSchurPi.hermPi_re_le_nrmPi_mul` | Cauchy–Schwarz on the plain carrier, derived from the transport, not re-proved |
| `Spine.RateBlockSchurPi.schur_gramPi_le_blockMultiplicity` | the rate-block Schur bound written with `hermPi`/`nsqPi` on `ι → (Fin n → ℂ)` — the exact shape the NS lane consumes |

`lake build Spine` succeeds with these wired into `Lean/Spine.lean` and
`Lean/Spine/AxiomAudit.lean`; the audit prints `[propext, Classical.choice,
Quot.sound]` for all four, and the file contains no `sorry`, `axiom` or
`native_decide`. (Repairing the *full* mismatch — the real-Gram spine kernels of
§6.7 — still needs a genuine `Fin 3 → ℂ ≃ EuclideanSpace ℝ (Fin 6)` transport and
is not done.)

### 4.2 `GramConsumerFactorisation` (26 declarations)

Uses the generic layer of `Proposed.FibreRoutingProjectionAdapter`
(`FactorsThrough`, `Determines`, `ProjectionCollision`,
`determines_of_factorsThrough`, `collision_blocks_factorisation`,
`not_determines_of_collision`) verbatim, at an NS consumer:

* `gramConsumer_factorsThrough_gramProfile` / `gramConsumer_determined_by_gramProfile`
  — `GramOperatorBound` reads a cell family only through its Gram profile
  (signed entries `Re⟪G p,G q⟫` together with masses `‖G p‖²`);
* `massProfile_collision`, `massProfile_not_factorising`,
  `massProfile_not_determines` — an explicit two-mode witness (coherent vs.
  sign-flipped family) with identical masses and Gram forms `1` and `0`, so the
  mass profile alone determines neither the Gram form nor the consumer.

This is a statement about what the consumer reads; it is not a bound and closes
no obligation. Its force is negative and precise: **no mass-only producer can
pay `GramOperatorBound`.**

### 4.3 `SlotKernelAntiParallel` (14 declarations)

Lean carrier for the Agda round
`DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact`
(byte-identical in both corpora). The round's Boolean ledger in *this*
repository reads, at lines 152–173:

| flag | value |
|---|---|
| `round145HighHighSlotKernelAntiParallelFactorizationClosed` | `true` |
| `round145AntiParallelEndpointZeroNormalizationClosed` | `false` |
| `round145IntraShellL2AggregationClosed` | `false` |
| `round145PackageAClosed` | `false` |

The Lean module proves `slotKernel_bacCab` (BAC–CAB over `ℂ` for the bilinear
dot product), `slotKernel_factorsThrough_antiParallelDefect` (under the two
transversality relations every scalar factor is a reading of `Σ = P+Q`),
`slotKernel_eq_zero_of_antiParallel` — the endpoint the second flag marks
`false` — and two non-degeneracy witnesses showing the endpoint is neither
vacuous nor trivial. Dependencies: `WaleffeAmplitude` only (1 lane module) plus
`Mathlib`; no Spine, no Agda, no ledger flag is imported or asserted. The two
remaining `false` flags are untouched and remain open.

### 4.4 Consumers, honestly

Within the delivered lane, **nothing imports the three new modules**: their
reverse-dependency sets are empty. They are leaves — 31 of the lane's 174
modules are, and the lane has no rollup module (`RequestProject/Main.lean`
imports only `Mathlib`). Their forward dependencies are 27, 27 and 1 lane
modules respectively.

Conversely, in *this* corpus the two consumed TOE modules had **no mathematical
consumer at all** before this tranche: `Spine.RateBlockSchur` is referenced only
by the `Lean/Spine.lean` rollup and `Lean/Spine/AxiomAudit.lean`, and
`Proposed.FibreRoutingProjectionAdapter` by nothing. This delivery supplies the
first genuine consumer of each. That is the substantive integration result of
this intake — a use, at a named NS consumer, of two previously unconsumed TOE
carriers, with hypotheses that match definitionally rather than by transport.

## 5. Bidirectional lineage map

```
   public OpenAI NavierStokesAndEuler corpus            DASHI Agda NS closure lane
   (Provenance/openai-ns-20260912, 2 659 files,         (Agda/DASHI/**, 5 229-file
    51 242 decls, 0 axioms, 0 native_decide)             NS closure profile)
        endpoint: forced finite-time blowup                 endpoint: regularity side,
        with bounded kinetic energy (Clay C → D)            conditional, Boolean ledgers
                  │                                                  │
                  │ no shared declaration name with the four         │ R145 flags (§4.3)
                  │ new NS terms (0 of 70); keyword overlap          │ read as claims, never
                  │ only, denoting different objects (§5.1)          │ imported as proofs
                  ▼                                                  ▼
        ── no formal edge ──                       RequestProject.NavierStokes  (delivered lane)
                                                    RateBlockGramBound  ── re-delivery, identical
                                                      ▲            ▲        to Provenance/ns_worker_result
                                       SpineRateBlockAdapter   GramConsumerFactorisation
                                                      │            │
                                     Spine.RateBlockSchur   Proposed.FibreRoutingProjectionAdapter
                                          (this corpus, byte-identical both ways)
                                                      ▲
                                            Lean/Spine.lean, Lean/Spine/AxiomAudit.lean
                                              (rollup + audit only: no prior consumer)
```

### 5.1 Against the public forced-blowup proof: no transport

Of the 70 declaration names in the four modules, **0** occur among the 51 242
declaration names of the public corpus (`NS_LATEST_LINEAGE.csv`). Keyword-level
overlap exists and is misleading: the public corpus has 115 Gram-named and
181 dyadic-named declarations, but they are the Euler Gram-inverse/Gevrey path
machinery (`EulerBoundedFieldGramInverse`, `EulerTransverseGramInverse`, …) and
the dyadic band covers of the blowup initial source
(`NavierStokes.InitialDyadicSource`, `ValidDyadicBandCover`, …) — not a Schur
test against a resolvent Gram kernel. `Schur`, `Bony`, `Besov`, `Leray`,
`enstrophy` and `BKM` occur **0** times there.

The endpoints also differ and must not be conflated: the public development
forces finite-time blowup with bounded kinetic energy (Clay alternative C, then
D by parabolic compression), whereas every DASHI NS surface — Lean and Agda —
aims at the regularity alternative and is conditional. Nothing in this tranche
narrows that gap, and nothing here should be read as evidence for either
alternative.

### 5.2 Against the DASHI Agda lane

One genuine edge, and it runs Agda → Lean: the R145 round's *informal* content
is re-proved on the Lean `ℂ³` carrier (§4.3), including one endpoint its ledger
marks unclosed. No Agda proof term is imported, no Boolean flag is treated as
evidence, and no flag was flipped — the Agda ledger in this repository is
unchanged.

### 5.3 New Agda: the Clay-carrier vacuity audit

`DASHI/Papers/NavierStokes/ClayCarrierVacuityAudit.agda` (90 lines,
postulate-free) instantiates
`NSTriadKNFeffermanPeriodicClayStatementExact.FeffermanPeriodicClayCarrier` with
the degenerate "everything holds of everything" record and exhibits an inhabitant
of `FeffermanPeriodicClayStatementB` at it. Consequence, in the donor's words and
confirmed by reading this corpus' byte-identical copy of the target module: the
in-repo "literal Fefferman periodic Clay statement" is **parametric in an
uninterpreted carrier** — smoothness, periodicity, divergence-freeness, the
momentum equation and the initial trace are all abstract `X → Set` fields — so
inhabiting it for *some* carrier is not evidence for periodic regularity, and
the in-repo end-to-end composition to it is a schematic reduction between
records. It has been copied into `Agda/DASHI/Papers/NavierStokes/` and wired
into that directory's `Everything.agda` rollup. **That wiring is not
Agda-checked here** (no Agda toolchain in this environment); it is a plain
`import` of a module whose only dependency is a byte-identical in-repo module
whose record field names were checked by hand to match.

## 6. Unresolved physical seams (exact)

1. **Truncation-uniform constant.** `gramOperatorBound_of_rateBlockMultiplicity(_ofSpine)`
   gives `A = 32·m` with `m` the dyadic rate-block multiplicity, and it is
   cancellation-free. `gramOperatorBound_fails_on_comparable_shells` shows the
   linear degradation is real: for every `N` there is an output `k`, a set of
   ≥ `N` nonzero modes of pairwise comparable length and a transverse constant
   cell family forcing every admissible `A ≥ N`; `Spine.RateBlockSchur.schur_form_ge_half_mul_multiplicity`
   is the domain-neutral counterpart. A truncation-uniform `A` must therefore
   come from cancellation *among the signed Gram entries of the physical outer
   cells* `G_p = P_k(N_p × u_{k−p})` — not from the kernel, the transversality
   or the shell geometry. §4.2 sharpens this: the needed information is provably
   not in the masses. **Open.**
2. **Comparable shells.** Not a bug to be repaired: a proved obstruction. It
   remains a distinct seam from the rate-block route and is not paid by it.
3. **R582/R584 vector class-norm budget transport.** Still impossible from
   supplied material: those Agda rounds (and the whole rounds-570–585 family)
   were named in the earlier truncated download's nested manifest but never
   delivered; this corpus' NS Closure lane tops out at Round 530 and this
   tranche adds no `NSTriadKN*` Closure module. **Blocked on re-delivery.**
4. **Outer spectator / weight spacetime seam.** No delivered Lean or Agda module
   addresses it. **Open, not attempted.**
5. **R145 intra-shell `L²` aggregation** (`round145IntraShellL2AggregationClosed
   = false`) and **Package A** (`round145PackageAClosed = false`). The new Lean
   carrier is pointwise algebra only. **Open.**
6. **Clay carrier.** Per §5.3, the in-repo literal periodic Clay target type has
   no analytic instance anywhere in this corpus; supplying one (fields
   interpreted on real function spaces) is a prerequisite for any statement
   about the Clay problem, and is not part of this tranche.
7. **Carrier refactor.** *Partly closed by this intake for the complex scalar
   Gram form*: `Spine.RateBlockSchurPi` (§4.1) supplies the `WithLp.toLp 2`
   transport from `Fin n → ℂ` with the lane's `herm`/`nsq` to
   `EuclideanSpace ℂ (Fin n)`, so the rate-block kernel is now available at the
   lane's carrier without a hand-supplied Cauchy–Schwarz. Still open: the
   **real**-Gram spine kernels (`Spine.TransverseGram`, `Spine.SchurComplement`,
   `Spine.SchurBlock`) act on `⟪·,·⟫_ℝ`, and consuming them from the NS lane
   needs a `Fin 3 → ℂ ≃ₗ EuclideanSpace ℝ (Fin 6)` transport that exists in
   neither corpus. **Partly open.**

## 7. What is not claimed

No Clay obligation is closed by this tranche and none is claimed: Package A and
the literal periodic Clay regularity target remain open. No axiom, postulate,
conditional bridge or placeholder was introduced by this intake. No build of the
*delivered* sources was run — the delivery does not request one and the NS lane
is not on this project's build surface — so every statement above about them is
a hash comparison or a source reading, explicitly labelled, and the donor's own
elaboration and `#print axioms` results are reported as its claims. The one
piece of new Lean written here, `Lean/Spine/RateBlockSchurPiCarrier.lean`, *was*
built and axiom-audited in this checkout, as was the repair of the
pre-existing misplaced-`import` error in `Lean/Spine/JMD.lean` that had been
breaking the `Spine` target. Agda was not available, so the wiring in §5.3 is
unchecked.
No physical theory-of-everything claim is made or supported, and no Yang–Mills
material was imported.
