# Navier–Stokes proof archaeology: the public OpenAI proof against the DASHI corpus

**Round date** 2026-09-12. Source-only intake, indexing, lineage map, and three
checked Lean adapters. No corpus-wide build was requested or run; the two new
Lean modules were each built individually (see §8).

---

## 0. Delivery verification, performed before anything was written

`openai-ns-lean-archaeology-tranche-20260912.tar.gz`
sha256 `d1daa3dc44edc635a705a2f5ec5bbf4d8a11ef2b361fde16837064e905222681`.

| check | result |
|---|---|
| `sha256sum -c SHA256SUMS` | **2671 / 2671 `OK`**, 0 failed, 0 missing |
| `SOURCE_MANIFEST.txt` vs extracted payload | **exact set equality**, 2669 paths, sorted `diff` empty |
| `SOURCE_MANIFEST.txt` vs `SHA256SUMS` payload lines | byte-identical after removing the two self-entries (`HANDOFF.md`, `SOURCE_MANIFEST.txt`) |
| declared source-only (`.git`, `.lake`, `.olean`, build outputs excluded) | **confirmed**: 0 such paths in the payload |
| payload file types | 2659 `.lean`, 3 `.json`, 2 `.md`, 1 `.yaml`, 1 `.toml`, `.gitignore`, `lean-toolchain`, `LICENSE` |

No delivery anomaly was found. The payload is preserved verbatim in the tree at
`Provenance/openai-ns-20260912/`, together with the donor `HANDOFF.md`,
`SOURCE_MANIFEST.txt` and `SHA256SUMS`; the checksums were re-verified *after*
copying into the tree (2671/2671 `OK` again).

### Declared provenance, carried forward verbatim

* Repository: <https://github.com/openai/NavierStokesAndEuler>
* Pinned commit: `f9e8bc5b38b6e212696e8a30e3e91517af887bbd` (2026-09-10T13:40:53Z)
* Announcement: <https://openai.com/index/navier-stokes-solution/>
* Navier–Stokes paper: <https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf>
* Euler paper: <https://cdn.openai.com/pdf/315b36cd-ec98-4023-8342-93345194ece1/euler.pdf>
* Clay problem statement: <https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf>
* Comparator reference statements adapted from Formal Conjectures:
  <https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Millenium/NavierStokes.lean>
* Handoff also pins the independently checked current `dashi_agda` master
  `4c8ebfb733f5768ce7ed61388cc5272ececd5d0d`. **This round did not receive an
  Agda payload at that commit**, so no comparison against `4c8ebfb7` could be
  made; the Agda material indexed below is the tree as it already stands
  (donor lineage `1d3cb03c…` → `a866c675…`, recorded in earlier rounds). That
  is a named gap, not a finding.

---

## 1. Index artefacts produced this round

All regenerable, idempotent, pure source analysis (no Lean or Agda kernel is
invoked by any of them):

| file | rows | content |
|---|---|---|
| `NS_OPENAI_INDEX.csv` | 2659 | one row per delivered `.lean` file: path, module, lane, sha256, lines, bytes, import/declaration counts, `sorry`/`axiom`/`native_decide` counts, `#print axioms` targets |
| `NS_OPENAI_DECLS.csv` | 51 242 | one row per top-level declaration: module, line, kind, name, namespace, fully-qualified name, modifiers |
| `NS_OPENAI_IMPORT_EDGES.csv` | 7 277 | one row per `import`, with resolution |
| `NS_OPENAI_INDEX_SUMMARY.json` | — | roll-up |
| `NS_DASHI_LEAN_DECLS.csv` | 8 607 | declarations of the 479 first-party DASHI Lean files (`Lean/Spine`, `Lean/Synthesis`, `Lean/Promoted`, `Lean/Integration`, `Lean/Cuisine`, `Lean/Proposed`, `Lean/AgdaMirror`, `Provenance/ns_worker_result`, and the four root modules) |
| `NS_AGDA_NS_LANE.csv` | 5 229 | per-file profile of `Agda/DASHI/Physics/Closure/`, recursive |
| `NS_LINEAGE_SHARED.csv` | 106 | declaration base names appearing on both the OpenAI and DASHI-Lean sides |
| `NS_LINEAGE_SUMMARY.json` | — | roll-up |

Scripts: `scripts/ns_openai_index.py`, `scripts/ns_lineage_map.py`.

---

## 2. What the delivered proof actually is

### 2.1 Shape

| | |
|---|---|
| Lean files | 2659 (`NavierStokes/` 816, `Euler/` 1839, `ComparatorChallenges/` 2, root 2) |
| Lines of Lean | 641 332 |
| Top-level declarations | 51 242 — 38 503 `theorem`, 28 `lemma`, 10 827 `def`, 899 `abbrev`, 667 `structure`, 148 `instance`, 14 `inductive`, 156 `notation` |
| `axiom` declarations | **0** |
| `native_decide` / `@[implemented_by]` | **0** |
| `sorry` tokens | **4**, all of them intentional, all of them in `ComparatorChallenges/` |
| Import edges | 7 277 — 6 105 in-tranche, 1 172 Mathlib, **0 unresolved** |
| Toolchain | `leanprover/lean4:v4.34.0-rc2`, Mathlib `v4.34.0-rc2`, Comparator `v4.34.0-rc2` |

The four `sorry`s are the Comparator *challenge placeholders*: they sit in the
copied Formal-Conjectures reference statements
(`ComparatorChallenges/NavierStokes.lean:277,284` and
`ComparatorChallenges/Euler.lean:88,184`), which the challenge protocol requires
to be unproved. The file header says so explicitly. The proof modules
(`NavierStokes/**`, `Euler/**`) contain **zero** `sorry`. This matches the
repository's own `formalization.yaml` (`sorry_count: 0`).

Only two modules carry `#print axioms`: `NavierStokes.ComparatorSolution` and
`Euler.Solution`. `formalization.yaml` declares the permitted axiom set for all
four headline results as `propext`, `Classical.choice`, `Quot.sound`.

### 2.2 The four endpoints, and their exact statements

| # | declaration | module | endpoint |
|---|---|---|---|
| C | `NavierStokes.Comparator.navier_stokes_breakdown_R3` | `NavierStokes.ComparatorSolution` | whole space ℝ³ |
| D | `NavierStokes.Comparator.navier_stokes_breakdown_periodic` | `NavierStokes.ComparatorSolution` | torus ℝ³/ℤ³ |
| E1 | `Euler.euler_breakdown_R3` | `Euler.Solution` | whole space ℝ³, unforced |
| E2 | `Euler.exists_compact_smooth_euler_singularity` | `Euler.Solution` | whole space ℝ³, unforced, quantitative |

Endpoint (C), verbatim:

```lean
theorem navier_stokes_breakdown_R3 (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p)
```

The solution notion `NavierStokesExistenceAndSmoothnessRn`
(`NavierStokes/ComparatorDefinitions.lean`) is a `structure` requiring: the PDE
pointwise for all `t ≥ 0` with `derivWithin` in time and `fderiv`/`gradient`/`Δ`
in space; `∇⬝ v = 0`; `v(·,0) = u₀`; `v` and `p` in `ContDiffOn ℝ ∞` on
`univ ×ˢ Ici 0`; `MemLp (‖v · t‖) 2` for each `t ≥ 0`; and
`∃ E, ∀ t ≥ 0, (∫ x, ‖v x t‖²) < E` — **uniformly bounded kinetic energy**.
`InitialVelocityConditionDecay` is smooth + divergence-free + all-order
polynomial decay; `ForceConditionDecay` is smooth on `univ ×ˢ Ici 0` + all-order
space-time polynomial decay.

### 2.3 The derivation chain of (C) and (D)

```
NavierStokes.Comparator.navier_stokes_breakdown_R3          NavierStokes/ComparatorSolution.lean:17
└─ NavierStokes.ComparatorBridge.navier_stokes_breakdown_R3 NavierStokes/ComparatorR3Theorem.lean:38
   ├─ NavierStokesR3.theorem_1_1                            NavierStokes/R3/Theorem.lean:46
   │  └─ NavierStokesR3.theorem_1_1_with_initial_rest       NavierStokes/R3/Theorem.lean:25
   │     ├─ NavierStokesR3.ActualCandidate
   │     │    .selected_candidate_one_with_initial_rest     NavierStokes/R3/ActualCandidate.lean:143
   │     └─ NavierStokesR3.ViscosityScaling
   │          .candidate_at_viscosity                       NavierStokes/R3/ViscosityScaling.lean:172
   └─ NavierStokesR3.comparator_of_breakdown                NavierStokes/R3/ComparatorBridge.lean:77

NavierStokes.Comparator.navier_stokes_breakdown_periodic    NavierStokes/ComparatorSolution.lean:25
└─ NavierStokes.ComparatorBridge
     .navier_stokes_breakdown_periodic                      NavierStokes/ComparatorTheorem.lean:47
   ├─ NavierStokes.PeriodicPaper.periodic_corollary         NavierStokes/PeriodicPaperTheorem.lean:155
   │  ├─ NavierStokesR3.theorem_1_1_with_initial_rest       (shared with (C))
   │  ├─ NavierStokesR3.ParabolicScaling.compressedCandidate NavierStokes/R3/ParabolicScaling.lean:95
   │  └─ NavierStokes.PeriodicPaper.of_compact_candidate    NavierStokes/PeriodicPaperTheorem.lean:92
   └─ NavierStokes.ComparatorBridge
        .option_D_of_paper_candidate                        NavierStokes/PeriodicPaperComparator.lean:45
```

So (D) is *derived from* (C)'s whole-space construction by parabolic compression
and periodisation — a single construction serves both alternatives. The
transitive in-tranche import closure of `NavierStokes.ComparatorSolution` is
**609 modules**; of `Euler.Solution`, **1829 modules**.

The Euler chain, for completeness:

```
Euler.euler_breakdown_R3                                    Euler/Solution.lean:34
└─ Euler.initialDatum_no_global_solution                    Euler/Solution.lean:25 (private)
   ├─ Euler.ComparatorBridge
   │    .finiteLifespan_contradiction_of_compact_vorticity  Euler/CompactVorticityContradiction.lean:18
   └─ EulerPacketInduction.{initialDatum, lifespan,
        canonicalVorticityBall, …}                          Euler/PacketFiniteLifespan.lean
Euler.exists_compact_smooth_euler_singularity               Euler/Solution.lean:47
└─ Euler.ComparatorBridge.maximal_sobolevSolution           Euler/ComparatorMaximalSolution.lean:82
   + maximalVelocityExtension_{bounded_energy, c1_limsup,
     vorticity_integral, c1_locally_bounded, …}
```

### 2.4 The proof's own vocabulary

The construction is a **packet/cylinder recursion in Gevrey classes**. The
largest modules are `Euler.EulerProof` (20 755 lines, 1239 declarations),
`NavierStokes.CorrectionStep` (9 849), `NavierStokes.CorrectionInitialization`
(5 562). Dominant namespaces: `EulerOrdinarySobolev`, `NavierStokes.CorrectionStep`,
`EulerPacketTerminalDatum`, `EulerPacketCylinderField`, `EulerPacketInduction.Stage`.

A keyword sweep of all 51 242 declaration names for the DASHI NS lane's own
vocabulary returns:

| term | occurrences in the OpenAI proof |
|---|---|
| `Schur` | **0** |
| `Galerkin` | **0** |
| `Bony`, `paraproduct`, `Besov`, `Littlewood` | **0** |
| `Leray` | **0** |
| `enstrophy` | **0** |
| `BKM` / `BealeKatoMajda` | **0** |
| `helicity`, `trit` | **0** |
| `vorticity` | 94 (Euler lane only) |
| `Gronwall` / `gronwall` | **14** |

This single positive row is the whole of the vocabulary overlap, and §5 shows it
is a genuine one.

---

## 3. Scope discipline: what the public result is *not*

| axis | OpenAI `f9e8bc5b` | DASHI Lean `NavierStokesClosure` | DASHI Lean `ClayNS.RateBlocks` | DASHI Agda NS closure lane |
|---|---|---|---|---|
| **claim direction** | finite-time **blowup** | **global regularity** (conditional) | measurement of an obstruction to global regularity | global regularity (Clay A/B), never promoted |
| **Clay alternative** | (C) and (D) | (A)/(B) shaped | (B) shaped | (B), "literal periodic Clay target" |
| **domain** | ℝ³ and ℝ³/ℤ³ | abstract scalar `ℝ → ℝ` | periodic Galerkin lattice `Z³` | periodic Galerkin lattice `Z³`, exact rational carrier |
| **forcing** | smooth, compactly supported in time, all-order decaying force; **zero initial datum** | none (forcing never appears) | none explicit | none explicit |
| **solution notion** | pointwise-smooth `ContDiffOn ℝ ∞` classical solution with uniformly bounded kinetic energy (Fefferman conditions 1–7, 8–11) | none — `Z`, `Y`, `w` are abstract scalars | finite Galerkin truncation of Fourier modes | finite Galerkin truncation, `Complex3` over ℚ |
| **theorem consumer** | Comparator challenge `ComparatorChallenges/NavierStokes.json` | `ns4_global_regularity`, itself hypothetical (`bkm : IntegrableOn … → GlobalRegular`) | `spacetime_remainder_le_critical_of_gramBound` (not shipped) | `NSFinalStateReceipt`, `Papers.NavierStokes.TheoremInterface` — all Boolean status surfaces pinned `false` |
| **unconditional?** | **yes**, for every `ν > 0` | **no**: `Z' ≤ -2αZ` is an assumed physical input, and BKM is a named hypothesis | **no**: the Gram bound is exactly the hypothesis being measured | **no** |

> **The DASHI corpus did not contain the public proof, and contains nothing that
> implies it.** No DASHI declaration, in Lean or Agda, states finite-time blowup
> for Navier–Stokes or Euler, with or without forcing. The entire historical
> DASHI Navier–Stokes programme is aimed at the opposite Clay alternative. The
> two bodies of work share exactly one proved mathematical carrier (§5) and one
> unproved-clause donation opportunity (§6); everything else is disjoint.

---

## 4. Chronological archaeology of the DASHI side

Dates below are those recorded in the corpus's own provenance documents; file
`mtime`s in this checkout are all the checkout date and carry no information.

### 4.1 Archived historical DASHI Lean — the enstrophy/BKM chain

`Lean/NavierStokesClosure.lean`, sha256 `5cff4214…`, 137 lines, Mathlib-only,
namespace `NavierStokesClosure`. Three byte-identical copies exist in the tree
(`Lean/NavierStokesClosure.lean`,
`Lean/DASHI/Klüver’s Form Constants_aristotle/NavierStokesClosure.lean`,
`Lean/DASHI/output-final_aristotle/RequestProject/NavierStokesClosure.lean`),
plus four further copies under the vendored `Lean/ImportedLeans/` provenance
corpus, all seven byte-identical (verified by `sha256sum`). It is in **no**
build target.

Four theorems, no `sorry`, no `axiom`:

* `ns1_enstrophy_passage` — `Z' ≤ -2αZ` on `t ≥ 0` ⟹ `Z t ≤ Z 0 · e^{-2αt}`.
* `ns2_vorticity_control` — same inequality for `Y ≥ 0` ⟹ `√(Y t) ≤ √(Y 0)·e^{-αt}`.
* `ns3_linfty_vorticity_control` — `w t ≤ K e^{-βt}` ⟹ `w` integrable on `(0,∞)` and `∫ w ≤ K/β`.
* `ns4_global_regularity` — `GlobalRegular` is a **`Prop` parameter** and BKM is
  the **hypothesis** `bkm : IntegrableOn w (Ioi 0) volume → GlobalRegular`.

Honest reading: these are four correct scalar-analysis lemmas about abstract
functions `ℝ → ℝ`. Nothing in the file mentions a velocity field, a Navier–Stokes
solution, a vorticity, or a viscosity: the physical interpretation lives only in
the docstrings, and both the depletion inequality and BKM enter as assumptions.
The file proves no Navier–Stokes theorem.

### 4.2 Aug-6 scalar Bony donors — located, and characterised honestly

The prompt's "Aug-6 scalar Bony donors" correspond to the two non-round-numbered
`NSBony*` modules in the Agda closure lane, which sit in the `*Boundary`
fail-closed receipt family (269 files, 145 078 lines) rather than the
round-numbered `*Exact` family:

| module | lines | top-level decls | postulates | `: Bool` ledger | `= refl` pins | holes |
|---|---|---|---|---|---|---|
| `DASHI.Physics.Closure.NSBonyParaproductA6RepairBoundary` | 712 | 57 | 1 | 18 | 38 | 0 |
| `DASHI.Physics.Closure.NSBonyLipschitzAngularPushforwardBoundary` | 933 | 86 | 1 | 29 | 71 | 0 |

Their own headers are explicit about their status. `NSBonyParaproductA6RepairBoundary`
records the corrected A6.2 route

```
ω · S(u) ω = low-frequency paraproduct
           + finite near-diagonal resonant shells
           + high-frequency subleading tail
```

and then states: *"This module is fail-closed: it records targets and blockers
only. It does not prove A6, residual depletion, local monotonicity, NS Clay, or
terminal promotion."* Both are consumed by
`DASHI.Papers.NavierStokes.TheoremInterface` and by
`NSA7ResidualDepletionGronwallBoundary`.

**There is no Bony/paraproduct/Littlewood–Paley material in DASHI Lean at all.**
A whole-tree grep of every `.lean` file for `Bony`, `paraproduct`, `Besov`,
`LittlewoodPaley` returns zero genuine hits (the only matches are the string
"carbonyl compound" in three generated Wikidata glossary modules). The scalar
Bony donors are an Agda-only, ledger-only surface.

### 4.3 The `R145 / R582 / R584` lineage

These are Agda closure-lane rounds. The lane spans rounds 4–585 across 1482
round-numbered files.

| round | module | what it actually proves |
|---|---|---|
| R145 | `NSTriadKNAntiParallelHelicitySlotKernelRound145Exact` (173 lines) | defines `slotKernel`, the anti-parallel helicity slot kernel used as the cell-valued object downstream |
| R180 | `NSTriadKNRawCurlFibreGramLedgerRound180Exact` (113 lines) | **a genuine proved identity**: `complex3NormSquared (sumCells cells) ≡ cellMassSum cells + gramDebt cells`, by induction with `complex3Polarization`; plus `nonpositiveGramDebtClosesFibre` |
| R580 | `NSTriadKNFourSignBonyClassGramCompilerRound580Exact` (211 lines) | four-sign Bony class Gram compiler; asks for four classwise signed Gram-debt bounds |
| R581 | `NSTriadKNLiteralFourSignBonyRoutingRound581Exact` (262 lines) | routes literal four-sign Bony cells |
| R582 | `NSTriadKNClassNormBudgetToBonyGramPaymentRound582Exact` (166 lines) | **a genuine proved reduction**: `cellMassSumNonnegative582` and `gramDebtBelowSummedNorm582` (`gramDebt cells ≤ ‖sumCells cells‖²`), so *any* independently proved class-norm budget `‖∑ cells‖² ≤ B` pays the R580 residual |
| R583 | `NSTriadKNDirectBonyClassNormCompilerRound583Exact` (159 lines) | the generic class-norm compiler `literalRoutedFourSignBound583` |
| R584 | `NSTriadKNNestedSlotBonyClassNormBidiRound584Exact` (146 lines, 23 imports) | **the BIDI round**: instantiates R581/R583 on the *literal* R573 nested outer slot, proving `nestedSlotFoldIsLiteralFold584 = refl` and `nestedSlotFoldBelowClassNorms584` |
| R585 | `NSTriadKNFourSignInnerBonyLHHLNormSymmetryRound585Exact` (175 lines) | LH/HL norm symmetry for the four-sign inner |

R584's own status ledger is the honest frontier statement for this lineage:

```agda
round584LiveR573NestedSlotBidiClosed                        = true
round584UsesOlderRawCurlClassAsSameObject                   = false
round584AnyLiveNestedSlotClassNormPaymentConstructed        = false   -- ← no payment exists
round584OuterWeightAndSpectatorSpacetimeClosed              = false
round584ClayPromotion                                       = false
round584CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
```

So R584 proves a *conditional*: given a `NestedSlotClassNormPayment584` record
— whose only field is a four-tuple of class-norm budgets — the nested slot fold
is bounded. **No inhabitant of that record is constructed anywhere in the lane.**
R580–R585 are all stated over the exact rational `Complex3` carrier, and R584
says so explicitly: *"this BIDI is deliberately rational too; it does not pretend
to be scalar-generic."*

### 4.4 The exact remaining Agda obligation (Round 504)

`NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact` names the lane's terminal
cutset as **two leaves**, and pins the current status at `false, false`:

* **Leaf A** — literal R406 signed-cross payment (same-object integrated receipt
  plus cutoff-uniform upper bound). Mechanism: `ThinkSignedSameScaleSpacetime`.
* **Leaf B** — literal R406 phase-sensitive critical-production slice plus a
  cutoff-uniform initial critical ceiling. Mechanism:
  `ThinkPhaseSensitiveCriticalProduction`.

with `round504ClayPromotion = false` proved by `refl`. Full R439 companion
equality, Laplace factorisation, Cauchy PSD, Schur majorisation and R284
decomposition are explicitly *rejected as mandatory* (`hypothesisInflation`).

The paper-facing surface agrees: `DASHI.Papers.NavierStokes.ClayContractRound23`
has `physicalProducersInhabited = false` and
`unconditionalClayTheoremPromoted = false`, both pinned by `refl`.

### 4.5 2026-09-09 — the Agda NS tranche intake, and the Lean worker result

`Provenance/ns_worker_result/docs/ns-clay-contract/source-tranche-audit.md`
records that an announced R423 Agda bundle was initially absent and was later
re-sent as `ns-agda-tranche-20260909.tar.gz`.

The Lean side of that round produced
`Provenance/ns_worker_result/RequestProject/NavierStokes/RateBlockGramBound.lean`
(sha256 `e1f74452…`, 37 647 bytes, namespace `ClayNS.RateBlocks`). This is the
strongest genuine Lean mathematics in the historical DASHI NS lane:

* `gramOperatorBound_of_rateBlockMultiplicity` — **positive**: if each dyadic
  rate block `λ_p ∈ [4^b, 4^{b+1})` carries at most `m` retained modes, the
  Gram-operator bound holds with `A = 32m`, cancellation-free, for every cell
  family. Proof: a Schur test against the Cauchy kernel `1/(λ_p+λ_q)`, with
  `amgm_block` and `sum_half_pow_natAbs_le`.
* `gramOperatorBound_fails_on_comparable_shells` — **negative and sharp**: for
  every `N` there is a retained output, `N` pairwise-comparable nonzero modes,
  and a transverse cell family forcing `A ≥ N`.
* `nsq_sum_eq_sum_sum_herm_re` — `‖∑_p G_p‖² = ∑_{p,q} Re⟪G_p,G_q⟫`.
* `gramOperatorBound_of_cluster_cancellation` and its converse
  `cluster_cancellation_of_gramOperatorBound`.

Its accompanying note is explicit: *"Package A and the literal periodic Clay
regularity target are **not** closed and nothing is claimed for them."*

**Named gap, unchanged this round:** the file opens with
`import RequestProject.NavierStokes.TransverseFrameSplit`, and no handoff has
ever shipped that module. The file is therefore **not buildable in this
checkout** and is not in any build target. Its mathematical core was extracted,
domain-neutrally and independently, into `Lean/Spine/RateBlockSchur.lean`
(sha256 `f24f666e…`, `Spine.RateBlockSchur.schur_form_le_blockMultiplicity` and
the matching lower bound `schur_form_ge_half_mul_multiplicity`).

### 4.6 2026-09-10 / 2026-09-11 — spine consolidation and delta overlay

Recorded in `SPINE_CONSOLIDATION_20260910.md` and `DELTA_20260911_OVERLAY.md`.
Neither touched NS material.

### 4.7 2026-09-10 — the public construction

Upstream commit `f9e8bc5b`, dated 2026-09-10T13:40:53Z — i.e. **the same day as
the spine consolidation round, and two days before this intake**. There is no
derivation relationship in either direction: the DASHI corpus is not cited by
the upstream repository, and no upstream declaration appears in the DASHI tree
before this round's intake.

---

## 5. Common carriers actually found, and the adapters built

Name-level cross-reference (`NS_LINEAGE_SHARED.csv`): of 51 242 upstream and
8 607 DASHI-Lean declaration names, **106** base names coincide, and on
inspection all but the Grönwall family are generic English words
(`zero`, `step`, `value`, `support`, `shift`, `weight`, `reflect`, …) or
independent coincidences (`quadraticMap_hasFDerivAt`, `variance_nonneg`). There
is no accidental duplication of infrastructure between the two.

### Carrier 1 — the integrating-factor comparison lemma  ✅ real, bidirectional

`Lean/Spine/GronwallComparison.lean` (new, builds, `sorry`-free, axioms
`propext`/`Classical.choice`/`Quot.sound` only).

**The carrier.**
`Spine.GronwallComparison.homogeneous_antitoneOn`: if `E` is continuous on
`Icc 0 T`, differentiable on `Ioo 0 T` with `E' t ≤ K · E t` there, then
`t ↦ exp(-K t) · E t` is `AntitoneOn (Icc 0 T)`. No sign condition on `K`.
`affine_antitoneOn` adds `0 ≤ K`, `0 ≤ ε` and the perturbed bound
`E' t ≤ K·E t + ε`, making `t ↦ exp(-K t)·E t − ε·t` antitone.

Both are stated with derivatives on the *open* interval only, which is the
weaker of the two consumers' hypothesis sets, so each consumer's hypotheses
genuinely discharge the carrier's.

**Consumer A — OpenAI direction.**
`Spine.GronwallComparison.openai_comparison_gronwall` has, modulo the
declaration name, a **character-identical signature** to
`NavierStokesR3.ComparisonGronwall.exp_neg_mul_le_of_deriv_le`
(`NavierStokes/R3/ComparisonGronwall.lean`, lines 24–31 of the preserved donor).
The comparison was performed mechanically against the preserved source, with
whitespace normalised; the only difference is the identifier.

**The whole on-path chain is factored, not just the first link.** Exactly two
modules in the tranche import `NavierStokes.R3.ComparisonGronwall`:
`NavierStokes/R3/WholeSpaceEnergyLimit.lean` (which uses
`le_div_radius_of_deriv_le` at line 88) and `NavierStokes/R3/H3Energy.lean`
(which uses `le_exp_mul_of_deriv_le` at line 112). Of those, only
`WholeSpaceEnergyLimit` lies in the 609-module import closure of
`NavierStokes.ComparatorSolution` — via `NavierStokes.R3.WholeSpaceComparisonClosure`.
So the single on-path external consumer of the Gronwall module is
`le_div_radius_of_deriv_le`, and the internal chain reaching it is

```
exp_neg_mul_le_of_deriv_le → le_exp_mul_of_deriv_le
  → le_uniform_exp_mul_of_deriv_le → le_div_radius_of_deriv_le
```

All four are re-derived here from the carrier as
`openai_comparison_gronwall`, `openai_le_exp_mul_of_deriv_le`,
`openai_le_uniform_exp_mul_of_deriv_le`, `openai_le_div_radius_of_deriv_le`.
The signatures of the first and the last were checked mechanically against the
preserved donor source and are character-identical modulo the declaration name.

> **Transport, stated exactly.** This is a *restatement proved locally*, not an
> import of the upstream term. The upstream project pins Lean `v4.34.0-rc2` and
> Mathlib at that tag; this checkout pins `v4.28.0`. The upstream repository is
> not a Lake dependency here and no upstream `.olean` exists in this
> environment, so no upstream proof term is quoted, reused or relied upon. What
> is established is: *the statement the upstream proof uses at that point is
> provable from a carrier this corpus now owns.* It is **not** established that
> the upstream proof, or any part of it beyond that one lemma, has been
> reproduced.

**Consumer B — DASHI Lean direction.**
`Spine.GronwallComparison.dashi_ns1_enstrophy_passage` is the statement of
`NavierStokesClosure.ns1_enstrophy_passage`, re-derived from the homogeneous
carrier with `K := -2α`. `dashi_ns2_vorticity_control` is `ns2` re-derived from
it in turn. This is the genuine factorisation: the historical DASHI consumer's
own hypotheses (global differentiability, inequality for `t ≥ 0`) are strictly
stronger than the carrier's.

The homogeneous carrier is stated without a sign condition on `K` **because**
consumer B needs `K = -2α` with no sign information on `α`; the affine carrier
needs `0 ≤ K` **because** consumer A's `ε`-absorption step requires
`exp(-Kt) ≤ 1` for `t ≥ 0`. Neither consumer's form implies the other.

### Carrier 2 — the Gram ledger  ✅ real, Agda ↔ DASHI-Lean only

`Lean/Spine/GramLedger.lean` (new, builds, `sorry`-free, same axiom set).

Three places state the same finite fact:

| presentation | where |
|---|---|
| list recursion over the exact rational `Complex3` carrier | Agda `…RawCurlFibreGramLedgerRound180Exact` (sha256 `387dbca2…`): `‖sumCells cells‖² ≡ cellMassSum cells + gramDebt cells` |
| the same, plus `0 ≤ cellMassSum` hence `gramDebt ≤ ‖sumCells‖²` | Agda `…ClassNormBudgetToBonyGramPaymentRound582Exact` (sha256 `f0afd58f…`) |
| `Finset` double sum over the Galerkin mode set | DASHI Lean `ClayNS.RateBlocks.nsq_sum_eq_sum_sum_herm_re`: `‖∑_p G_p‖² = ∑_{p,q} Re⟪G_p,G_q⟫` |

The new module proves both presentations over an **arbitrary real inner-product
space** —
`sq_norm_sum_eq_massSum_add_gramDebt`, `gramDebt_le_sq_norm_sum`,
`sq_norm_sum_le_massSum_of_gramDebt_nonpos`, `sq_norm_sum_eq_double_sum` —
with `massSum` and `gramDebt` defined by exactly the Agda recursion, and then
the **carrier equality**

```lean
theorem ofFn_massSum_add_gramDebt_eq_double_sum {n : ℕ} (G : Fin n → V) :
    massSum (List.ofFn G) + gramDebt (List.ofFn G) = ∑ p, ∑ q, (inner ℝ (G p) (G q) : ℝ)
```

identifying the two presentations as the same real number. This is the
bidirectional adapter: the Agda and DASHI-Lean statements are not merely
similar, they are the same statement, and the Lean one is strictly more general
(arbitrary real inner-product space rather than `Complex3` over ℚ).

> **Scope.** The OpenAI proof has **no** consumer of this carrier. Its 2659
> modules contain no Schur test, no Galerkin truncation, no Bony decomposition
> and no Gram ledger of this shape. Carrier 2 is a DASHI-internal Agda↔Lean
> bridge, and bears on neither blowup nor global regularity.

---

## 6. One donation, honestly labelled as such

`Spine.GronwallComparison.agda_a7_residual_depletion_comparison`.

`DASHI.Physics.Closure.NSA7ResidualDepletionGronwallBoundary` (sha256
`fb6b62b1…`, 589 lines) is a fail-closed Agda receipt whose `A7GronwallClause`
is a **14-constructor enumeration** of the steps the intended residual-depletion
argument would need — it proves none of them, and its own header says it
*"proves no A8 local monotonicity, no A9 CKN/BKM closure, no Navier-Stokes Clay
result, and no terminal promotion."* One constructor,
`gronwallComparisonForZPrimeWithPositiveSlope`, names the scalar comparison
`Z' ≥ αβ Z − αC` used there to drive `D_r → 0`.

That clause is the reflection of the affine carrier: applying
`affine_antitoneOn` to `−Z` discharges it, giving
`(Z 0 − ε t)·exp(K t) ≤ Z t` with `K := αβ`, `ε := αC`. The Lean theorem is
proved and checked.

This is **not** a factorisation of an existing consumer chain, and it is not
reported as one: nothing in Agda consumes the statement, the Agda clause remains
a data constructor, and the surrounding A6 assembly / A8 monotonicity / A9
CKN–BKM steps are entirely untouched. It is a one-directional donation of a
scalar lemma into a lane that had named it as an obligation.

---

## 7. Divergences retained, not overwritten

Nothing in the existing tree was modified this round. In particular:

* `Lean/NavierStokesClosure.lean` and its six copies are untouched; the new
  Spine module *restates* `ns1`/`ns2` rather than editing or replacing them, so
  both the original and the carrier-derived version remain readable side by side.
* `Provenance/ns_worker_result/RequestProject/NavierStokes/RateBlockGramBound.lean`
  is untouched, still unbuildable, and its missing import
  `RequestProject.NavierStokes.TransverseFrameSplit` is still recorded as absent.
* `Lean/Spine/RateBlockSchur.lean` already owns the Schur kernel
  domain-neutrally; `Lean/Spine/GramLedger.lean` deliberately does **not**
  duplicate it and owns the complementary ledger identity instead.
* No Agda file was edited. The `false`-pinned Boolean status ledgers
  (`round584ClayPromotion`, `round504ClayPromotion`,
  `unconditionalClayTheoremPromoted`, `physicalProducersInhabited`) are left
  exactly as they are; nothing this round changes any of them, and nothing
  should be read as changing them.
* The whole upstream payload is preserved verbatim with its manifest and sums,
  not merged into the DASHI namespace.

---

## 8. Build status

No corpus-wide build was requested, and none was run to completion. The two new
modules were each built individually with the project toolchain
(`leanprover/lean4:v4.28.0`, Mathlib `v4.28.0`):

```
lake build Spine.GronwallComparison   ✔ Built (8026 jobs)
lake build Spine.GramLedger           ✔ Built (8026 jobs)
```

Both contain zero `sorry`, zero `admit`, zero `axiom` declarations, zero
`native_decide`, zero `@[implemented_by]`. Every headline theorem in them was
checked with `#print axioms` and depends on exactly
`[propext, Classical.choice, Quot.sound]` — the same set the upstream project
declares for its four endpoints.

Both files land inside the existing `Spine` library glob (`Spine`, `Spine.*`),
so they are now build targets of this project.

**No Agda kernel exists in this environment.** Every Agda statement quoted above
is read from source and is *not* kernel-checked here; the Agda claims are
resolution-checked against the corpus index only.

---

## 9. Frontier: exact remaining obligations

### 9.1 Upstream (`f9e8bc5b`)

Nothing is outstanding in the delivered artefact itself: 0 `sorry` in the proof
modules, 0 axioms, 0 unresolved imports, and its own `formalization.yaml`
declares `review.status: self-assessed`. What this round did **not** do, and
does not claim:

* it did not elaborate a single upstream module (wrong toolchain; 641 332 lines
  of Lean against a Mathlib pinned two minor versions ahead of this checkout);
* it therefore has **no kernel receipt** for any upstream theorem, and asserts
  none. The `sorry`- and axiom-counts above are *source-level* counts;
* the Comparator verification (`lake exe comparator …`, `landrun` / `lean4export`
  / `nanoda_bin`) was not run.

### 9.2 DASHI Agda NS lane

Profile of `Agda/DASHI/Physics/Closure/` (recursive, 8 subdirectories): 5229
files, 1 484 251 lines, 77 534 top-level declarations, **71 postulates**,
**2 holes**, 31 638 `: Bool` ledger declarations and 55 988 `= refl` pins.

Exact terminal cutset, from R504, unchanged:

* **Leaf A** — literal R406 signed-cross payment: same-object integrated receipt
  plus cutoff-uniform upper bound. `round504SignedCrossPaymentClosed = false`.
* **Leaf B** — literal R406 phase-sensitive critical-production slice plus
  cutoff-uniform initial critical ceiling.
  `round504CriticalProductionSliceClosed = false`.

Plus, from R584: no inhabitant of `NestedSlotClassNormPayment584` is constructed
(`round584AnyLiveNestedSlotClassNormPaymentConstructed = false`), and the outer
weight / spectator spacetime is not closed
(`round584OuterWeightAndSpectatorSpacetimeClosed = false`).

Plus, from R582's own framing: the R580 Gram residual is paid by *any* proved
class-norm budget `‖∑ cells‖² ≤ B`, and **no such budget is proved anywhere in
the lane**. Carrier 2 now makes that reduction available in Lean over an
arbitrary real inner-product space, but produces no budget either.

### 9.3 DASHI Lean NS lane

* `NavierStokesClosure.ns4_global_regularity` is conditional on two named
  hypotheses (`Z' ≤ -2αZ`; BKM as `IntegrableOn … → GlobalRegular`) and on
  `GlobalRegular` being an uninterpreted `Prop` parameter. Nothing supplies
  either. The file is in no build target.
* `ClayNS.RateBlocks` remains unbuildable for the missing
  `RequestProject.NavierStokes.TransverseFrameSplit`. Its own conclusion stands:
  the remaining obligation is square-root cancellation *inside* one dyadic rate
  block, for the aggregated cell `∑_{p ∈ cluster} P_k(N_p × u_{k−p})`, with a
  constant independent of the truncation. Nothing in this corpus supplies it.
* Neither of the two new Spine modules is a step towards either Clay direction,
  and neither is presented as one.

### 9.4 Analytic seams in the proposed connections

| connection | seam |
|---|---|
| Carrier 1 → OpenAI | statement-level only. No transport of a proof term; the upstream module is not compiled here and not depended on. A future round with the upstream toolchain could make this a literal import, which would replace a restatement by a reuse. |
| Carrier 1 → DASHI Lean | none at the scalar level: the discharge is complete. The seam is one level up — `ns1`'s hypothesis `Z' ≤ -2αZ` is the A8/A9 scale-monotone input, which is unproved in both languages. |
| Carrier 1 → Agda A7 | the Lean theorem is not an Agda term. No Agda consumer is re-pointed, and no Agda kernel ran. |
| Carrier 2 → Agda R180/R582 | same: carrier equality is proved in Lean over a general space; the Agda modules keep their own `Complex3`-over-ℚ proofs. Transporting the Lean statement into Agda, or the Agda one into Lean via a `Complex3 ℚ` instance of `InnerProductSpace ℝ`, is not done and would need a rationals-into-reals embedding lemma. |
| Carrier 2 → DASHI Lean `ClayNS` | the consumer file does not build. Re-pointing `nsq_sum_eq_sum_sum_herm_re` at `Spine.GramLedger.sq_norm_sum_eq_double_sum` is a one-line edit that cannot be validated until `TransverseFrameSplit` is delivered, so it was not made. |
| any connection → the OpenAI endpoint | **none exists.** No DASHI carrier, proved or unproved, appears in the 609-module import closure of `NavierStokes.ComparatorSolution` or the 1829-module closure of `Euler.Solution`, other than the one scalar Grönwall lemma of Carrier 1 — which is a standard integrating-factor argument and carries none of the construction. |

---

## 10. Summary of claims

**Claimed, and checked in this environment.**
Two new Lean modules build against this project's toolchain with no `sorry`, no
added axiom, and the axiom set `{propext, Classical.choice, Quot.sound}`. They
own two carriers. Three consumers are discharged from them: the upstream
Grönwall signature (as a locally proved restatement), the historical DASHI
`ns1`/`ns2`, and the scalar clause named by the Agda A7 receipt. One carrier
equality identifies the Agda list ledger with the DASHI-Lean `Finset` ledger.

**Claimed, from source analysis only.**
Every count, hash, import edge and declaration location in this document,
including the `sorry`/axiom profile of the upstream tranche and of the Agda NS
lane.

**Not claimed.**
That DASHI already had the public proof, or any part of its construction; that
any upstream theorem was verified here; that any Clay alternative is closed or
advanced in either direction; that any Agda module was kernel-checked; that the
scalar carriers carry analytic content. The corpus's own `false`-pinned Clay
promotion ledgers remain `false`, and this round gives no reason to change them.
