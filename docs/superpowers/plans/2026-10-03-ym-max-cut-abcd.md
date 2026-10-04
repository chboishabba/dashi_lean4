# Yang–Mills A–D Max-Cut Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close every theorem-bearing A–C seam that can be closed from the live source, expose any genuine finite-source RP counterexample/obligation without weakening it, and add an honest D3 projective-marginal compactness producer interface.

**Architecture:** Extend the existing literal SU(2) and CMP119 files instead of introducing parallel carriers. A gets a same-object projection/pullback theorem; B gets source-facing sector classification/certificate constructors or an explicit obstruction theorem; C gets a single additive source dictionary feeding the existing dyadic weld; D gets finite-marginal extraction/consistency infrastructure while leaving projective-limit existence explicit unless mathlib already supplies it.

**Tech Stack:** Lean 4.28 / mathlib, existing `YMContinuum` library, GitHub Actions exact-branch workflow.

**Spec:** `docs/superpowers/specs/2026-10-03-ym-max-cut-abcd-design.md`

## Global Constraints

- Reuse the literal selected Wilson/CMP119 carriers; no surrogate measure or action family.
- Fixed-boundary Wilson positivity is forbidden by the existing no-go witness; boundary Haar projection is mandatory.
- Residual smallness never implies RP.
- Vacuum remains a constant reflected-half factor.
- Existing dyadic localization/oscillation consumers are reused rather than duplicated.
- D3 must not claim a projective-limit continuum measure without an actual theorem producing it.

## Review Focus

- Upper and lower periodic crossing slabs must use the same literal link field and reflection convention.
- Boundary-Haar averaging must not silently condition on a fixed boundary.
- E/R/B certificates must preserve source crossing polymers rather than relabel one-sided terms.
- The C dictionary must evaluate every sector on one configuration/cutoff/evaluator and preserve additive semantics.
- D3 consistency maps must compose in the stated direction and limits must remain actual `ProbabilityMeasure` objects.

---

### Task 1: Block A projected Wilson RP bridge

**Files:**
- Create: `YangMills/LiteralSU2BoundaryGaugeProjectionRP.lean`
- Create: `YangMills/LiteralSU2BoundaryGaugeProjectionRPTest.lean`
- Modify: `YangMills/YMClayMaxCut20261002.lean`

**Interfaces:**
- Consumes: `literalSU2BoundaryGaugeProjectedWilsonKernel`, literal sector Haar split, crossing-slab partition, literal half-path Wilson kernel identity, `su2_wilson_crossing_plane_integral_rp`.
- Produces: a theorem whose conclusion is `LiteralSU2BoundaryGaugeProjectionRPExact`, or a minimal named same-object pullback equality whose only remaining consumer is the generic integral RP theorem.

- [ ] **Step 1: Write the failing test** importing `LiteralSU2BoundaryGaugeProjectionRP` and asserting that the new terminal theorem has type `LiteralSU2BoundaryGaugeProjectionRPExact`.
- [ ] **Step 2: Push the test-only commit and confirm the exact-branch `YM Continuum Lean` workflow fails because the production theorem/file is absent.**
- [ ] **Step 3: Implement the minimal same-object bridge.** Prefer an outright proof; if a source equality is genuinely absent, expose exactly that equality as a proposition/structure and prove the terminal compiler from it without calling the block closed.
- [ ] **Step 4: Run exact-branch CI and require the focused test plus `YMContinuum` build to pass.**
- [ ] **Step 5: Wire the result into `YMClayMaxCut20261002.lean` with naming that distinguishes closed theorem from remaining physical producer.**

### Task 2: Block B source polymer reflection audit

**Files:**
- Create: `YangMills/CMP119PolymerReflectionAudit.lean`
- Create: `YangMills/CMP119PolymerReflectionAuditTest.lean`
- Modify: `YangMills/CMP119ResidualReflectionCut.lean`
- Modify: `YangMills/YMClayMaxCut20261002.lean`

**Interfaces:**
- Consumes: `CMP119ResidualSector`, `CMP119SectorReflectionCertificate`, source periodic-polymer support data already present in the repository.
- Produces: literal four-way placement classifier (`positive`, `negative`, `crossing`, `empty`) for source polymers; reflected-half constructor for one-sided sectors; crossing-kernel certificate constructor requiring actual PSD; and a theorem reducing complete finite RP to the E/R/B crossing PSD leaves.

- [ ] **Step 1: Write tests for classifier exhaustiveness/disjointness and for the reduction theorem naming all three crossing leaves.**
- [ ] **Step 2: Push test-only commit and confirm expected RED.**
- [ ] **Step 3: Implement classifier and certificate constructors using existing periodic time-plane predicates/dictionaries. If the source carrier is not yet physically connected, encode the dictionary as an explicit structure with no theorem claiming it exists.**
- [ ] **Step 4: Add a falsification theorem: any exhibited test vector with negative crossing quadratic form rules out a `crossKernel` certificate for that source kernel.**
- [ ] **Step 5: Require exact-branch CI green.**

### Task 3: Block C additive same-object source weld

**Files:**
- Create: `YangMills/CMP119LiteralResidualSourceDictionary.lean`
- Create: `YangMills/CMP119LiteralResidualSourceDictionaryTest.lean`
- Modify: `YangMills/CMP119LiteralDyadicResidualWeld.lean`
- Modify: `YangMills/YMClayMaxCut20261002.lean`

**Interfaces:**
- Consumes: `su2FullResidual`, `finiteLocalizedResidualTail`, existing dyadic shell majorant and source shell bounds.
- Produces: one structure containing E/R/B/V source evaluators, common shell embedding, additive evaluator semantics, source-to-periodic carrier equalities, and a constructor of `CMP119LiteralDyadicResidualWeld` from the exact source identity.

- [ ] **Step 1: Write a test that constructs the dyadic weld from the new dictionary and exact localized-tail equality.**
- [ ] **Step 2: Push test-only commit and confirm expected RED.**
- [ ] **Step 3: Implement the dictionary with each unresolved physical source identification as a separately named field; prove the additive residual equality and the weld constructor.**
- [ ] **Step 4: Prove downstream interval/normalized-expectation results are inherited directly from the existing weld without duplicate localization logic.**
- [ ] **Step 5: Require exact-branch CI green.**

### Task 4: Block D3 finite-marginal compactness producer

**Files:**
- Create: `YangMills/ProjectiveMarginalTightness.lean`
- Create: `YangMills/ProjectiveMarginalTightnessTest.lean`
- Modify: `YangMills/ContinuumProkhorov.lean`
- Modify: `YangMills/YMClayMaxCut20261002.lean`

**Interfaces:**
- Consumes: `exists_weakly_convergent_subsequence_of_tight`, actual `ProbabilityMeasure` marginals, continuous/measurable projection maps.
- Produces: per-marginal tightness/extraction package, preservation of pushforward consistency under weak limits when continuity hypotheses are supplied, and an explicit `ProjectiveLimitExistenceObligation` for the remaining global measure theorem.

- [ ] **Step 1: Write tests for marginal subsequence extraction and limit consistency under continuous pushforward.**
- [ ] **Step 2: Push test-only commit and confirm expected RED.**
- [ ] **Step 3: Implement the finite-marginal package and diagonal-compatible interfaces using existing probability-measure topology theorems.**
- [ ] **Step 4: Add the named projective-limit obligation rather than postulating a continuum measure.**
- [ ] **Step 5: Require exact-branch CI green and run the finite Python diagnostics already in the workflow.**

### Task 5: Frontier integration and audit

**Files:**
- Modify: `YangMills/YMClayMaxCut20261002.lean`

**Interfaces:**
- Consumes: Tasks 1–4.
- Produces: one theorem-bearing status surface distinguishing CLOSED compilers/results from OPEN physical producers.

- [ ] **Step 1: Add compile-time status theorems/abbreviations for A, B, C, and D3.**
- [ ] **Step 2: Confirm no theorem name or docstring states that complete-action RP, the literal CMP119 source weld, projective-limit existence, continuum OS QFT, clustering, spectral completeness, or the mass gap is closed unless the corresponding producer theorem now exists.**
- [ ] **Step 3: Run exact-branch CI at the final head and record the result.**
