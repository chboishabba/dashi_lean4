# OpenAI Math Corpus Integration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Pin OpenAI's mathematics corpus as a hermetic, attributed theorem source and expose safe Lean/Agda ingress layers plus an initial DASHI relevance atlas.

**Architecture:** Keep `openai/math` at immutable commit `1581d4cbdd69a0faf34b2089614fe2a814316a6a` outside DASHI's normal Lean dependency graph. Add proof-status and authority firewalls in Lean, mirror them as cross-prover source receipts in Agda, and route likely useful mathematics into existing DASHI programmes without claiming same-object theorem promotion.

**Tech Stack:** Lean 4, Agda, Git/GitHub, YAML metadata, Apache-2.0 provenance.

**Spec:** `docs/superpowers/specs/2026-10-16-openai-math-corpus-design.md`

## Global Constraints

- Upstream repository is exactly `openai/math` at commit `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
- Upstream Lean toolchain is exactly `leanprover/lean4:v4.34.1`.
- Do not retarget DASHI's Lean toolchain or mathlib to the upstream environment.
- Preserve Apache-2.0 attribution and distinguish upstream work from DASHI synthesis.
- Manuscript, catalogue, upstream declaration, upstream kernel receipt, DASHI port, DASHI kernel receipt and Agda theorem status remain distinct.
- No CI/kernel-green claim is made without execution evidence.

## Review Focus

- Upstream `main` moving must not alter the pinned receipt.
- A catalogue entry without a declaration/kernel receipt must not be promoted.
- A Lean theorem receipt must not become an Agda theorem by metadata alone.
- A research-topic match must not become same-object theorem transport.
- The vendor helper must reject or visibly expose a checkout whose HEAD differs from the declared pin.

---

### Task 1: Lean source-level regression contract

**Files:**
- Create: `Integration/OpenAIMath/OpenAIMathCorpusRegression.lean`

**Interfaces:**
- Consumes: future `Integration.OpenAIMath.Everything`.
- Produces: compile-time assertions for pin, toolchain, authority firewall and relevance classes.

- [ ] **Step 1:** Create the regression owner importing `Integration.OpenAIMath.Everything` and asserting exact pin/toolchain values plus non-promotion booleans.
- [ ] **Step 2:** Verify RED by confirming the production rollup does not yet exist.
- [ ] **Step 3:** Commit the regression owner.

### Task 2: Lean upstream pin and status model

**Files:**
- Create: `Integration/OpenAIMath/UpstreamPin.lean`
- Create: `Integration/OpenAIMath/FormalizationStatus.lean`

**Interfaces:**
- Produces: `upstreamCommit`, `upstreamLeanToolchain`, `UpstreamAuthorityLevel`, `PromotionStatus`, and firewall theorems/booleans consumed by Tasks 3-5.

- [ ] **Step 1:** Implement immutable upstream metadata and license/toolchain/catalogue paths.
- [ ] **Step 2:** Implement distinct upstream/DASHI promotion-status constructors with no automatic promotion function.
- [ ] **Step 3:** Add explicit negative/inequality-style firewall facts consumed by regression.
- [ ] **Step 4:** Commit.

### Task 3: Lean relevance atlas and vendor contract

**Files:**
- Create: `Integration/OpenAIMath/PriorityAtlas.lean`
- Create: `scripts/materialize_openai_math_vendor.sh`
- Create: `vendor/openai-math/README.md`

**Interfaces:**
- Consumes: Task 2 metadata.
- Produces: `DASHIProgramme`, `RelevanceClass`, initial priority entries, and an executable checkout contract pinned to the exact upstream SHA.

- [ ] **Step 1:** Add coarse routing classes and named DASHI programmes without theorem promotion.
- [ ] **Step 2:** Add the vendor helper that clones/fetches `openai/math`, checks out the exact pin, and fails if the resulting HEAD differs.
- [ ] **Step 3:** Add vendor README documenting hermetic upstream environment and Apache-2.0 retention.
- [ ] **Step 4:** Commit.

### Task 4: Lean focused rollup

**Files:**
- Create: `Integration/OpenAIMath/Everything.lean`

**Interfaces:**
- Consumes: Tasks 2-3.
- Produces: one import target for regression and downstream theorem-specific adapters.

- [ ] **Step 1:** Export the pin, status and atlas modules.
- [ ] **Step 2:** Source-audit the regression contract against the exported names.
- [ ] **Step 3:** Commit.

### Task 5: Agda source-level regression contract

**Files:**
- Create: `DASHI/Research/OpenAIMath/OpenAIMathCorpusRegression.agda`

**Interfaces:**
- Consumes: future `DASHI.Research.OpenAIMath.Everything`.
- Produces: exact upstream pin/status assertions and cross-kernel non-promotion assertions.

- [ ] **Step 1:** Create the regression owner first.
- [ ] **Step 2:** Verify RED by confirming the production rollup does not yet exist.
- [ ] **Step 3:** Commit.

### Task 6: Agda upstream receipt and priority atlas

**Files:**
- Create: `DASHI/Research/OpenAIMath/OpenAIMathUpstreamReceiptExact.agda`
- Create: `DASHI/Research/OpenAIMath/OpenAIMathPriorityAtlasExact.agda`
- Create: `DASHI/Research/OpenAIMath/Everything.agda`

**Interfaces:**
- Produces: immutable upstream source receipt, cross-prover status vocabulary, relevance routing and focused rollup.

- [ ] **Step 1:** Encode the exact upstream repository/SHA/toolchain/catalogue and Apache-2.0 attribution.
- [ ] **Step 2:** Encode `manuscript != upstream Lean != Agda theorem` and local promotion boundaries.
- [ ] **Step 3:** Mirror the named DASHI programme/relevance atlas without importing Lean proof authority.
- [ ] **Step 4:** Export through a focused rollup.
- [ ] **Step 5:** Commit.

### Task 7: Repository integration and PRs

**Files:**
- Modify: nearest existing Lean integration rollup if one canonical root is present and safe.
- Modify: nearest existing Agda research/global rollup if one canonical root is present and safe.

**Interfaces:**
- Consumes: all previous tasks.
- Produces: discoverable integration branches and draft PRs with attribution/verification boundaries.

- [ ] **Step 1:** Inspect canonical rollups and add only minimal imports where appropriate.
- [ ] **Step 2:** Re-read changed source for exact pin consistency and absence of automatic promotion.
- [ ] **Step 3:** Open Lean and Agda draft PRs documenting source-written status and kernel-pending boundary.
