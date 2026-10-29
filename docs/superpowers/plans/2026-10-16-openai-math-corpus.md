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

---

## 29 October 2026 continuation — full ingestion, reuse-first max-cut

**Provenance:** This continuation is independently authored DASHI planning over OpenAI's Apache-2.0 released source (original authorship OpenAI and credited source authors), not proof of any OpenAI manuscript, Lean kernel rerun, or new mathematical theorem. Do not modify protected ESD modules. Preserve earlier DASHI/Ibrahim ownership and dated source priority. An externally known theorem is not newly invented by DASHI; a new repository proof is not automatically first publication. Never infer a Monster same-object representation from a character fingerprint or arithmetic coincidence.

### Verified current PR owners and boundaries

- Lean #78 (`integration/openai-math-corpus`): genuine **git submodule** `vendor/openai-math-src` pinned at `1581d4cbdd69a0faf34b2089614fe2a814316a6a`; `.gitmodules`, `PIN.json`, vendor materialization script, status model, priority atlas, four source-precise Lean donors (003,102,362,376). Open / not merged; source-written, kernel pending.
- Agda #1212 (same branch name in Agda): source receipt and provenance-only atlas. Open / not merged; source-written, kernel pending. 002 and 032 manuscript-only. Do not treat cross-prover receipts as theorem proofs.
- Agda #772: existing recursive Pareto / dependency-derived truth maintenance / selective invalidation. Reuse; do not create duplicate L40 owner.
- Agda #697: history-indexed proof/experiment/action loop; #672: BIDI residual-fibre and provenance; #1266: factorisation collision and source-first proof-search; #1001: explicit distributed epistemic attribution. Reuse before extension.
- Agda #1217 and Lean #80: existing TOE integration owners. Import qualified proof terms only, not source catalogue metadata as physical claims.
- Upstream `openai/math/history.md` lists changes on 2026-10-26 including two new manuscripts with Lean formalizations; source pins must be compared, never silently moved. Latest catalogue `lean/formalization.yaml` schema v0.4. Counts require pinned exact-tree census, not memory.
- The older checkboxes above are a historical implementation plan; actual files exist in PR #78. Do **not** interpret unchecked boxes as missing implementations.

### Acceptance obligations, mapped to existing machinery

| Group | Obligations | Existing owner / unpaid frontier |
| --- | --- | --- |
| Acquisition | L01–L08 immutable SHA, blob identity, parsed catalogue, coverage, revision delta, round-trip | #78 pin/vendor; **unpaid** full exact-source census/diff |
| Source identity | L09–L16 unique identities, challenge/solution, statement fidelity, dep closure, environment, withdrawal, provenance | #78 Lean atlas, #1212 Agda receipt; **unpaid** exhaustive per-declaration census |
| Lean verification | L17–L24 verifier binding, isolation, checking, escapes/axioms, statement fidelity, replay, statuses | upstream Comparator; **unpaid** exact-head run receipts; not required to write source but required to assert kernel acceptance |
| Cross-prover | L25–L32 same-object and hypothesis/conclusion/definition-preserving transport, cross-kernel firewall | #78/#1212 firewalls; **unpaid** target-specific exact bridges |
| Search/residual | L33–L40 corpus search, ranking nonauthority, decomposition, reverse trace, residual preservation, refinement, collision, selective invalidation | #672/#697/#772/#1266; **unpaid** wiring source dependency identity into already existing machinery, NOT reconstructing L40 |
| Final | L41–L48 canonical ownership, attribution, TOE reachability, unpaid-leaf conservation, valid transfer, coverage/replay/completion | #1217/#80; **unpaid** precise regression and target theorem receipts |

### Source-first Pareto / snowball / Ibrahim worklist

1. **P0: do not duplicate.** Compare exact current branch symbols/PR diffs against #78, #1212, #772, #697, #672, #1266. Record the canonical owner and distinct source-written/kernel-accepted states per declaration.
2. **P1: source-delta census.** Read exact upstream historical and current manifests. Preserve per-entry family, manuscript, dated revision, formalization statement, solution declaration, challenge declaration, dependency closure, license, status and withdrawn/superseded lineage. Produce one machine-readable reconciliation manifest; source-only checks cannot award theorem authority.
3. **P2: donor 102 / Max-Cut.** Compare `OAI.OptimalMaxCut.main` exact hypotheses and conclusion with DASHI graph/C3/fibre Max-Cut targets. An approximation-hardness result and a finite fibre reduction are not the same theorem. Build a bridge only after identifying a same-problem objective-preserving reduction and complexity-preserving map; record any irreducible approximation-gap/complexity assumption as residual.
4. **P3: donor 003 / quasi-RH.** Compare `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` to DASHI G21 exact zeta and zero-free corridor. Obtain explicit same-zeta and domain inclusion maps, preserving strict inequalities, pole exclusions and dependency/axiom provenance. No RH promotion.
5. **P4: donors 362 / Vlasov–Maxwell and 376 / forced-NS.** Match same physical fields, function spaces, time intervals, forcing and smoothness, not merely PDE vocabulary. No YM/Clay promotion without same-object analytical transport.
6. **P5: manuscripts 002 / 032 and subsequent catalogue entries.** Only catalogue and research-route until exact proof declarations/receipts exist; preserve BSD/Hodge source owners and dated priority.
7. **P6: symmetry / fabric / hyperfabric.** Admit a new join only with an explicit map preserving the theorem's typed invariants (group action equivariance, boundary and energy constraints, objective or analytic estimates). Require a commuting square or a counterexample. Numerical 3/6/9 matches, dimension coincidences, Monster fingerprints, and descriptive analogies have zero proof weight.
8. **P7: recursion and invalidation.** Feed source revision differences into canonical #772 dependency graph. Check both reachability invalidation and retention for dependencies + environment + verification-policy pins. Existing general L40 proof stays owned by #772. Expand fixtures rather than invent another calculus.
9. **P8: reverse BIDI.** Given one target obligation, return exact source revision/declaration, the accepted proof receipt if any, all transported assumptions, and unpaid residuals. Given a donor, enumerate candidate consumers without asserting theorem reuse.
10. **P9: TOE.** Export only kernel-supported or explicitly conditional theorem terms into existing root graph; a source citation/metadata/atlas belongs in the research index, not in a theorem-bearing TOE claim.

### Explicit irreducible leaves

- Complete current-versus-pinned catalogue and dependency closure, including withdrawn items.
- Real upstream verifier/kernel receipts for every promoted declaration (if no executable runtime: status stays pending).
- Same-object, assumption-preserving bridges for each adopted DASHI theorem.
- Existing truth-maintenance integration of source revisions (not a new general invalidation lemma).
- Exact proof of objective/action compatibility for any proposed fibre/fabric/hyperfabric symmetry bridge.
- Per-target previous-prior-art/priority ledger: dated published theorem; original source author; older DASHI proof/PR and timestamp; new source code author; executed check; kernel verifier; allowed claim.

### Mandatory evidence row (per donor and consumer)

`upstream_commit | family | manuscript_revision | published_author_and_date | prior_published_result | formal_solution_module | theorem | proof_dependencies | upstream_accepted? | earlier_DASHI_declaration/PR/date | DASHI_proof_owner | DASHI_kernel_accepted? | target | exact_transport_lemma | remaining_residual | invalidation_dependents`.

Statuses: `MANUSCRIPT_ONLY`, `FORMAL_SOURCE_IDENTIFIED`, `SOURCE_WRITTEN`, `EXECUTED_CHECK`, `KERNEL_ACCEPTED`, `TRANSPORT_VERIFIED`, `WITHDRAWN`, `UNKNOWN`. They are non-interchangeable.

### Stop condition

Source admission completes only after every pinned manuscript and every catalogue entry has a row and revision policy; formal theorem promotion completes only for named entries with adequate kernel and target transport receipts. Research into every remaining unformalized manuscript and general Clay problems is **not** silently included in ingestion completion. Record all walls in the evidence row; never fake completion.
