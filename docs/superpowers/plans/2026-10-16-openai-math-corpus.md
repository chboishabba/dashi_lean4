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


### 29 October — Max-Cut terminology correction and original owner reuse

**Confirmed two different senses of “max-cut”:**
1. OpenAI family 102 is the actual graph-optimization/approximation-hardness theorem `OAI.OptimalMaxCut.main` in `OAI.Computability.MaxCut.Main` (source-owned OpenAI `openai/math`, pinned above). Independent mathvet review lists `OptimalMaxCut` among built/audited solutions and Comparator-accepted challenges. Verify actual target statement directly before adapting it.
2. DASHI's “max-cut” often names a *frontier/obligation partition*, not the graph optimization problem. Existing Agda `DASHI.Unified.TOE369MaxCutKernelBidiTernaryExact` is a theorem reuse / nonpromotion aggregate, not a Max-Cut graph-hardness proof.

**Recent reuse:** Agda #1407 owns 27/9 antipodal orbit symmetry, Hermitian Q(omega) reconstruction and 729-contribution finite convolution (source-written; kernel pending); #1390/#1336 converge finite-ternary/kernel-BIDI/Ibrahim nonpromotion; #1249 owns distinct path/periodic cube graph/Fourier geometry. Keep these mathematical owners separate from OpenAI family 102 and from graph-hardness claims.

**Corrected P2 max-cut:** First inspect the **actual** type and assumptions of `OAI.OptimalMaxCut.main`. Identify its graph classes, weighted/unweighted convention, approximation ratio, Unique Games assumptions, reduction and complexity model. Separately audit DASHI for any existing *actual graph-cut objective* and corresponding algorithm/reduction. Only then attempt a graph-morphism or group-orbit quotient with an exact weighted edge-count/objective identity and polynomial-time construction. The necessary condition for orbit compression is that edge weights are invariant under the acting graph automorphism group (or that a more general equitable quotient preserves the relevant weighted cut), not that a 27- or 9-element orbit count merely matches. If group-invariant cuts are only a restricted subclass, their quotient optimum need not equal unrestricted Max-Cut; retain this as an explicit counterexample/negative-control task. In particular, no hardness transfer from general graphs to fixed 27-vertex finite graphs can exist under standard variable-input complexity definitions; a finite fixed graph has constant-size exhaustive search. Require a *uniform variable-size graph family* plus polynomial reduction and objective/approximation-preserving correspondence.

**Attribution:** Goemans–Williamson SDP approximation, Unique Games hardness source authors, OpenAI released formalization, and previous DASHI ternary/orbit theorem owners are separate. A new exact graph quotient proof by DASHI, if supplied, is attributable to its repository implementation, not original invention of the general method.

**Immediate blocker:** exact upstream family-102 Lean theorem signature and direct same-problem DASHI graph objective owner not yet source-verified in this pass; do not declare reduction complete.


### 29 October — actual finite Max-Cut orbit regression committed

Lean #78 branch commit `796781ba2decdb66b00e1243e3dfba5817e15797` adds `scripts/check_openai_maxcut_orbit_objective.py`. An equivalent locally executed Python script passed finite graph/orbit/counterexample tests in this session. The committed script itself has not been independently re-executed by a connected checkout or CI; mark **SOURCE-WRITTEN**, with local algorithmic-equivalent **EXECUTED CHECK**, not kernel-accepted.

Precise result: for any undirected nonnegative weighted finite graph and vertex partition (orbits of a weight-preserving automorphism action), sum inter-orbit edge weights. Each Boolean quotient assignment lifts to a vertex-orbit-constant cut with **identical** weighted objective; every invariant cut descends. Thus `maxCutInvariant(G,H) = maxCut(quotientWeighted(G,H)) <= maxCut(G)`. The inequality is strict for a one-edge two-vertex graph with vertex-swap symmetry, and a four-cycle with transitive rotation. This finite proof idea is classical; source regression code ownership is DASHI.

**New proof target:** Re-express this theorem over upstream `OAI.OptimalMaxCut.Graph.cutSize` (simple unweighted graph, edges exactly once), rather than inventing a second graph ontology. Verify the actual upstream pinned solution theorem `OAI.OptimalMaxCut.main` separately. State weighted orbit aggregation as a target interface and prove an objective-preserving graph-reduction law plus a polynomial encoding/runtime bound only when the quotient graph family grows with input. Do not claim general Max-Cut hardness for fixed 9/27 sites or on symmetry-restricted cuts. Compare with #1407 mathematical 13/27–5/9 involution, but do not identify its signed Fourier coefficient involution with graph automorphism without a concrete action on the graph edges.

**Highest-alpha follow-up:** (1) Lean native exact cut/quotient theorem on pinned upstream graph type; (2) source-verified uniform complexity transport, preserving thresholds and output scale; (3) graph family/action witness from existing finite fibre owners; (4) reverse BIDI and prior-art ledger with Ibrahim Pareto/snowball source custody; (5) optional lifted symmetry QAOA orbit-state reduction, maintaining the distinction between invariant *assignments* and invariant *linear subspaces*.


## 29 October 2026 — OpenAI 26 October ETH / P-versus-NP source-delta acquisition

**Original source:** https://github.com/openai/math/blob/main/history.md (October 26, 2026). Announces two new manuscripts and accompanying Lean formalizations: (i) **The Exponential Time Hypothesis is False** (deterministic subexponential-time, polynomial-space exact counting for fixed-width CNF; claimed 3-SAT consequence refutes ETH); (ii) **Local smoothing for the Euclidean wave equation** (claimed implications for Kakeya and restriction). Also reports an added Lean formalization for **the rational Hodge conjecture for CM abelian varieties**, improved Lean formalizations/Comparator configurations, and restored dimension-six mutually unbiased bases C++/records/Python checker. Reconfirm source bytes and current commit before copying identities or asserting kernel status. This is dated 2026-10-26, not a claim of a 2026-10-29 new result.

**Semantics correction:** `P = NP => not ETH` but `not ETH` does **not** entail `P = NP`. A deterministic subexponential algorithm may remain superpolynomial. Counterexample to the invalid inference is the asymptotic cost shape `2^(sqrt(n))`, which is subexponential but exceeds every fixed polynomial; this is a cost-function illustration, not a statement about the announced algorithm. An exact model is `ETH := there exists epsilon>0 such that 3-SAT requires 2^(epsilon*n) time` (with exact quantifiers/model fixed to source); distinguish ETH, #ETH, SETH, counting vs decision, randomized vs deterministic, uniform vs nonuniform, size vs variables, worst-case vs average-case, and polynomial-space vs polynomial-time.

### P0–P7 source-first obligations

- [ ] **P0 source identity:** Diff pinned `openai/math@1581d4c` against the exact Oct-26+ head, identify the ETH manuscript path, Lean formalization catalogue entry, complete declaration names, dependencies, source SHA, changed/withdrawn status, Lean toolchain, Comparator configuration, and exact mathematical statement. Do not assume family ID or local kernel acceptance.
- [ ] **P1 original source audit:** Read the actual ETH proof and accompanying Lean source; extract width `k`, variable count `n`, `#SAT_k` count output and any integer bit-size costs, uniformity, machine model, polynomial space and subexponential runtime definition. Record which headline assertions are formally represented versus manuscript-only.
- [ ] **P2 current canonical DASHI P-vs-NP owners:** Reuse Agda #1040 `PNotEqualsNPDirectSATLowerBoundExact` (literal BooleanFormula, PolynomialCostModel, universal polynomial-SAT decision failure frontier), #1129 resource-closing semantic-quotation actual coded TM/compiler frontier, #1006 `RSAQuantumShorPvsNPCrossPollinationExact`, #1366 Millennium cross-prover nonpromotion, Lean #45 upstream acceptance audit. Search other in-repo direct SAT/Cook/complexity owners before construction.
- [ ] **P3 exact counting-to-decision bridge:** On the *same* CNF encoding and machine model, show `countSat(F)>0 <-> satisfiable(F)`; establish overhead bound in the chosen bit-complexity model. The reverse decision-to-exact-counting implication is **not** free.
- [ ] **P4 quantified runtime bridge:** Prove formal source subexponential bound and `poly(n)*2^o(n)=2^o(n)`; distinguish fixed width / encoding length / clause count / output bit length. Do not promote an asymptotic statement to a polynomial-time decision algorithm.
- [ ] **P5 ETH refutation semantic bridge:** Specify source's actual ETH variant and its reduction to 3-SAT; only infer its negation from same-model deterministic exact-counting/subexponential algorithms with the required quantifiers. Keep #ETH and SETH claims separate.
- [ ] **P6 conflict / residual reconciliation:** A proposed universal polynomial SAT lower bound is **compatible** with a subexponential 3-SAT algorithm. Check any DASHI P9 / self-reference / diagonalization / quotation assertion for stronger universal exponential lower-bound claims. Run dependency-derived selective invalidation through the existing Agda #772 owner only where source semantics actually conflict. Never relabel source announcements as proof contradictions.
- [ ] **P7 research snowball:** Route new local-smoothing, Kakeya and restriction donors to existing harmonic/Fourier/NS/YM analytical owners after verifying their exact hypotheses; route newly formalized CM Hodge to existing #002/#032 source atlas with upgraded **source status only**, not automatic Agda proof; route dimension-six MUB checker as computational evidence, not kernel theorem. Maintain prior published/older DASHI/original OpenAI authorship and independent referee status.

**Priority:** P0→P1→P3→P4→P5 before a cross-domain theorem transport. Reuse #1040/#1129/#772 for P2/P6, and the original OpenAI corpus vendor (#78) rather than a second source store. A successful ETH formalization may offer algorithmic machinery but does not pay the remaining universal polynomial SAT lower-bound theorem or prove P=NP. No Lean/Agda kernel run is claimed by this roadmap update.
