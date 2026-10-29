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


## 29 October 2026 — transcript-led TSP / A* / RSA / tetration / 9999 cross-pollination

**User-supplied secondary source**: ThePrimeTime, *This is Crazy*, 2026-10-29, https://www.youtube.com/watch?v=Ka0p5tUUmgg ; transcript supplied in conversation. Source is a discussion of OpenAI's 26 October release, not an original proof or verifier receipt. Inspect primary OpenAI `math/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex` and `math/lean/docs/378.md`, plus OpenAI 26 October announcement, for exact claims. Avoid the transcript's misleading shortcuts: ETH-false ≠ P=NP; P=NP does not by itself establish efficient recovery of arbitrary existing secret keys without encoding/representation/runtime detail; factoring is not established NP-complete; neither SHA-256/HMAC nor practical protein-folding applications follow from the ETH claim; a 2^o(n) SAT solver does not uniformly transfer to every NP problem under arbitrary polynomial reductions.

**Primary theorem reconciliation:** OpenAI's Oct-25 manuscript states exact fixed-width CNF counting and polynomial space; the paper's main theorem gives `(n+m)^{O_k(1)} 2^{O_k(n loglog n / sqrt(log n))}` bit time and sharper sparse-clause bound, while the Lean formalization note `378.md` states `(L+1)^{O_k(1)} 2^{O_k(n (loglog n)^2/sqrt(log n))}` for canonical encoded input length L, with polynomial tape-cell space. Keep these distinct; do not silently copy the manuscript's sharper exponent into the Lean theorem, or mistake the video's shorthand `2^{n/sqrt(log n)}` for the fully checked general theorem. The paper expressly states that general polynomial-time reductions can destroy the subexponential parameter bound and considers graph-coloring / matching consequences separately.

### Existing owners confirmed in Agda current default branch

- `DASHI.Computation.PathfindingFibreFamilyExact`: BFS, Dijkstra, Bellman-Ford, A*, bidirectional and BMSSP as distinct residual/scheduling fibres. Explicit `quotientAloneProvesAlgorithmCorrectness=false`.
- `DASHI.Computation.AStarPlateauFibreExact`: A* f-plateau and residual semantics. Reuse; do not create another algorithm identity.
- `DASHI.ComputerScience.RSA260BidiSignedResidualAStarSearchExact`: RSA generator-coefficient residual A* scheduling donor, explicitly no established admissible heuristic or optimality certificate. Companion `RSA260BidiAStarEncodingGeneratorCollisionExact`, `RSA260BidiAStarRelationAugmentedEncodingCollisionExact`, and production diagnostic adapter retain coarse/fine identity-loss controls.
- Agda #839 `FibreProgramComplexityExact`: transition, storage, head movement and physical-cost consumers distinct.
- Agda #104, #1000, #1006 and #875: Shor order-to-factor certificates, classical/quantum distinctions and RSA original-source snowball provenance. No transfer from SAT-ETH to polynomial classical factoring is permitted without a real reduction and a polynomial bound.
- `DASHI.Topology.TetrationalGateField` and `Ontology.DNA.FixedPointTernaryAndTetration`: height/size recurrence; `DASHI.Foundations.DecimalNonaryRefinementBridgeExact`: decimal/nonary exact finite accounting. Agda #1260 owns `9999` factorial/CRT and Eisenstein `lambda^9` arithmetic. Tetration height is a growth representation, **not** an integer factoring algorithm; modular congruences/CRT witnesses do not by themselves give a factor-finding speedup.
- Agda #772: canonical selective invalidation / Pareto / worklist. Reuse historical Ibrahim source/prior-art custody and no-promotion owners.

### Specific reusable theorem obligations — no false welding

- [ ] **TSP1 decision-language identity:** State weighted directed/undirected TSP, Hamiltonian cycle, threshold decision `exists tour, cost<=B`, cost encoding (binary weights), and tour certificate verifier. Distinguish exact optimization, approximate optimization, decision and enumeration.
- [ ] **TSP2 reduction direction:** Prove actual TSP-decision → canonical k-CNF via a polynomial-size Cook encoding, with an explicit input-variable blow-up `N(n,logW)`. Do not silently infer `2^{o(n)}` TSP from `2^{o(N)}` SAT when `N` is superlinear.
- [ ] **TSP3 parameter-preserving route:** If aiming for true 2^o(n) TSP, prove a *linear-variable* (or otherwise sufficient subexponential-preserving) source reduction and include the polynomial overhead. If not, retain the exact derived upper bound `poly(input)*2^{o(N)}` only.
- [ ] **TSP4 reconstruction:** Convert SAT decision into a witness using a bounded sequence of queries; show objective/binary-search overhead and output encoding cost, including false-positive/false-negative proof guards.
- [ ] **ASTAR1 state fibre:** Reuse `PathfindingFibreFamilyExact` and `AStarPlateauFibreExact`. Encode TSP partial tour `(visited,current,cost)` with sound transitions, visited-set identity, terminal-return edge, invariant of remaining vertices and cycle closure.
- [ ] **ASTAR2 lower bound:** Define a genuinely admissible heuristic on the same TSP graph (e.g. relaxation / MST plus entry/exit bounds where applicable). Prove `h(s)<=remainingOptimalCost(s)`, nonnegative weights and consistent/reopening rules where needed.
- [ ] **ASTAR3 search correctness:** Prove invariant preservation, termination on finite states, returned-tour validity, goal optimality under precise A* policy. Distinguish exponential worst-case exploration from good-instance pruning and do not equate A* scheduling with complexity-class collapse.
- [ ] **ASTAR4 fibre quotient:** Prove quotient-state simulation and cost compatibility before deduplication; demonstrate collision counterexamples when visited set / last city / cumulative cost / predecessor changes optimal future.
- [ ] **FACT1 counting→decision / factoring:** Keep exact #SAT→SAT decision bridge separate from classical integer factoring. Factoring witness `1<d<N and d|N` is efficiently verified; factoring is not known NP-complete. Actual SAT encodings of multiplication can grow with bit-length; track length and machine cost.
- [ ] **FACT2 RSA/Shor:** Reuse #1000 order-extraction and #1006 classical/quantum distinction, with RSA-260 diagnostic A* separate from a certified classical factor algorithm. Preserve provenance #875.
- [ ] **FACT3 tetration/9999:** Audit #1260 exact `9999` CRT residues, #772 growth-worklist and canonical tetration recurrence. Require a reproducible new *uniform factoring algorithm*, sound divisor certificate, and proven runtime/space bound before claiming complexity gain. Tetrational state counts may make algorithms worse. Never infer factorization from a base-9/decimal pattern or residue match.
- [ ] **VIDEO1 claim matrix:** Timestamp/source excerpt -> original paper/Lean statement -> actual implication -> disproved overreach. Distinguish SHA-256 preimage/collision, HMAC unforgeability, RSA factor security and PQ protocols; do not state all encryption broken.
- [ ] **FIBRE1 qualified joins:** Only connect 27/9, hyperfabric or ternary symmetry to SAT/TSP/factoring if an actual computable map preserves witnesses, objectives, transition costs and asymptotic input length; provide an explicit nonfactorability counterexample otherwise.
- [ ] **BIDI1 source/ownership receipt:** Record historical Cook–Levin, Held–Karp dynamic programming, Hart–Nilsson–Raphael A*, Dijkstra, Shor, ETH (Impagliazzo–Paturi), OpenAI 2026 original authors, prior DASHI PR and exact declarations, new repository code, executed checks, and kernel receipt separately.
- [ ] **PARETO1 ranked source-faithful tests:** First: TSP→SAT variable blow-up; A* admissibility; exact ETH theorem type. Next: RSA factor certificate and Shor source identity. Finally: tetration/9999 as counterexample-backed complexity diagnostic. Reuse #772 recursive selective invalidation without duplicate owner.

**Roadmap cut:** No kernel-verified TSP→SAT complexity transfer, admissible TSP A* heuristic, or uniform tetration-based factoring improvement is claimed in this tranche. Existing source-written finite arithmetic, pathfinding and RSA owners are useful donors but not same-object proof receipts.


## 29 October 2026 — CORRECTION: Pickover sine `99^(9999!)`, not factoring/tetration

**User correction accepted.** The relevant challenge is `sign(sin(99^(9999!)))`, with **postfix factorial**. The prefix `!9999` is the unrelated subfactorial/derangement count. Previous `FACT3` tetration-to-factoring framing must NOT be represented as the user's intended 9999 task. Treat the previous FACT3 as an optional independently gated arithmetic experiment, not a motivating source or necessary ETH/P-vs-NP bridge.

**Actual repository owners verified in Agda PR #1414, head `b87483e44d5fef456c0aa081b957f0d736873e51`:**
- `DASHI/Foundations/PolynomialPickoverFactorialGammaDegreeExact.agda` defines `factorialIndex9999 = 9999 !` and `pickoverInteger = 99 ^ factorialIndex9999`. It distinguishes degree-angle reduction and radian analytic authority, includes factorial vs subfactorial typed differentiation, modular cycle witnesses, and makes `isRadianAngleSolvedHere = false`. Historical Euler/Legendre Gamma and classical Euler phase law have their own attribution. Analytic Gamma interpolation is conditional.
- Agda #1260 owns the pre-existing exact `9999` CRT / factorial and Machin-rational sign-probe machinery on an independent branch; import only once merge/reconciliation allows; do not copy/reassign its source proof ownership.
- Primary mathematical search: https://math.stackexchange.com/questions/5152905/determining-the-sign-of-sin999999-is-straightforward-with-the-angle-in . This is **discussion**, not an accepted mathematical proof or original Pickover publication. Degrees: `pow(99, factorial(9999), 360) = 81`, so sine positive. Radians: cannot reduce integer argument modulo 360; needs rigorously certified distance from nearest multiple of `pi`, with enough precision to settle sign. Neither tetration, CRT residue nor finite decimal coincidence by itself solves this analytical sign.

**Confirmed PR #1414 27→11→7 reusable owner and proof status:**
- `PolynomialC3S3TwentySevenOrbitQuotientExact.agda`: C3 conjugation on the **27 functions** of three-valued truth set, 11 orbit classes (three fixed plus eight triples), actual classifier/representatives/witnesses, induced reflection, map to seven S3 classes, orbit-iff equivalence and invariant-function factorization. SOURCE-WRITTEN, no Agda kernel receipt.
- `PolynomialC3S3OrbitFieldVectorAtlasExact.agda`: 7/11/27 length field codecs with 3^7/3^11/3^27 counts and 11=7+4 residual coordinates. No Fourier-eigenspace or Monster identification inferred.
- `PolynomialC3S3OrbitSamplingProjectionExact.agda`: selected-representative projections `P_C3`/`P_S3` idempotent with nested absorption, not Fourier averaging or orthogonal projection.
- Non-equivariance: conjugation C3 has fixed points; free output-phase C3 has none. No equivariant identification. **Separate quotients**: conjugation 27→11→7; output phase 27→9; unrelated horn five-orbit quotient in Agda #1244.
- Dedicated original Agda roadmap `Docs/papers/PolynomialVideoTernaryOrbitInvariantFieldsRoadmap20261029.md` tracks O01–O24 and later O25–O26 at #1414; keep its detailed algebraic ownership, status and independent geometric/Spin/Galois boundaries there. No new duplicate orbit theorem belongs in Lean ingestion branch.

### New priority ledger and false-weld guards

- [x] **PICK0 expression identity:** `99^(9999!)` distinguished from `99^(!9999)`, `(99^9999)!` and tetration. Paid at source level in Agda #1414.
- [x] **PICK1 degree sign:** exact residue `81 mod 360` and positive sine in degrees; Agda source and cited independent finite run. Local Agda kernel pending.
- [ ] **PICK2 radians sign:** need an actually checkable interval enclosure for `99^(9999!) / pi` or the equivalent rational enclosure of `pi` with precision sufficient to determine which sine half-period contains the huge integer; computing a decimal approximation with ordinary precision is not evidence. Complexity and rational-interval bit lengths may be astronomical.
- [ ] **PICK3 prior art:** confirm original Pickover publication (if any); record existing math discussion as secondary source only, original historical modular periodicity and Gamma authorship separately; do not claim original discovery.
- [x] **ORB1 existing quotient:** reuse #1414 27→11→7 with exact 27 classifiers, source-only proof and finite tests; different from phase 27→9 and horn five-orbit.
- [x] **ORB2 non-equivalence:** no fixed-point-preserving equivariant identification of conjugation action with free output-phase action.
- [ ] **ORB3 kernel:** typecheck exact #1414 Agda checkout and imports; retain kernel pending until receipt.
- [ ] **ORB4 Fourier extension:** only attempt actual C3/S3 representation-equivariant character/Fourier intertwiner on typed invariant fields; sampling projectors are not averages. Check characteristic and inner product before claiming orthogonality.
- [ ] **ORB5 cross-domain search:** mathematical joining to OpenAI ETH SAT counting/TSP/Max-Cut requires explicit graph/constraint action, orbit-preserved objective or counting-weight identity, and complexity/encoding bounds. Bare 27/11/7 counts or parity cannot transfer hardness or SAT speedup.
- [ ] **SOURCE1 updated original attribution:** separate historic finite-group/orbit/Galois mathematics, PR #1414 original Agda proof authoring, PR #1260 arithmetic owners, external OpenAI ETH/Max-Cut formalizer, executed Python and Agda-kernel status, and Ibrahim Monster 3B original ownership. No coincidental numerical or character fingerprints become a same-object representation.

**Pareto order:** first preserve already-paid #1414/#1260 owners, then obtain PICK2 analytic sign bounds if feasible, then exact ORB4 Fourier proof; only after actual same-object coupling should OpenAI SAT/graph complexity receive a bridge. No CI edit required; missing compiler receipts remain explicit.


## 29 October — ACTUAL Agda/Lean repository archaeology: concrete pre-OpenAI donors and source proof comparison

**Search-before-write performed for both real repositories:** actual master source for `PNotEqualsNPConcreteCircuitSharedSemanticsExact`, `PNotEqualsNPConcreteCircuitSharedUpperBoundExact`, `PNotEqualsNPRestrictionQuotientSATAuthorityExact`, `SATDecisionToWitnessSelfReductionExact`, prior 11-orbit and 2-point parity owners, and current #1414 branch; Lean #78 `Integration/OpenAIMath/SourceAtlas.lean`; `openai/math` original `OptimalMaxCut.Main`, family 378 Comparator and `SqrtLogSpace.Final`. Compared with exact early Agda PR changed-file patches, not just titles.

**Proven prior DASHI repository-file introduction chronology** (NOT independent worldwide priority or Agda kernel receipts):
- [Agda #437](https://github.com/chboishabba/dashi_agda/pull/437), **opened 2026-08-06**, patch adds `DASHI/Biology/MoonshineOrbifoldSectorProjectorExact.agda` (C2 rational positive/negative projector, parity, reconstruction and idempotence via rational solver). Mathematically inherited Reynolds/finite character theory and orbifold authors retain historical authorship.
- [Agda #514](https://github.com/chboishabba/dashi_agda/pull/514), **opened 2026-08-10**, actual patches introduce `NormalizedFibreAveragingExact` and `GlassesProjectionInvolutionExact`, exact 2-fibre averaging/retraction and projector exchange, without asserting abstract analytic disintegration.
- [Agda #1040](https://github.com/chboishabba/dashi_agda/pull/1040), **opened 2026-09-24 and merged by 2026-10-04**, exact patch introduces `PNotEqualsNPConcreteCircuitSharedUpperBoundExact` with `gateConstraintNodeCountAtMostThirteen`, `programSharedConstraintNodeCountUpper`, `sharedAcceptanceFormulaNodeCountUpper`, and `PNotEqualsNPRestrictionQuotientSATAuthorityExact` with `rootSatisfiableGivesQuotientAuthoritySatisfiable` and reverse. This predates ETH discovery Oct 16 / formalization Oct 17; these are **semantic and formula-node complexity** results, not an ETH subexponential machine theorem.
- Existing `SATDecisionToWitnessSelfReductionExact.recoverWitness` counts **one oracle decision query per variable**, but explicitly leaves actual formula-substitution instantiation unconstructed; a call count is not Turing runtime.

**OpenAI actual solution declaration, not comparator:** family 102 `OAI.OptimalMaxCut.main` in `lean/OAI/Computability/MaxCut/Main.lean` proves a variable-size simple-unweighted graph polynomial-time 3SAT gap reduction at all ratios strictly above GW; comparator `OptimalMaxCut.lean` contains a target `sorry` by design. Family 378 `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat` in `lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean`, with `compiled_exact_count_and_sat`, actual canonical bounded-width CNF encoding and primitive machine, an exact count+SAT output, polynomial visited tape **at every prefix**, and `poly(L) × 2^O(n(loglog n)^2/sqrt(log n))` time. Its `Interfaces.scan_calls_le_length` is only a leaf-call bound and explicitly not machine step cost. This is not P=NP and is not a direct logical generalization of Agda #1040.

**New precise reuse-first mathematical gap:** compare DASHI Cook `BooleanFormula` / Tseitin syntax-node counts with upstream `SAT.CNF (Fin n)` and `Encoding.formulaBitLength`; prove a computable semantics-preserving **bounded-width, bit-encoded** transformation and count preservation (or document that Tseitin only proves satisfiability, not #SAT), plus exact parameter `n` growth and runtime/space. Any statement `#SAT(F)=#SAT(Tseitin(F))` requires unique extension of auxiliary gate variables with exact finite support, not just bidirectional satisfiability. Only then can one claim a transfer, no automatic stronger result.

**Actual #1414 work reused the already-proved parity owner rather than duplicate it:** `PolynomialC3S3RationalCharacterAlgebraExact` now uses `MoonshineOrbifoldSectorProjectorExact`, derives rational eleven-orbit reflection-invariant positive and odd negative modes, positive projector idempotence by inherited theorem and actual eleven-class involution. These are SOURCE-WRITTEN only; no Agda kernel receipt. Its own roadmap now tracks through O52. No ESD files modified, no prior Ibrahim Monster 3B action re-owned.

**Two newly updated code artifacts:** Lean source atlas commit `ac33b9662c7603126d78e87b817d20cbfbfbff52` introduces `LaterUpstreamReceipt` for family 378 and **explicitly marks absent at pinned vendor SHA `1581d4...`** (upstream new inspected revision `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`); Agda #1414 added same-carrier borrowed parity consequences. This avoids silently equating live OpenAI main with pinned vendor content.

**Updated Pareto:** (1) exact-head Agda and Lean compile if environment permits; (2) upstream revision/manifest to source-typed vendor accounting without mutation of incompatible Lean toolchain; (3) source type/encoded input mapping and parsimonious count bridge; (4) uniform machine runtime/space and 3SAT/TSP parameter preservation; (5) only if strict implication, priority-certified stronger-than-OpenAI claim; (6) original-owner and selective invalidation receipts via Agda #772. Status is truthful: commits/source inspected and authored, no local kernel run, no arbitrary Monster/SAT/graph equivariance or novel mathematical prior-art priority claimed.
