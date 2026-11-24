# P0 — Native Rust numeric-PNF port, formal constitution before implementation

Status: **24 November 2026**. Original source authorities: SLR Rust PR #78;
SensibLaw Python/strict PostgreSQL and its SQL migrations; DASHI Agda
numeric-PNF constitution; DASHI Lean PR #112 for the P0-specific proof and
acceptance contract. No compiled Rust numeric engine is claimed here.

The user's two-hour process launched
SensibLaw/scripts/run_complete_tranche.py (the *historical* CLI).
That CLI explicitly selects local-compatibility-replay unless supplied
--strict-exact; the production wrapper run_complete_tranche_production.py
always injects --strict-exact. The original architecture notes identify
historical document-size Python typing/persistence as an hour-scale path
already removed from the strict PostgreSQL numeric production contract.
**Do not port that compatibility implementation.** Verify the actual old
run ledger's execution_strategy_ref before attributing all of its runtime
to the strict compiler: the visible process command was truncated.

The stopped job was processing hundreds of kilobytes and thousands of
sentences. The accepted P0-B source consumer is the much smaller book
manifestation with original SHA-256
7ff2ec8ffe6243871ad682e7d7060fe3b84025fb15dbe229154d7aa7f6a72b30
(6,678 source bytes in the previous original-source audit).
A larger GWB article or tranche must not be silently called that exact
manifestation. Require cryptographic bytes, Unicode coordinate encoding
and revision match *before* any compiled numeric object can support WELD-01.

## 1. Existing donors and why the port is not a rewrite

| Owner | Existing source contract | Rust port must preserve |
| --- | --- | --- |
| SLR Rust | sl-core numeric sentence/token projection, sl-pg-source-store original parser/source reinspection and native bounded frontier, source-local consumer | Same source digest and original Unicode offsets, explicit missing parser capabilities, no head fallback, exact source/provenance refs |
| SensibLaw strict numeric owner | run_complete_tranche_production.py; src/policy/work_conserving_ordered_compilation.py; src/pnf/bounded_streaming_owner.py | Numeric runtime mode, canonical owner activation revision, staged persistence/coverage, not Python compatibility replay |
| Canonical reducer | src/pnf/factor_proposals.py; src/policy/reduction_hot_path_execution.py | Canonically ordered proposal_ref, exact semantic-coordinate/fibre/type/signature bucket, *first compatible* grouping, exact factor IDs and incompatible-alternative residuals |
| Dependency owner | src/policy/dependency_indexed_owner_execution.py | Reverse dependency and observation indices, transitive dirty-owner wakeups, producer multiplicity and genuine loss of availability; do not assume same-owner incremental reductions are associative |
| SensibLaw SQL | m051, m069, m074, m077, m083, m086, m089, m123-124, m141-145 | Original token→object support; numeric typed demand; separate represented/active/refuted candidates; explicit open-world closure; original document-derived witness/admission; H9 supported occurrence; Level-3 supported factor/retraction |
| DASHI Agda donors | ConsumerSufficientComplexityExact, OwnerFibreReductionComplexityExact, SignatureBucketReductionFactorizationExact, SparseFrontierTopologyExact, ProducerCompleteDependencyProjectionExact (referenced by NumericPNFHyperfabricEverything.agda) | Consumer/residual/provenance equality, dependency-complete invalidation, canonical bucket factorization, sparse topology and no false authority |
| DASHI Lean | NumericPnfRustPortContract.lean | Manifest isolation, parser/nonadmission, prune/nonrefutation, open-world witness and live-candidate counterexample, independent-owner commutation, conditional work accounting, source-bound replay |

**Attribution:** SLR owns native observation. SensibLaw owns canonical
numeric-PNF meanings and SQL admission. DASHI's role is formal proof
integration, not creating new source/identity authority. Rust output is
a *producer of the existing SQL input contracts*; it may not bypass
original admission triggers and views.

## 2. Formal invariants — required for each native stage

**N0 Manifest and provenance.** Every record carries exact
(document, immutable source revision, canonical UTF-8 SHA-256,
Unicode codepoint coordinate contract, parser/model/normalization
contract, compiler rule-set revision). The SLR book digest is
7ff2ec8f…; differing digests/byte lengths must fail closed.
Don't infer equivalence from the string GWB or an offset crosswalk
that cannot re-find exact local source text.

**N1 Observation soundness.** Parser output is an observation, not
a semantic identity. Missing dependency head is an explicit residual
(no root fallback); token/NER duplicates are separate observation
channels over one original span. Each native fibre owns its exact
sentence ranges; overlap context is not double-admitted.

**N2 Canonical semantics.** For each owner bucket, preserve exact
source semantic-coordinate, fibre kind, factor type, structural
signature, proposal refs, role-binding conflicts and deterministic
first-compatible allocation. Physical bitset acceleration is allowed
only when its chosen group equals the canonical first-compatible
group for *every* proposal. Canonical ordering and stable receipt
hashing are part of parity, not optional formatting.

**N3 Dependency correctness.** Admission/retraction dirty exactly
the affected reverse-reachable owners. Global known_dependency_refs
is a validity input even if factor grouping is signature-local.
Producer multiplicity prevents one owner from removing a factor
still produced by another. Unknown observation/dependency refs
produce named residuals rather than silently disappearing.

**N4 Open-world candidate safety.** Separate represented F,
active P, deferred/reopenable Q, represented residual R and
outside-model O. A resource/budget prune changes P/Q, never
semantic refutation. A semantic refutation requires a
candidate-specific actual evidence row; unknown/missing evidence
cannot be treated as false. The 64-candidate cap is an execution
window, not the size of the candidate universe. O is true until
a *real* coverage witness is verified. Retain signed -1/0/+1
phase and exact numeric residuals separately; do not convert
them to floating probability/confidence.

**N5 Identity and H9 authority.** Parser PERSON, two Bush mentions,
a preferred H9 label, a unique ranked candidate and a named-topic
policy inference do NOT build a numeric object identity witness.
Require exact original token↔numeric object occurrence, typed
demand, represented/open-world coverage, resolved_unique
with candidate_count=1, real constraints, original accepted
document_derived witness and supported factor alignment before
level-3. m123/m124 entity-bearing/label anchors must derive
from actual supported occurrences; never assume the legacy
demand.source_object_id alone suffices.

**N6 Reversible execution.** Original Level-1 objects and source
offsets remain immutable. Commit derived factors and their
witness/revision dependencies atomically under original SQL
constraints. Retraction of an admitted witness invalidates
only dependent Level-3 factors, not Level-1 text or retained
historical evidence. Native source-consumer read-only replay
does NOT constitute transactional SQL retraction.

**N7 Consumer sufficiency.** The native output and strict numeric
reference must give equal consumer-relevant observations,
unresolved residuals, provenance, coverage/open-world state,
typed actor outcomes, same semantic factor/receipt IDs, and
reopen behavior. Hash or comparison equality of final answer
strings is insufficient. If a consumer uses a distinction
not captured by the proposed projection, refine the projection;
do not claim equivalence with missing obligations.

## 3. Formal proof and port architecture

New file: DASHI/output-final_aristotle/RequestProject/Slr/
NumericPnfRustPortContract.lean.

It proves reference-level N0–N6 implications (no identity creation by
parser observation or execution prune, source-bound equivalence/replay,
failure of coverage with an omitted live candidate, distinct-owner
keyed-write commutation), and a *conditional* work-charge theorem.
The formal file itself is written; **Lean acceptance has not been
run on the workstation**. Passing it would certify the model,
not actual Rust↔Python/SQL semantics or physical cost. Those
require correspondence between concrete functions and the model.

**Big-cut Rust crate plan**: a coherent numeric-PNF execution crate
inside the existing SLR Cargo workspace, not a collection of GWB
scripts. Interfaces:

- NativeInput: strict source manifest plus original parser numeric
  observations; source envelope is checked before SQL mutation.
- IndexedDelta: immutable owner/sentence delta with dependency
  and observation refs; deduplicated against source+rule revision.
- OwnerReducer: immutable canonical semantic reducer reference
  and native bitset/indexed implementation; every admitted
  difference must be explained by a formally justified rule.
- CandidateFibre: represented/active/deferred/refuted/open-world
  and evidence-horizon state; no promotion API without accepted
  original owner evidence.
- NumericPnfSink: writes existing SensibLaw numeric PostgreSQL
  schema via staged, idempotent bulk operations and explicit
  original SQL authority; no parallel identity system.
- Receipt: manifest, producer revision, input/output digests,
  count ledger, semantic/physical work counters, dirty owner
  closure, and resumed checkpoint identity.

First source milestone is **exact 7ff2ec8f… original book**,
not the historical 783 KB tranche. Retain all accepted SLR
P0-A/P0-B results without re-running the original parser.

## 4. Physical complexity: what must be proved and measured

The desired local work measure is

    W(Δ) = O(|new_observations| + |touched_dependency_edges|
             + Σ_(dirty owner o) cost(canonical_reduce(o))
             + |actually_emitted_rows|).

This is a **work-accounting contract**, not a claim of linear-time
full compilation. Initial compilation necessarily reads original
input and emits many rows; its cost has a lower bound of input plus
output size.

An even stronger

    W(Δ) = O(|Δ| + |E_touched| + |output|)

is valid ONLY after proving same-owner reduction admits an exact
incremental/append homomorphism (or equivalent reusable signature
bucket certificate). The existing greedy first-compatible
reducer has no general associative-fold licence. Do not omit
Σ cost(canonical_reduce(o)) from claims in the meantime.

Instrumentation must separately report actual visit counts for:
tokens, owned sentences, proposal declarations, dependency refs,
proposals scanned, candidate comparisons, physical role-bit
checks, signature-bucket accesses, dirty-owner wakes, SQL rows
inserted/reused/deleted, and full-scope queries. Also log
peak allocation, wall/CPU time and bytes read/written.
A no-op replay must produce zero semantic work and may only
pay for bounded freshness verification, not a full-fibre scan.
A fast wall time with quadratic scans is NOT an acceptance.

Execution budget: per-slice <=90 seconds to a durable checkpoint
or explicit bounded failure; exact next-resume cursor; a crash
retries idempotently without double admission. This is a
target acceptance condition, not an established guarantee.

## 5. Big-bite acceptance protocol before any full-document mutation

**Gate F0 — formal kernel.** Compile
NumericPnfRustPortContract.lean and print axioms for the exact
theorems. The formal proof of independent-owner keyed updates
does NOT license first-compatible same-owner reordering.

**Gate F1 — frozen golden donor parity.** Pin a strict numeric
reference snapshot for a bounded original-source slice including
the Bush@19, Bush@22 and he@23 regions, competing actors,
missing features, quotation boundaries, duplicate observations
and cap overflow. Compare the entire semantic certificate and
original SQL evidence, not an answer string.

**Gate F2 — bounded full original book.** Check source envelope
first (7ff2ec8f…); use one parser pass already stored. Compile
only native numeric projection of the exact source. Assert counts
and equality of semantic hashes against strict reference for
each owner/sentence; sample and audit SQL referential integrity.
Do not need to process the entire giant GWB tranche.

**Gate F3 — adversarial/replay.** Duplicate chunks, reorder
independent owners, intentionally reorder same-owner proposals
(to ensure rejection/different outputs), drop dependency,
inject second PERSON, cut quotation, alter manifest byte,
force 64-cap truncation, crash and resume. Require equivalence
or explicit residue/fail-closed outcome; witness/QID promotion
must remain impossible without original authority.

**Gate F4 — performance.** Compare strict-path phase timings,
Rust actual work counters and peak RAM/CPU on bounded,
medium and large fixtures. Record and reject hidden full
document rescans on local updates. No speedup claim without
same-input same-output measured baseline.

**Gate F5 — original DB authority.** Only after F0–F4,
allow the native producer to commit exact-source numeric rows
under original schema; inspect H9 supported occurrence,
closed-world witness, unique typed resolution, accepted document
witness, supported Level-3 and transactionally retract/replay
one identity. Q23505 and historical truth remain independent
world/statement evidence lanes.

## 6. Stop conditions and roadmap mapping

Stop and preserve artifacts when source SHA/revision or Unicode
manifestation mismatches, original parser capability is missing,
identity or target ambiguity is unrepresented, any live candidate
was truncated, residual/provenance hashes differ, a dependency
edge is unexplained, same-owner order changes canonical grouping,
or a SQL update would bypass the owner authority.

WELD-01 exact source and numeric occurrence is the first gating
theorem. WELD-02 typed frontier and coverage, WELD-03 unique
source-object resolution, WELD-04 identity/admission, WELD-05
witnessed Level-3/retraction follow only on paid data. P0-B
original source-local Bush inference remains accepted.
Independent Q23505/JMD proof is WELD-07, not a compiler test.

**Current action:** formal model/architecture are committed for
local Lean verification; NO Rust compiler port and NO new
full-source numeric-PNF job have been launched here.
