# Formal repair: source-local coreference admission from typed evidence

Date: 2026-11-23. Authoritative real run: `M1–M3 run-PELWk2Yh`
at `dashi_lean4` commit `1a639892849db7df37fecb24a697f03a263d0472`.

**The flaw:** native C4.12 source and five-region parser facts are genuine,
but 27 parser nominations (25 exact spans) are *observation records*,
not a live, complete, typed referent set. The previous kernel
`GWB_NATIVE_FRONTIER_BOUNDARY_KERNEL_OK` checked source-bounded
structural data and conditional consumer principles only.
It does not prove that `he@4534` uniquely denotes the local
referent of `Bush@4310`. S29 is still Pending with zero commands.
The original SensibLaw full-book typed PNF graph was **not** welded
in that run. No Q23505 or Q207 link was paid.

## Exact repair theorem

Let `h` be a pinned original mention, `F` the complete typed
candidate-factor set in a declared original source revision and
discourse scope, `Live(c)` the independently checked surviving
referent candidates, and `~` the reviewer-verified local actor
equivalence relation.

A source-local uniqueness result about chosen factor `b` requires:

1. **Original source/revision/coordinates:** every original token,
   NER annotation, factor and discourse relation is reversible to
   source. Same-span token/NER equivalence is observation co-location,
   not referent equality. `Bush@19` and `Bush@22` are distinct
   mentions pending reviewed same-person correspondence.
2. **Typed source production:** factor scope, morphology
   (Number, Person, Gender if actually present), clause/paragraph
   quotation/reporting accessibility, referential type and explicit
   candidate exclusions come from ORIGINAL SensibLaw
   `compact_binding_artifacts` or original typed owner, not a
   shallow nearest-name/regex bridge. A missing Gender feature
   **retains** a candidate; it is not negative or positive gender
   evidence.
3. **Coverage:** `∀ c, Live(c) → c ∈ F` must be proved for the
   **declared consumer discourse scope**. The original producer's
   64-member candidate cap can emit a
   `candidate_limit_truncation` residual. An omitted live candidate
   contradicts `Coverage`; zero cap truncation is necessary only
   where relevant, and is **not sufficient** for semantic completeness.
4. **Reviewed dispositions:** `b∈F` and `Live(b)`, and
   `∀ c∈F, Live(c) → c~b`. Distinct factor refs may refer to
   the same local actor, but that equivalence needs evidence.
   Excluded candidates need explicit typed exclusion evidence; a
   token not selected by a heuristic has not been disproved.
5. **Distinct governed payment:** the original S29 review command
   must be authentic and `Accepted`; a separate ORIGINAL semantic
   owner must check review authority, source hash/revision, exact
   mention/factor/candidate-set references, compatibility,
   completeness, policy, resolver and alternative dispositions.
   S29 acceptance is necessary but **not sufficient**. The current
   S29 `Pending` state cannot supply this witness.
6. **Consumer invariance:** the source-local answer is licensed
   only when the chosen and every live source reading produce
   the same answer: `∀r,Live(r)→eval(r)=eval(b)`. A live
   rival with a different answer refutes the licence.
7. **Reversibility and world separation:** preserve Level-1 source
   and undo Level-3 substitution on evidence change. External
   George H. W. Bush/Q23505 evidence and the separate George W.
   Bush Wikipedia Q207/JMD article-property proof remain
   independent; no source-local review pays either or historical truth.

## New Lean proof, actual theorem signatures

File:
`DASHI/output-final_aristotle/RequestProject/Slr/GwbCoreferenceFormalRepair.lean`

Important theorems:

- `colocated_observations_share_coordinates`: token and NER co-location
  preserves original coordinates only, no identity theorem.
- `omitted_live_candidate_blocks_coverage`: genuine omitted live
  candidate gives `¬ScopedCoverage`; specifically closes the
  original binder 64-cap loophole.
- `pending_s29_cannot_pay`, `rejected_s29_cannot_pay`: non-admitted
  S29 workflow states cannot carry the governed-payment type.
- `unique_source_local_referent`: exhaustive live candidate scope
  + review of every surviving factor + independent governed
  admission imply uniqueness **modulo reviewed local-actor equivalence**.
- `all_surviving_readings_agree`: a consumer that respects
  equivalence has stable source-local answer across the live scope.
- `rival_reading_blocks_answer`: one admissible conflicting
  reading refutes such a licence.
- `retract_preserves_original` and
  `retract_clears_semantic_payment`: original Level-1 source is
  preserved on Level-3 local projection retraction.
- `q207_is_not_q23505` and `book_is_not_wikipedia_source`: the
  genuinely distinct source/QID lanes cannot be silently reused.

The coreference proof is **conditional**, as it must be. The
original semantic owner must supply *proofs of the premises*; Lean
does not coerce S29 JSON flags or raw parser nominations into those
premises. It also does not authenticate an S29 receipt or independently
decide the literary reading without source/reviewer evidence.

## Runtime boundary hardened in the same packet

The optional original typed-binding interop now records:
`original_binder_candidate_limit_truncation_count`,
`requires_omitted_candidate_audit` and the source binder's original
`exclusion_summaries`. The joint ledger rejects mismatched or
fabricated truncation totals. New tests cover the 64-cap residual and
still refuse to promote the source-local answer.

This is a **scope completeness repair**, not a claim that a
truncated set is by itself incomplete: if omitted candidates are
separately proved inadmissible, completeness can still be paid.

## Local acceptance, one existing packet

The existing script has been extended (no new parser or C4 micro-gate):

```sh
cd /path/to/dashi_lean4
SLR_ROOT=/path/to/slr DATABASE_URL="$DATABASE_URL" \
  bash scripts/run_gwb_native_maxcut_packet.sh
```

This now also runs:

```sh
lake env lean \
  DASHI/output-final_aristotle/RequestProject/Slr/GwbCoreferenceFormalRepair.lean
```

Expected new conditional marker after successful kernel checking:
`GWB_COREFERENCE_CONDITIONAL_REPAIR_KERNEL_OK`.
Look for `lean-coreference-formal-repair.log` in the fresh
project-local run directory. Code is committed but is **NOT YET
locally Lean-accepted** in the connector environment.

To pay positive `he→Bush`, the operator must additionally supply
the original exact-book typed factor/annotation graph, verified
coverage across declared scope and competing actor classes, real
S29 reviewer action and separately checked original semantic
admission. Until then the correct checked output remains
`EXPLICIT_UNRESOLVED`, no world QID or claim truth.
