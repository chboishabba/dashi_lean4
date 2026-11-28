# GWB source-local positive inference — substantive P0 semantic path

Date: 2026-11-24. Source owners: original SLR PR #78,
original SensibLaw typed binder and DASHI Lean PR #112.

## Root-cause correction

**There was no nearest-name coreference resolver in original SLR.**
The original C4.10 tool explicitly accepts a reviewer-selected Bush
source span and verifies only original text/position. The native
frontier deliberately enumerates prior NOUN/PROPN/PRON/NER observations
without resolving identity. The original SensibLaw binder builds
structure/morphology-governed candidate sets, then uses token distance
ONLY to order eligible members before a 64-member cap. That cap can
hide a valid rival and must never be treated as completeness, but it
did not select the Bush antecedent as an admitted local identity.

**The formal mistake was making S29 human acceptance mandatory.**
Original `crates/sl-semantic-admission/src/lib.rs` explicitly defines
`ResolutionAuthority::DeterministicReviewedPolicy` **or**
`ResolutionAuthority::HumanReview`. The earlier
`GwbCoreferenceFormalRepair.lean` only admitted the latter.
Now `SourceLocalResolutionAuthority` has two separate constructors;
`deterministic_policy_need_not_wait_for_s29` proves the former
may exist while the S29 queue remains Pending. The theorem that an
*unaccepted human S29 receipt* cannot pay the human route is still
valid, but it is NOT an obstruction to evidence-based inference.

## What is derivable from the original book, right now?

Original source digest
`7ff2ec8ffe6243871ad682e7d7060fe3b84025fb15dbe229154d7aa7f6a72b30`.
Original source revision
`source-revision:sha256:8dd2afe20c7cfb36bc1372f764b7683962e6acdfac6fe0bfa47554812d4eab00`.
The published real first run `run-PELWk2Yh` contains one
complete original parser run, 27 observations across 5 original
before/focus regions, and 25 physical source spans.

Exactly two **PERSON** named-entity observations appear before
the focus `he` ([4534,4536)); both are `Bush` in different
original sentences at [4061,4065) (sentence 19) and
[4310,4314) (sentence 22). No other named PERSON occurs in
the pre-focus window. The original text is a continuous evaluative
discourse, including `this amiable fellow` in sentence 21 and
`him`/Ronald Reagan in sentence 23. Reagan is mentioned after
the focus, not a preceding same-source candidate. No double-quoted
boundary separates these statements.

This supports a **positive source-local Bush interpretation under
the versioned named-topic-continuity policy**. This is stronger
than an unresolved list, but narrower than all possible linguistic
worlds or an institutionally approved human/semantic admission.
The document's George H. W. Bush/Q23505 identity is a strong
external hypothesis, not a computed QID equivalence.

## Implementation delivered

SLR #78 now exports
`native_antecedent_named_topic::derive_native_named_topic` and
`sensiblaw native-antecedent-review derive REVIEW_ITEM_REF
[PARSER_RUN_REF]`. It consumes the **original PostgreSQL** source
inspection and exact parser-run frontier rather than re-parsing
or choosing the closest name. It:

- Reopens the original focus PRON, POS, dependency and morphology,
  plus each exact source-backed PERSON observation.
- Deduplicates repeated observation positions, groups named people
  by normalized literal and preserves distinct original spans.
- Derives a source-local actor ONLY when one named PERSON occurs in
  two distinct original statements, the proposed antecedent belongs
  to that person group, the pronoun is `he` or `she`, no original
  double-quote barrier occurs and morphology is noncontradictory.
- If any second named PERSON, possible quotation crossing, conflicting
  morphology, corrupt original source or missing repeated support
  occurs, returns explicit ambiguity/residual (or rejects corrupt
  provenance), not an invented actor.
- Returns `source_local_answer=Bush` and
  `source_local_inference_derived=true` when its scope conditions
  hold; human S29 approval is **not** required for this inference.
  It never writes an S29 command or claims an external QID or truth.

The existing M1–M3 operator runner now calls `derive`, runs
additional focused SLR Rust tests, validates the actual actor
result independently through DASHI Python and
`GwbNamedTopicPolicy.lean`, and puts a positive
`DETERMINISTIC_POLICY_SOURCE_LOCAL` answer into the **book
lane** of the joint ledger while retaining separate fields for
institutional semantic admission, all-live reading completeness,
Q23505, Q207 and historical truth. Both source-local and
world-lane authority are never silently conflated.

The new targeted Lean success marker is
`GWB_NAMED_TOPIC_LINGUISTIC_POLICY_KERNEL_OK`. It checks that
the **actual source** contains just the one repeated PERSON name
under the declared policy, not an arbitrary `resolved=true` JSON
flag. There are additional unit tests for a nearer nonperson
PROPN, a second named PERSON, quote boundary, conflicting person/
number/gender morphology, forged foreign source and QID promotion.
Real-input mutations also test that the independent ledger rejects
false local actor and source/authority assertions.

This new implementation is **SOURCE-WRITTEN, NOT YET RUN** by the
operator. The preceding `run-fmUVYwIY` is already reported PASS
for its old gate set (7/7 store, 6/6 frontier, 1/1 CLI,
30/30 ledger, 9/9 binder, original two Lean kernels,
14/14 adversarial controls); its local artifacts were not
committed and are not presumed inspected.

## One local run

```sh
cd /path/to/dashi_lean4
SLR_ROOT=/path/to/slr DATABASE_URL="$DATABASE_URL" \
  bash scripts/run_gwb_native_maxcut_packet.sh
```

New run files:
`native-named-topic-inference.json`,
`lean-named-topic-policy.log`,
updated `joint-evidence-ledger.json`, original
`native-inspection.json`, `native-frontier.json`, and the
original typed-binding worksheet. The script preserves prior
untracked runs.

**Expected linguistic endpoint:** `he → source-local Bush`
under explicit `slr:policy:source-local-repeated-person-topic:v1`,
without a human S29 action. That is not yet a kernel proof of
universal English coreference or a trusted reviewed-policy admission.
Any failure to derive must be analyzed against the actual persisted
focus morphology, source-group count and quotation scope,
not papered over with a hardcoded Bush answer.

## P0 after this positive run

(1) Treat the local interpretation as a genuine **computed result**,
not a queue receipt. If the registered deterministic policy is
approved for semantic admission, the SLR original owner should issue
a separate, source-bound `DeterministicReviewedPolicy` semantic
receipt with exact candidate refs, policy hash, source revision and
reversible dependency ledger. No human S29 button is intrinsically
required; if the relevant typed referent set is ambiguous or
truncated, keep the stronger absolute uniqueness claim open.

(2) For *this* original actor, separately pin and check original
JMD Q23505 EntityData, independent source statements including
Reagan/1980 and reviewed book-actor↔Q23505 alignment.
`Q207` is a mandatory mismatch-negative: it is George W. Bush,
a different article and source scope.

(3) Prove one real consumer-relevant source answer with its exact
policy/evidence/retraction surface and one independently imported
JMD property statement, not a claim about all English readings
or all 51 QIDs. Then scale the versioned source-local policy to
the 3,078 pronoun-like production candidates and measure
positives, ambiguity, and residuals. Do not create another
C4.xx inspection-gate series.
