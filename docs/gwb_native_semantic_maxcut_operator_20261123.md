# GWB semantic maximum cut — one operator run

Date: 2026-11-23. Source owners: original SLR PR #78, original
SensibLaw typed binding reference, dashi_lean4 PR #112 + original JMD
meta-introspector. This packet is the **integrated M1–M3
source-bounded unresolved baseline**. It is not an S29 human review,
an admitted referent, a GHWB/Q23505 external identity, a reviewed
Wikipedia property alignment, or a complete 51-QID world theorem.

## First command: one targeted local acceptance

Use the original SLR and dashi_lean4 PR checkouts; both must be current:

\`\`\`sh
cd /path/to/dashi_lean4
SLR_ROOT=/path/to/slr \
DATABASE_URL="$DATABASE_URL" \
  bash scripts/run_gwb_native_maxcut_packet.sh
\`\`\`

Only for more than one fully matching *persisted* native parser run,
set \`GWB_NATIVE_PARSER_RUN_REF\` to the exact run from the emitted
\`original-parser-runs.json\` and repeat. No fallback to a different
source, no parsing again, no nearest-token inference.

To also run the existing, independent Q207 Wikipedia/JMD conditional
proof lane, set \`GWB_RUN_WIKI_P10=1\`. Its original source and EntityData
fixtures must already exist for the optional property/graph checks.
\`GWB_WORLD_GRAPH_JSON\`, \`GWB_JMD_ENTITY_CACHE\`,
\`GWB_Q207_ENTITY_JSON\`, \`GWB_WIKIDATA_OFFLINE=1\` are passed to
the *existing* \`scripts/run_gwb_maxcut_acceptance.sh --proof-only\`
when configured. For an independently recorded original Q207 minimal
kernel check, pass \`GWB_Q207_KERNEL_LOG=.../original-q207-lean.log\`
containing the exact \`GWB_Q207_MINIMAL_KERNEL_OK\` emitted by the
minimal JMD source-field runner. A freeform \`ACCEPTED\` status
string does not pay this proof.

## What the run actually does

1. Original SLR \`cargo test --lib native_antecedent_review\`, new
   \`--lib native_antecedent_frontier\` and original native CLI test.
2. Reopen original C4.12 PostgreSQL S29/source row (book digest
   \`7ff2ec8...\`) and original five preceding+focus sentence parser
   regions, with actual parser product keys, source spans, tokens,
   morphology/dependency and NER. An original run must cover all
   five regions. Reject incomplete, wrong-revision, missing-product,
   forged-focus or changed \`Bush\` source tokens.
3. Emit separate parser nominations for PROPN, NOUN, PRON and NER
   spans *before* the focus. Do not filter by proximity; retain all
   observed rivals. The output explicitly marks morphology and
   quotation/accessibility \`UNASSESSED\` and does **not** assert
   exhaustive semantic readings, identity, QID, or truth.
4. Run Python 24-case fixture regression and the new independent
   Lean theorem+frontier checker. Lean proves the original-level
   retention/retraction contract, source/revision mismatch exclusion,
   consumer-coverage/invariance implication and an explicit
   counterexample refuting a false consumer licence. The runtime
   marker \`GWB_NATIVE_FRONTIER_BOUNDARY_KERNEL_OK\` pays only
   exact *structural/bounded* frontier validation.
5. Recheck the original Rust inspection and parser frontier in
   Python, including Unicode original source substrings and
   explicit source/QID separation; run 14 adversarial mutations
   on the real inputs. Emit a two-source ledger with all **unpaid**
   semantics explicitly open and a review worksheet for all
   original source-backed parser nominations.
6. Optionally run original JMD/Q207 conditional P5–P10 proof lane.
   No automatic transformation of a GHWB-book pronoun into the
   pinned Wikipedia George W. Bush Q207 entity.

The script creates a **fresh** project-local
\`.dashi/gwb-relation/m1-m3-maxcut/run-XXXXXXXX/\` directory
for every run. Previous untracked output, existing \`Cargo.lock\`,
other SLR binaries and archives are preserved.

Outputs inside that run include:

- \`native-inspection.json\`: C4.12 exact original store review state
- \`original-parser-runs.json\`: eligible original source-matching runs
- \`native-frontier.json\`: bounded original parser nominations
- \`lean-frontier-kernel.log\`: targeted independent Lean certificate
- \`joint-evidence-ledger.json\`: book and Wikipedia *distinct* status
- \`original-antecedent-review-worksheet.json\`: actual rivals, all unreviewed
- optional \`wiki-p10-conditional-kernel.log\`, \`jmd-world-proof-report.json\`

Positive command marker:
\`M1_M3_MAXCUT_BOUNDED_PACKET_OK\`.
This is a bounded source **inventory** result, not a proof of
\`he \mapsto Bush\`. If no unique original parser run covers five
regions, the correct result is a fail-closed integration residual:
the \`original-parser-runs.json\` explains which original producer
needs its native region/ancestry weld.

## Optional actual typed-binding weld (original owner; not a duplicate)

If the original full-book semantic annotation/PNF graph is available,
the **same** runner can invoke the original SensibLaw
\`src.pnf.binding_candidate_sets.compact_binding_artifacts\`.
Set:

\`\`\`sh
SENSIBLAW_ROOT=/path/to/SensibLaw \
GWB_ORIGINAL_BINDING_ARTIFACTS=/path/to/original-full-book-pnf-and-annotation-artifacts.json \
SLR_ROOT=/path/to/slr \
DATABASE_URL="$DATABASE_URL" \
  bash scripts/run_gwb_native_maxcut_packet.sh
\`\`\`

The bridge (tools/gwb_original_binding_interop.py) requires the
original full canonical text **exactly** hash to the native book
\`7ff2ec8...\`; the original graph document ref must match the SLR
document; the original parser token index must reconstruct the exact
\`he\` factor span; all candidate factor spans must precede the
reference in the original book; and the binder must actually use
\`direct_observation_graph_index\`, not the legacy pairwise fallback.
It preserves original binder references, accessibility paths,
morphological compatibility state and exclusion summaries, without
claiming any one member was uniquely reviewed. It creates
\`original-typed-binding-crosswalk.json\` and lets the main ledger pay
**only** exact source crosswalk, never identity.

If the original book graph is absent or has a different source
manifestation, **leave this optional lane off**. Do not fabricate
one from the earlier 643-sentence Q207 article, the world-level
timeline or the numeric SensibLaw legacy GWB corpus.

All source-written files were pushed but **not executed** from this
connector environment. The first real Cargo/PostgreSQL/Lean receipt
belongs to the operator run. Source-check and bound-check failures
are meaningful constraints; do not fill in fake data to make them pass.

## Authority and next source-owner implementation cut

The selected \`Bush\` at [4310,4314) in original book sentence 22
and \`he\` [4534,4536) in sentence 23 share original source.
But structural POS/NER and source precedence are **not** original
SensibLaw \`resolved_unique\` typed binding or a human semantic review.
The original reference owner is
\`SensibLaw/src/pnf/binding_candidate_sets.py\`
(\`compact_binding_artifacts\`) with accessibility paths, quotation
scopes, morph conflict policy, candidate-set identity and explicit
unresolved type. Its full factor/annotation graph *must* be connected
to original SLR native factor IDs before positive resolution; this
script does not guess that bridge from token similarity.

The S29 item
\`review-item:native-antecedent-candidate:sha256:25e927f12a0092fbed143669f6a0621fa004636d728074d576275b361da8f7d1\`
remains Pending until an authorized operator actually reviews it.
Even S29 Accepted remains only workflow state. An independently
validated semantic antecedent receipt needs exact original
same-source candidate set, reviewed competing exclusions, actual
accessibility witness, policy, reviewer and reversible Level-3
identity projection. If genuinely unsupported, a checked
\`UNRESOLVED_REVIEW_REQUIRED\` consumer answer is correct.

The Q207 JMD kernel source-fields check remains separate;
Q23505 world identity may not be inferred from the title or \`Bush\`
surname. For a property-level claim, require original JMD
\`PKB.supportsB_iff\`/KB checker + independently reviewed original
book/article property statement alignment and exact source revision;
this packet does not forge the premise or claim historical truth.

This **one packet replaces further isolated C4.xx discovery tools**.
The meaningful next advance is full typed binding + governed human
antecedent adjudication, then a real consumer-scoped answer and a
pinned JMD property proof, not another JSON count report.
