# GWB acceptance correction: original SLR producer first (18 November 2026)

## Problem that required this patch

PR #112 had made the intentionally experimental
`sensiblaw-semantic-expansion` Rust observer the mandatory data producer
of `--full` acceptance. That observer classifies 12,543 original
source parser tokens as `UnsupportedDependency`, even though the
source-bearing SLR/ITIR/SensibLaw pipeline retains their original
dependency labels, heads, offsets and semantic-reduction facilities.
Consequently, prior P4 and P5–P10 acceptance proved checks about an
artificially narrow observer, **not** the whole original producer.

This was the wrong execution default. Do not mistake a proof that the
restricted observer matches its source data for a proof that it is
the canonical or maximally informative SLR interpretation.

## Repair: one original producer, proof consumer only

Canonical input, *already emitted by the original SLR pipeline*:

- `.dashi/gwb-source/article.txt`: exact revision-pinned article bytes
- `slr-record.json`: `slr-source-unit-pnf-record-v1`, full dependency
  rows, original token/head/offsets, source identity and parser receipt
- `article-candidates.json`: original SLR-based article predicates,
  grammatical roles, source span/year/section and textual-order evidence,
  `slr-jmd-wikipedia-article-candidates-v1`
- `gwb_sensiblaw_p0b_mention_licences.json`: source-indexed P0b
  mention-eligibility receipts

The new `tools/gwb_canonical_slr_acceptance.py` checks these
actual original records and publishes **all original dependency-label
counts**, original predicate/actor/patient counts, source sections,
source-only year occurrences, and P0b counts. It preserves all
source-carrier digests. No new NLP/parser/semantic producer was added.

The original `WikipediaArticleProof.checkProjection` and
`GwbRealSource.sourceBoundCollision?` Lean owners check source-bound
predicates, complete direct grammatical role children, scope
nonfactorability, original sections and dates, source hashes and
no false occurrence/identity authority. Five source-bound adversarial
mutations must be rejected *by the intended Lean checker*.

**The new canonical path does NOT invoke**
`sl-semantic-expansion`, `gwb_slr_fibre_probe.rs` or `cargo`.
The old full suite remains accessible only with an explicit
`--legacy-rust` option; it is not a semantic acceptance prerequisite.

This is a correction to the PR's source-of-truth selection. It does
not invent new actor identity, event truth or cross-sentence review
witnesses. Original SensibLaw/ITIR/AO review and production results
should be transported separately by their existing producer
contracts, not reconstructed from Rust residuals.

## Operator commands

```bash
cd /home/c/Documents/code/dashi_lean4
git pull --ff-only
bash scripts/run_gwb_maxcut_acceptance.sh --full
```

**No `SLR_ROOT` needed for the canonical path:** the original SLR
source records are already in the operator's ignored
`.dashi/gwb-source` from previous successful acceptance.

Outputs, ONLY after verification:

```text
artifacts/gwb-original-slr-proof/proof_run_manifest.json
artifacts/gwb-original-slr-proof/original-source-inventory.json
artifacts/gwb-original-slr-proof/original-scope-and-mention-audit.json
artifacts/gwb-original-slr-proof/article-source-proof.log
artifacts/gwb-original-slr-proof/semantic-scope-proof.log
artifacts/gwb-original-slr-proof/rejected-*.log
```

No TAR created/modified, no overwrite of historical
`artifacts/gwb-semantic-proof/`, and no deletion of operator
untracked files. The command uses the pinned Lean 4.28.0 environment.

For regression-only comparison with the historical experimental
observer:

```bash
SLR_ROOT=/path/to/slr bash scripts/run_gwb_maxcut_acceptance.sh --legacy-rust
```

## Proof and scope accounting

- **Closed by this source correction, once locally passed:** canonical
  original SLR-to-Lean source transfer, source/predicate/role
  enumeration, article heading and temporal lexical evidence, exact
  source identities, adverse mutation rejection. No dependency labels
  are lost in the acceptance inventory.
- **Not automatically closed:** reviewed multi-sentence semantic
  identity, event-equivalence, temporal interpretation, production-live
  semantic consumer fibres, or independently reviewed external JMD
  article-property equivalence.
- **Already implemented in other owners:** SensibLaw PNF identity
  evidence migration family 077–080, set-valued bindings and annotation
  graph; DASHI Agda GWB v0.4 fine labels and six-route work routing;
  ITIR/SLR discourse and predicate source carriers; SensibLaw
  candidate world / Wiki article AOO, with JMD optional and downstream.

Those gates must be answered with source-specific original-owner
receipts, not by assigning semantics to parser labels or consulting
Wikidata as an article interpreter.

## Acceptance status

This patch is source-written and pushed to PR #112. The new canonical
full run has **not** been executed in the author's environment against
the original ignored fixtures or the pinned Lean compiler. Prior green
P4/P5–P10 results remain receipts of the historical restricted probe
and are not relabeled as canonical semantic acceptance.


## 2026-11-20 — current native identity integration boundary

The native reconciliation at 5ebc5f5b3 establishes candidate evidence but no
persisted document-local identity or QID binding; zero review receipts and
no matching legacy parser source. Native occurrence replay at cc9eadbf6
passed 29,043/29,043 with zero missing. See the controlling [C4.09 automatic
proof roadmap](gwb_automatic_proof_maxcut_20261117.md). Reuse existing
SensibLaw typed binding logic through an explicit source-coordinate adapter
while retaining SLR Rust as production parser/PNF owner. No legacy
benchmark on unrelated data, second parser, identity promotion or new
kernel acceptance is implied. Original article proof scope remains separate.
