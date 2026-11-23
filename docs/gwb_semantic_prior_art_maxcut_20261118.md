# GWB semantic-output maximum-cut: original-repo prior-art audit
**Date:** 18 November 2026  
**Target:** `chboishabba/dashi_lean4` PR #112, pinned GWB Wikipedia `enwiki-revid:1385850169`  
**Original reference dataset:** `artifacts/gwb-semantic-proof/slr-rust-semantic-expansion.json` (643 sentence rows)  
**Status:** owner audit + diagnostic refinement implemented; **no canonical producer replaced, no review authority promoted**.

## Corrected diagnosis

The previous assessment incorrectly generalized from a deliberately limited
SLR **experimental candidate projector** to the maturity of the full
SLR/ITIR/SensibLaw/Agda/world/AO stack. That generalization is invalid.
The original runtime already implements parser annotation carriers,
declarative semantic reductions, set-valued reference binding, reversible
document identity evidence, provenance-aware event observations, chronology
and bounded world-model review. Whether each facility is *executed and
source-aligned in this exact 643-sentence PR #112 run* is a different question.

`UnsupportedDependency` is the name of a coarse **Rust projection residual**,
not "unsupported by the project", an NLP parse failure or missing meaning.
Its production point is the project's deliberately limited
`sl-semantic-expansion` observation vocabulary.

For the original small receipt:

| Quantity | Actual count | Meaning |
|---|---:|---|
| Parser token sites | 17,547 | Complete source parser inventory |
| Syntactic candidate sites | 4,190 | Original Rust candidate vocabulary |
| Clause alternative sites | 814 | `Condition/Temporal/Qualifier` diagnostic choices |
| Unsupported sites | 12,543 | Original parser labels omitted by this *particular* projection |
| Total residual entries | 15,595 | 12,543 unsupported **plus** 3,052 further open diagnostic entries |

**Correct token identity:** `17547 = 4190 + 814 + 12543`.
**Correct residual identity:** `15595 = 12543 + 3052`.
The 3,052 other residuals refer to candidates and alternative sites, so the
15,595 residual count is **not** an independent partition of tokens.

The original SLR parser fixture for this pinned source is ignored at
`.dashi/gwb-source/slr-record.json`. The committed Rust native receipt
retains unsupported *token ordinals* but not the original `dep` label
for each of the 12,543 sites. A complete fine histogram cannot be honestly
computed from the native JSON alone. **New exact-source auditor:**
`tools/audit_gwb_original_dependency_fibre.py`. It joins
`sentence_index/token_ordinal` to original
`pnf_candidates[].dependency_rows[].dep`, checks revision and digest,
requires an exact token-site partition, rejects duplicate, foreign or
promoted records, and emits the fine-label counts and Agda v0.4 work routes.
The script **does not run a new parser**.

### Pre-existing Agda fine residual prior art (do not reimplement)

- `chboishabba/dashi_agda/DASHI/Cognition/PNF/SensibLawGWBv01ResidualFrontierCertificationV03Exact.agda`:
  prior 10-document / 41,044-sentence GWB v0.3 certified **706,246**
  residuals, **533,994** coarse unsupported entries, zero projection
  failures; explicitly says counts are *not semantic quality*.
- `.../SensibLawGWBv01UnsupportedResidualCertificationV04Exact.agda`:
  exact **28-label spaCy unsupported fibre**, zero parity failures,
  same fine fibre direct/reference, and no additional semantic authority.
- `.../SensibLawUnsupportedResidualRelativeFibreExact.agda`:
  `coarsePlusDependencyLabelReopensDiagnosticState` via the existing
  `DASHI.Core.CoarseFineRelativeFibreExact` owner.
- `.../SensibLawUnsupportedDemandRoutingExact.agda`: six work routes,
  **surfaceStructural / relationAttachment / nominalStructure /
  predicateAction / coordination / parserUnknown**; not legal meaning.
- `.../SensibLawGWBv01RuntimeCertificationValidation.agda`: existing
  certified run's coarse histogram and admission boundary validation.

**Important:** these v0.3/v0.4 counts describe a *different, larger*
10-document GWB tranche. Never substitute 533,994 for 12,543, nor
blindly assume its set of seen dependency labels equals the smaller
article's. The new auditor reports
`labels_outside_historical_v04` explicitly.

## Source-linked issue → prior art → integration action

### GWB-A01 — "Unsupported" overstates missing work
**Observed:** 12,543 coarse unsupported entries, 80.43% of 15,595
residuals; sampled labels include `ROOT, compound, punct, det, amod,
appos, pobj, conj, cc, advmod, nummod, aux, poss, case, mark, dep,
auxpass, nmod`. This is a **sample**, not the complete histogram.

**Actual prior art:** original SLR
`dashi_agda/tools/slr-discourse-reconstruct/slr_wikipedia_article_pnf_world_producer.py`
retains `dep`, `head_i`, `idx`, `pos`, `lemma` and local
`dependency_rows`; its `ROLE_DEPS` already covers `ROOT`,
coordination, auxiliary, subjects, objects and clauses. DASHI Agda
v0.4 stores the fine labels and routing; SensibLaw
`src/language/graph.py` retains immutable annotation layers.

**Resolution:** **not a grammar-implementation task**. Run the exact
original-source fine audit and compare the narrow observation surface
against existing SLR and SensibLaw carriers. Keep the full parser
annotation graph as source provenance. Mark as integration/coverage
debt only when canonical reducers fail to consume an *expected*
producer observation. Never replace unsupported with a fabricated
semantic interpretation.

**Acceptance:** original token partition and sum of per-label histograms
`=12543`; all source indices/offsets preserved; v0.4 route and
out-of-v0.4 labels reported; no source or authority change.

### GWB-A02 — Predicate/coordinated-action loss
**Observed:** sentence 9 ("As governor, Bush sponsored ... increased
... set ... reformed ...") has a questionable original `amod` parse
for `increased`; the narrow projector does not emit a complete
four-predicate claim. Sentence 18's `had` is `conj` and intentionally
not a free-standing source assertion.

**Actual prior art:** `SensibLaw/src/language/semantic_reductions.py`
(declarative predicate/modifier/conjunction relations);
`dashi_agda/DASHI/Cognition/PNF/SensibLawRoleTransitionManifoldExact.agda`;
`dashi_agda/tools/slr-discourse-reconstruct/src/bin/slr-role-transition.rs`;
`SensibLaw/src/policy/operational_corpus_compilation.py`.
Canonical source producer also retains `ROOT/conj/cc`.

**Resolution:** feed the actual original dependency graph through
existing relation and role-transition owners; compare with current
`GwbTypedFibre` projections. If the input spaCy `amod` is an actual
parser error, fix/review **upstream parse** separately from semantic
reduction, with original source and parser-model provenance. Preserve
conjunct's governing/quotation/claim scope and don't promote it.

**Acceptance:** exact per-predicate source spans, shared subject
inheritance only under licensed coordination, no attribution/scope
collapse, negative case `possessed ... and had` under `citing claims`.

### GWB-A03 — Nominal phrase and name loss
**Observed:** sentence 5 retains `Welch` as a syntactic object but
not the full "Laura Welch" nominal phrase, nor the `librarian`
apposition.

**Actual prior art:**
`SensibLaw/docs/architecture/PROOF_RELEVANT_IDENTITY_ACCEPTANCE.md`
and migrations **077–080**: parser-grounded apposition, PERSON/title
and alias evidence, exact sentence reference, unique PNF object
anchor, admission with provenance; `src/pnf/binding_candidate_sets.py`.
`docs/planning/pnf_binding_candidate_sets_20260718.md` documents
source-canonical binding and the non-identity boundary.

**Resolution:** project canonical span/phrase evidence into the same
source object and use existing admitted witness pathway. A
`compound` label alone is not an external person identity.

**Acceptance:** reviewed exact-span noun phrase; `appos` witness
connected via existing migration 078; negative: surname alone must
not become a person-QID identity.

### GWB-A04 — Reference/entity confusion
**Observed:** 1,146 `Role(Actor)` entries include passive subjects
and pronouns; 62 `ReferenceRelation` residuals. "He" and "it" in
sentence 18 are distinct grammatical candidates, not historical actors.

**Actual prior art:** `SensibLaw/docs/planning/pnf_binding_candidate_sets_20260718.md`
and `PROOF_RELEVANT_IDENTITY_ACCEPTANCE.md` (candidate set,
structural accessibility, typed anaphora, `resolved_unique`,
retractable Level-3 substitution). Original Agda
`DASHI/Interop/SLRWorldModelSuiteConvergenceRoadmapExact.agda`
already assigns identity review to SensibLaw.

**Resolution:** retain passive patient/agent role distinction and
call the original binder, not an `Actor`-name-to-entity lookup. An
accepted identity must reference its original span and source graph.

**Acceptance:** same-source source-token/PNF object binding and
proof-bearing singleton on selected original GWB examples, with plural,
ambiguous and passive agent negative controls.

### GWB-A05 — Date and document-structure coupling
**Observed:** sentence 5 year 1977 is `pobj`; sentence 18 year
2003 is `nummod`; sentence 131 mixes heading
"Presidency (2001–2009)" with the following paragraph.

**Actual prior art:** `SensibLaw/src/text/sentences.py` has
paragraph-aware canonical sentence units; `src/wiki_timeline/article_state.py`,
`scripts/wiki_timeline_aoo_extract.py` and
`docs/wiki_revision_harness_contract_v0_1.md` retain article
revision, state and event/epistemic deltas. Agda
`DASHI/Core/TypedIntervalEventTransitionExact.agda`,
`DASHI/Cognition/PNF/EventAlgebra.agda`.

**Resolution:** compare the *same pinned source* normalized sections,
headings and sentence units against the narrow article parser.
Reconcile source spans before event-time use; `year` lexical occurrence
is not automatically event chronology. A heading range scopes the
section, not an arbitrary following predicate.

**Acceptance:** no cross-heading attachment without reviewed structural
bridge, source spans exact, 1977 tied to the marriage event only with
valid attached evidence, 2003 attached to the right event.

### GWB-A06 — Clause alternatives and epistemic scope
**Observed:** 814 alternative sites all carry the generic triad
`Condition/Temporal/Qualifier`. This is a conservative
unresolved-site template, not 814 independently fitted meanings.

**Actual prior art:** `SensibLaw/src/language/semantic_reductions.py`,
`DASHI/Interop/SLRSemanticWorldClosureExact.agda`,
`Docs/ITIRReopenableEvidenceHyperformalism.md`,
`DASHI/Core/ProvenanceBearingQuotient` and
`DASHI/Core/DynamicalQuotientSafety` owners.

**Resolution:** consume source-anchored alternative/candidate
evidence through the existing semantic fibre and ask which *consumer
answer* differs. Do not force a clause interpretation where source
evidence is insufficient; do not flatten "citing claims" into a
historical factual assertion.

**Acceptance:** branch-specific source and governing-clause references;
consumer-relative invariant answers permit closure without global
unique interpretation; differing answers remain unresolved.

### GWB-A07 — NER zero is not suite-wide NER incapability
**Observed:** old 643-sentence article receipt lists zero
`ner_people_mentions` and zero `ner_date_mentions` while retaining
2,620 proper-noun tokens and 311 literal-year tokens.

**Actual prior art:** `SensibLaw/src/language/graph.py` and
`docs/architecture/PROOF_RELEVANT_IDENTITY_ACCEPTANCE.md` map
parser-backed PERSON spans into exact apposition/name evidence.
Original SLR source producers explicitly pin parser/model capability.

**Resolution:** audit **which** parser/NER components ran for this
source revision. Do not infer that the suite has no NER from these
counter fields. Distinguish unavailable annotation layer from
zero detections and from rejected named-entity identity.

**Acceptance:** parser capability/model receipt, counts for actual
NER annotation layer (if available), source-span/alignment parity;
no NER-less `no entities` assertions.

### GWB-A08 — M12/S28/World/AO are not missing semantic engines
**Observed:** PR #112 manifest says `production_db_s28=NOT_TESTED`
and `reviewed_semantic_transports=NOT_TESTED`. These are
**unexecuted welds**, not proof of nonimplementation.

**Actual prior art:**
- `SensibLaw/src/policy/world_model.py` is the shared generic
  `sl.candidate_world_model.v0_1` carrier for entities, claims,
  relations, events, timelines, provenance, residuals and authority;
- `SensibLaw/scripts/wiki_timeline_aoo_extract.py` is a Wikipedia
  actor/action/object article projection;
- `SensibLaw/docs/wiki_revision_harness_contract_v0_1.md` has
  source-revision and epistemic change records;
- `SensibLaw/docs/planning/direct_delta_compiler_convergence_20260829.md`
  specifies the **single** production semantic authority;
- `dashi_agda/DASHI/Interop/SLRWorldModelSuiteConvergenceRoadmapExact.agda`
  explicitly assigns ITIR canonical compilation, SLR discourse
  reconstruction, SensibLaw review/promotion, TiRCorder contested
  narrative, StatiBaker append-only state and DASHI proof boundaries;
- `dashi_lean4/.../DbSourceProducer.lean` has exact M12 and S28
  source-ancestry checks.
- `dashi_agda/tools/slr-discourse-reconstruct/slr_article_pnf_semantic_weld.py`
  already joins source PNF candidates to the multilingual semantic
  closure/gap carrier without promoting claim truth.

**Resolution:** run the original owner on the pinned source, then
weld by exact source/revision/PNF factor IDs and checked review
receipts. Do not build another world graph, run standalone
semantic-rewrite rules, or make Wikidata mandatory.

**Acceptance:** original P5–P8 same-source receipts actually
instantiated with the current SensibLaw/ITIR/AO owners; imported JMD
used **only** for independently aligned Wikidata-KB consistency
(P9/P10). Full event/identity/time authority remains conditional
until verified original receipts exist.

## Execution contract (no TAR)

```bash
# after pulling PR #112:
bash scripts/run_gwb_maxcut_acceptance.sh --proof-only
# or explicit fine diagnostic, same original ignored fixture:
python3 tools/audit_gwb_original_dependency_fibre.py \
  --native artifacts/gwb-semantic-proof/slr-rust-semantic-expansion.json \
  --slr .dashi/gwb-source/slr-record.json \
  --output .dashi/gwb-audit/unsupported_dependency_fine.json
```

**Do not treat green Lean builds, receipt source hash, negative controls,
or fine label parity as a positive claim about complete semantics.**
The decisive positive end-to-end test is the *original production
SLR/SensibLaw/ITIR/AO projection of this exact source* against the
narrow receipt, using its existing admissible review/provenance
contracts. The P5–P10 Lean interfaces can then be inhabited with
those verified owner-produced witnesses, not fresh assertion flags.

### Provenance and authorship

SLR integration and source handoff: chboishabba/DASHI.
Original SensibLaw parser/PNF identity and world-model implementations:
SensibLaw repository owners. DASHI fine residual and router theorem
owners: `dashi_agda`. JMD Wikidata KB and property consistency
theorems: original `meta-introspector` RequestProject import.
No attribution of JMD ontology consistency as author of article
semantic interpretation.

## Executable original-source witness checks

`tools/audit_gwb_original_semantic_cases.py` now reopens the exact
four **actual** source/token witnesses embedded in the committed native
receipt (sentences 5, 9, 18, 131) and fails if the cited parser labels
or source spans have changed. For the Iraq sentence it also checks that
the `overthrow`, `citing` and `possessed` clause positions retain
their alternative sites; for the Presidency example it asserts the
original heading/paragraph newline boundary is visibly inside the
single parser sentence. It emits a *problem inventory* with original
source text and existing owner paths, **not** a hand-labeled gold
interpretation or a claim that the canonical owner was executed.

The unified acceptance script executes this check with the exact
committed Rust JSON, alongside the nine negative controls for the
fine-label rejoin, and writes the generated original case diagnostics
into the **ignored** `.dashi/gwb-audit/` location. The complete
12,543-label breakdown additionally requires the original ignored
SLR JSON from the already passing full run.

This code and prior-art mapping are committed, but the new negative
test suite and full original-source fine audit have not yet been
locally executed with the operator's pinned source fixture. This
is deliberately distinct from the previously verified P4/P5–P10
Lean kernel receipts.


## C4.04c.7–8 — native multi-document semantic population

Operator receipt at bedad7427: 29,043 general mentions, 6,678 batch
bindings, 17,202 reconciliation review-item rows, 9,121 matching global
pressure candidates. The installed schema uses semantic.review_item and
semantic.review_receipt, not the later review-delta-fibre table.
These are candidate populations, not admitted semantic identities.

C4.04c.8 offline implementation:

```bash
python3 tools/audit_gwb_native_entity_fibres.py \
  --input .dashi/gwb-relation/native-semantic-observation-v2.json.gz \
  --output .dashi/gwb-relation/native-entity-audit-v1.json
```

Replay lexical fingerprints and original occurrence references; compare
PNF and L2 factors; report pronoun/role census, repeated lexical fibres,
same-statement preceding NER candidates, and revision-specific review
semantic-reference overlap. The latter is not run-level review parity.
The compact result is bound to the input artifact SHA-256.
No database or parser is invoked. Actual full receipt execution remains
pending; binary retrieval through the connector returned empty content.
Python/Rust Unicode lowercase parity is subject to the observed replay.

C4.04c.8a–d/g: implementation present, native acceptance pending.
C4.04c.8e: bounded candidate search only; exact original statement
literal and discourse accessibility are unpaid. C4.04c.8f and empirical
same-fingerprint/different-referent witness remain open. Reuse the
SensibLaw binder and reviewed identity acceptance owners above; do not
promote same-statement NER proximity into identity. C4.05/C5/C6 remain open.
