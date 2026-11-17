# GWB real-source semantic adequacy: negative-control findings

**Input:** user's exact seven-member `gwb_article_proof.tar`; enwiki
`1385850169`. Read-only audit, not an NLP producer or semantic admission.
The archive already passed exact source/P0b reconstruction checks.

## The question is consumer sufficiency, NOT parser integrity

A query q factors through a projection O only if equal O-values force equal
q-values across the relevant admissible readings. We must not assume
source-sentence PNF, actor surface or a scope label is a sufficient O for
all event/identity/temporal consumers.

## Counterexamples in the actual source

1. **Nested conjunction scope (57 instances).** Each of 57 projected
   `conj` verbs whose immediate parent has dependency
   `acl|relcl|ccomp|xcomp|advcl` is nevertheless labelled
   `unresolved-source-assertion`. Sentence 18:
   `claims -> possessed (acl) -> had (conj)`. Both predicates belong
   to a reported proposition. `had` is not independently licensed as
   world occurrence. The label remains unresolved, so this is not proof
   a bad world fact was inserted. It is a coarse-observer failure.
   An explicit scope-label nonfactorability witness is the pair:
   `had` (sentence 18, embedded parent) and `set` (sentence 9,
   ROOT parent), both assigned `unresolved-source-assertion`.
   The consumer 'does this predicate have an embedded dependency parent?'
   differs despite the identical scope label. The ORIGINAL dependency
   graph does preserve the distinction.

2. **Syntactic agents are not semantic actors.** 59 event candidate
   actor slots have surface `by` with a `agent` dependency. Example:
   `The company was hurt by decreased oil prices...` The `by` token
   is not a participant identity. Direct head-edge extraction is not
   adequate for the 'which actor?' consumer without retaining its
   prepositional complement, scope and candidate entity alternatives.

3. **Single main PNF predicate is not a full event summary.**
   419 of 643 SLR sentence candidate records have MORE projected action
   candidates than their `predicate_lemmas` lists. Difference totals
   859 across those sentences. Sentence 18 PNF predicate is `order`,
   while the candidate action list has `ordered, overthrow, citing,
   possessed, had`. A main-predicate consumer may close; an all-event
   consumer cannot factor through that field alone.

4. **Sentence/paragraph boundary interference.** 57 SLR sentence
   records cross original HTML-derived heading/paragraph blocks.
   Sentence 131 joins `Presidency (2001–2009)` to a following paragraph
   with `outlined`. Co-sentence years cannot date that action.

5. **Year mentions are not event temporal assertions.**
   311 lexical years: 161 `nummod`, 122 `pobj`, 20 `appos`,
   7 `conj`, 1 `npadvmod` among original token dependencies.
   226 years share a sentence with at least two projected events;
   6 share a sentence with zero. Sentence 5 `in -> 1977` attaches
   syntactically to `married`; sentence 18 `2003` modifies
   `invasion`. Consumer-specific temporal attachments remain to prove.

## What the TAR DOES NOT contain

There are **no materialized GWB** `SemanticFibreLedger`,
`FibreElement` alternative readings, `SemanticTransport` proofs,
consumer-specific H3/H6/H9 closure receipts, S28 reviewed joins or Lean
kernel output. The TAR contains P0b mention-shape *candidates* and
original syntax, not admitted semantic fibres.

Existing `SensibLaw/src/pnf/semantic_fibres.py` has `evaluate_fibre`,
which may return `outcome=satisfied` based on supporting elements
while `coverage_complete=False`. Its serialization separately has
`truth_closed=False`. Do not mistake this local validation status
for Agda's all-live-readings `ConsumerClosedOnSemanticFibre`.

## Required semantic-machine acceptance

Reuse existing Rust-first pipeline and original semantic/fibred runtime,
not a new Python producer. Emit the current GWB source's actual typed
coordinates, fibre elements, alternative readings, transports, scope and
query-indexed residual/closure receipts, then rerun these five
real-source discriminators. A positive answer must factor through the
actual retained observer, with an independently checked kernel theorem.
The current archive cannot establish that step.

**Locally executed:** read-only full source and event graph evaluation.
Script and machine-readable evidence are available in the current
conversation as `gwb_fibre_logic_audit.py` and
`gwb_fibre_logic_audit_results.json`. This is a negative adequacy
regression for the flattened projection, NOT a claim that the existing
unexecuted hyperfabric itself is unsound.
