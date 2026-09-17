# Related work, and what the DASHI Agda bridge taught us

Two questions are answered here:

1. **What did we learn from the `chboishabba/dashi_agda` work (PR #555)?** —
   section 1, with each lesson traced to the Lean declaration that now carries
   it, and the three lessons that were *not* yet ported now formalized in this
   pass (§1.3).
2. **What existing work is this connected to?** — section 2, a map of the
   surrounding literature and standards for each pillar of the development, and
   what this project adds on top of it (§2.9).

Everything referred to in §1 as "proved here" is machine-checked and `sorry`-free
in this repository; `PORTING_NOTES.md` gives the module-by-module map.

---

## 1. What we learned from the DASHI bridge

### 1.1 What that work actually is

PR #555 (`Bridge complete James/Aristotle Wikidata Lean development into DASHI`,
155 files, ~25.7k added lines, open at the time of writing) is a *bridge*, not a
re-implementation. It takes a Lean Wikidata development as a fixed external
artifact — pinned by archive and per-file SHA-256 in
`third_party/jmdupont_wikidata_lean/SOURCE_MANIFEST.tsv` — and records, in Agda,

* which upstream theorem or checker is being relied on (`LeanTheoremContract`),
* how a *record* of such a result may be used inside DASHI, and
* which authority that record does **not** thereby acquire.

Its own statement of intent is explicit that the Agda side does not kernel-check
the Lean proof terms (`BRIDGE_INVARIANTS.md`, invariant 1). So the interesting
content is not the ontology mathematics; it is the **discipline for consuming
imported results**, expressed as a list of things the system must refuse to do.

That is the reusable lesson, and it is why the port re-derives the same
discipline over a real engine: in Lean the refusals can be *theorems about the
data* instead of conventions about receipts.

### 1.2 The eleven bridge invariants, and where each one now lives

The source states its discipline as eleven invariants. Nine of them are directly
renderable as statements about knowledge bases and evidence, and are proved here.

| # | Invariant (source wording, abridged) | Rendered in this project as |
| --- | --- | --- |
| 1 | The bridge does not kernel-check the imported proofs | *Dissolved by porting*: the results are re-proved in Lean here, so nothing is imported on trust. `Epistemic.SurfaceClaim.losslessness_always_holds` is the sharpest case — a receipt upstream, a theorem here |
| 2 | Source matching includes request identity and pinned hashes | `Epistemic.receiptState` takes `sourceMatched` as a *separate* coordinate from `accepted` |
| 3 | Accepted results become scoped supporting evidence only | `Epistemic.ScopedClaim`, `Epistemic.Certificate`; support is backed by `Certificate.holds_of_supported` |
| 4 | Absence is unresolved; only a certified negative may contradict | `receiptState_ne_contradicted`, `verdictState_eq_contradicted_iff`, `verdictState_notObserved` |
| 5 | Truthy query semantics is not epistemic truth | `Wikidata.IsTruthy` vs. `Wikidata.Example.truthy_does_not_determine_evidence`; `Epistemic.viewClaim_layer_irrelevant` |
| 6 | Cross-ontology conflict requires explicit opposing evidence | `Epistemic.conflict_requires_opposition`, `unresolved_left_never_conflicts` |
| 7 | Identity / external-ID / sitelink / lexeme results stay candidate evidence | `Wikidata.Identity.identity_does_not_entail_instance`; the bijection results are conditional on constraints (`functional_of_singleValue`, `injective_of_distinctValue`) |
| 8 | Diagnostics and pruning feed a review proposal, not an edit | `Epistemic.enact_eq_of_not_approved`, `enact_eq_of_unsupported` |
| 9 | Certified redundancy removal ≠ claiming a superclass is bad | `Epistemic.RepairOperation.removeRedundantSuperclass` vs. `removeBadSuperclass`, plus `enact_redundancy_proposal_preserves_subclass` |
| 10 | Toy worlds are not claimed to have been executed by the real engine | *Dissolved by porting*: `Wikidata.Examples` runs the real QID fragment through the real checkers, by `decide` |
| 11 | Truth/edit authority non-promotion on every surface | `Epistemic.importEvidence_eq` and the enactment theorems above |

**The general lesson.** Nearly every invariant on that list is a *negative*: a
statement that some inference is **not** licensed. That is unusual and it is the
part worth keeping. A formalization of an ontology naturally accumulates positive
results (this checker is exact, this projection is lossless); the failure mode in
practice is not a missing positive but an unlicensed one — a query artefact read
as truth, a missing edge read as a refutation, a diagnostic read as permission to
edit. Negative theorems are what stop that, and they have to be stated
deliberately, because nothing in the positive development forces you to.

### 1.3 Three ideas we had *not* taken, now ported

Re-reading the bridge for this pass turned up three constructions that the
earlier passes did not cover. They are the genuinely novel structural content on
the DASHI side, and they are now Lean modules.

#### (a) The four-cornered support square — `RequestProject/Epistemic/Tetralemma.lean`

The source insists (`TernarySynthesisLogicQualificationExact.agda`,
`RelationalLensSynthesisCore.agda`) that `bothSupported` and
`neitherEstablished` **must not be collapsed into one ternary middle value**, and
that aggregated support-plus-contradiction belongs in a separate qualification
lane rather than in the trit.

This is a real defect of the three-valued layer we had built, and it is now
stated precisely rather than asserted. `SupportSquare` carries evidence *for* and
*against* independently; its four corners are Belnap's carrier, ordered by how
much is known (`Knows`, with `merge` proved to be the least upper bound). Then:

* `collapse_importSquare` — the square refines the trit: collapsing a single
  imported verdict reproduces exactly `verdictState`, so nothing changes for
  single-source import;
* `collapse_not_injective` together with `eq_of_collapse_eq_of_ne` — the collapse
  loses information, and loses it in exactly one place: the conflict corner and
  the ignorance corner are identified, and no other pair is;
* `conflicting_iff_merge_bothSupported` — the cross-source comparison we already
  had *is* the merge of two squares: `Disposition.conflicting` holds precisely
  when the pooled square reaches the top corner;
* `merge_then_collapse_ne_collapse_then_merge` — hence the order of operations
  matters, which is the operational content of the source's warning: pool
  evidence on squares, collapse only for display;
* `importSquare_ne_both` — and a single source can never reach the top corner on
  its own, so conflict is always a statement about two sources.

The meta-status coordinate (`MetaStatus`, `Qualified`) is the same idea one level
up: *why* a claim is indeterminate is not recoverable from the corner, and
`Qualified.scopeExceeded_ne_contradicted` records that out-of-scope is not
refutation.

#### (b) View families and lens transitions — `RequestProject/Epistemic/Lens.lean`, `RequestProject/Wikidata/Lens.lean`

`RelationalLensSynthesisCore.agda` separates the *latent object* from the family
of *projections* of it, and requires that a lens transition exist only when an
explicit two-sided transport has been supplied — "merely comparing two
projections does not manufacture one".

Our layer tower is exactly such a family, so this is now instantiated on it. The
generic side gives the information preorder `Determines`, the transition
structure, and `isEmpty_transition_of_not_determines`. The Wikidata side turns
the abstract warning into two concrete facts about real layers:

* `classTransition_full_truthy` — for class facts, the full and truthy layers are
  interchangeable, and the transport is the identity (this is the payoff of
  `subclassEdges_truthyLayer`);
* `determines_reified_direct` with `not_determines_direct_reified`, hence
  `no_transition_direct_reified` and `no_transition_reified_direct` — the reified
  layer fixes the direct layer, the converse fails on rank, and therefore *no*
  transport between them exists in either direction.

So "is it safe to move between these two layers?" has a different answer for
different pairs, and the difference is provable, not stipulated. Also ported:
the source's insistence that the directed comparison survive summarisation
(`comparePair` and `disposition_forgets_pair`), and the gate that keeps
unresolved views out of a polarised comparison (`unresolved_not_resolved`,
`notObserved_not_resolved`, `sourceMismatch_not_resolved`), matching
`notObservedCannotResolveFor` / `sourceMismatchCannotResolveFor` upstream.

#### (c) The governed-residual reading of diagnostics

`LeanWikidataGovernedResidualBridge.agda` makes the point that an executable
ontology engine is a *producer* for a governance layer that already exists: Lean
diagnostics become diagnostic-only residual features and context gates
(admissible / inadmissible / unknown), and adding the producer must not change
the authority boundary. In our terms this is precisely the three-way gate
`supported / contradicted / unresolved` feeding `Epistemic.Repair`, with
`enact_eq_of_not_approved` and `enact_eq_of_unsupported` as the statement that
the boundary is unchanged. We had the boundary; what the source adds is the
framing that the engine's role is to *populate evidence*, never to *act*.

### 1.4 What we deliberately did not take

* **The receipt architecture itself** (`LeanTheoremContract`, source hashes,
  manifests). It solves a problem this project does not have: here the theorems
  are in the same kernel as their consumers, so a pinned hash of an external
  archive would add ceremony, not assurance. Its value is real but it is a value
  for cross-system integration.
* **Boolean "boundary records"** — the recurring Agda pattern of a record of
  `Bool` fields each paired with a proof that it equals `true`/`false`
  (`canonicalRelationalLensSynthesisBoundary` and friends). These document a
  policy; they do not constrain the data. Where the policy was about the data we
  restated it as a theorem about knowledge bases instead, which is strictly
  stronger. Where it was not, we dropped it.
* **The wider DASHI mathematics** in that PR (the Moonshine, Hecke,
  representation-restriction and ternary-arithmetic modules, which are the bulk
  of the 155 files) is unrelated to the Wikidata surface and out of scope.

---

## 2. The existing work this connects to

A map of the surrounding landscape, pillar by pillar. Where a standard or a
classical reference is the right anchor it is named; where we did not verify a
claim about the literature, it is not made.

### 2.1 The Wikidata data model, ranks and *truthy*

The primary reference is Vrandečić and Krötzsch, *Wikidata: a free collaborative
knowledgebase* (CACM 57(10), 2014), together with the Wikidata data-model and
RDF-dump documentation, which is where preferred/normal/deprecated ranks and the
"truthy" projection are specified. Our `Wikidata.Core` follows that
specification: preferred statements, or normal statements when no preferred one
exists for the same subject and property, never deprecated
(`Wikidata.IsTruthy`). The layer tower (full → truthy → RDF) mirrors the shape of
the official exports rather than inventing one.

What is standard here is the *definition*; what this project adds is that the
projection is proved conservative for class facts
(`Wikidata.subclassOf_truthyLayer_iff`, `instanceOf_truthyLayer_iff`) and
idempotent (`truthyLayer_idem`).

### 2.2 RDF, RDFS entailment and reification

`Wikidata.Rdf` sits on the W3C stack: RDF 1.1 Concepts, RDF Schema, and the RDF
1.1 Semantics recommendation, whose class-related entailment rules are the two
our `Entails` relation uses (transitivity of `rdfs:subClassOf`, and lifting
`rdf:type` along it). Reification of statements as nodes with rank is the shape
of Wikidata's own RDF export.

Standard treatments prove entailment rules *sound* and, for the RDFS fragment,
complete. What we add is the four guarantees separated and proved for *this*
encoding — losslessness via an explicit decoder (`dereify_reify`), soundness
against an intended model, and **exactness** in both directions
(`entails_subclass_iff`, `entails_instance_iff`, `entails_inert`) — plus the
negative result that the direct layer is lossy, which is what §1.3(b) then turns
into the non-existence of a lens transition.

### 2.3 Constraints and schemas

Wikidata's own property-constraint system (single-value, distinct-value,
value-type, subject-type constraints, and `P1963` "properties for this type") is
the object modelled in `Wikidata.Constraints`. The neighbouring standards for
validating RDF against a schema are SHACL (W3C Recommendation, 2017) and ShEx.
Our contribution here is modest and precise: each constraint gets an executable
checker with an exactness theorem and a violation report with
`violations_eq_nil_iff`, and the constraints are then *used* — the identity
bijections of §2.5 are earned from them rather than assumed.

### 2.4 Ontology quality, redundancy and repair

The relevant background is the ontology-cleaning practice of the Wikidata
community (the Ontology Cleaning Task Force, whose mapped-ontology idea the
source bridge cites explicitly) together with the general literature on ontology
debugging and repair. `Wikidata.Diagnostics` and `Wikidata.Redundancy` are the
formal core of that practice: an error report equivalent to an independent
validity predicate (`errors_eq_nil_iff_valid`), and the theorem that pruning a
redundant `P279` edge changes nothing derivable (`subclassOf_prune_iff`).
`Epistemic.Repair` then adds what the practice needs and the mathematics does not
supply: a proof that enacting such a pruning under review is
relation-preserving.

### 2.5 Identity: sitelinks, external identifiers, lexemes

The background here is entity matching / record linkage and the identity
semantics of `owl:sameAs`, whose over-use is a known problem in linked data.
`Wikidata.Identity` takes the cautious line the source bridge takes: identity
evidence is candidate evidence. The formal content is that partial bijections are
*conditional* results — `idMatching_partial_bijection` needs functionality and
injectivity, which come from the constraint layer — and that identity licenses no
class fact (`identity_does_not_entail_instance`); lexeme translation by shared
denotation is symmetric but provably not transitive.

### 2.6 Provenance and context

W3C PROV-O is the standard vocabulary; the theoretical anchor for
provenance-annotated data is Green, Karvounarakis and Tannen, *Provenance
semirings* (PODS 2007). `Wikidata.Provenance` and `Wikidata.Slices` take the
lighter, order-theoretic view that suits this problem: a slice is the sub-base
cut out by a criterion on statements, slices compose and are ordered by
refinement, derived facts are monotone in the slice, and validity is inherited.
The epistemic consequence is the directional one: support transfers *up* the
refinement order (`sliceClaim_transfers_up`) and provably not down
(`support_does_not_transfer_down`).

### 2.7 Three- and four-valued evidence logics

`Epistemic.Trit` is Kleene's strong three-valued logic (Kleene, *Introduction to
Metamathematics*, 1952) — the De Morgan and associativity laws we prove are its
standard laws. The four-cornered square added in this pass (§1.3(a)) is Belnap's
"useful four-valued logic" (1977), whose carrier is exactly *neither / true /
false / both* with the knowledge order; Fitting's and Ginsberg's bilattices are
the general setting. The DASHI framing of the same square as a *tetralemma*
(catuṣkoṭi) is a different intellectual lineage for the same four corners, and
the source's demand — do not collapse *both* and *neither* — is Belnap's original
motivation for the fourth value, arrived at from the other direction.

Mathlib does not carry this material: its `KleeneAlgebra` is the star-semiring
notion from formal-language theory, unrelated to Kleene's three-valued logic, and
a search of the Mathlib source pinned by this project finds no Belnap, bilattice,
RDF or ontology development. The three- and four-valued layers here are built
from scratch for that reason.

### 2.8 Lenses and bidirectional transformations

The `ViewFamily` / `Transition` pair of §1.3(b) is the view-update problem in its
lens formulation: Foster, Greenwald, Moore, Pierce and Schmitt, *Combinators for
bidirectional tree transformations* (TOPLAS 29(3), 2007), and the relational
lenses of Bohannon, Pierce and Vaughan (SIGMOD 2006). Our `Transition` is
deliberately the strong, *very well-behaved* end of that spectrum — a two-sided
transport with both round trips — because the question we want to answer is
binary: can this layer change be undone at all? The interesting result is
therefore a **non-existence** theorem (`no_transition_direct_reified`), which is
the direction that lens work usually does not need to make explicit and that an
ontology pipeline very much does.

### 2.9 Where this project sits

Against all of the above, the specific position of this development is:

* an **executable** engine — every relation has a decidable checker with an
  exactness theorem, so the worked fragment in `Wikidata.Examples` and
  `Wikidata.ExamplesLayers` is decided by `decide`, not asserted;
* organised along **two axes made formal** — layers (which projection you read)
  and slices (which part you trust) — with the epistemic layer indexed by both
  and each coordinate's behaviour proved separately (layer inert, slice
  directional);
* carrying a deliberate stock of **negative results** — the direct layer forgets
  rank; support does not transfer down; absence is not refutation; identity does
  not entail class membership; part-of is inert for the class order; translation
  is not transitive; the trit collapse identifies conflict with ignorance — which
  is the part of the discipline we learned from the source bridge.

### 2.10 Gaps that remain

Two of the four gaps recorded here have since been closed by the sixth pass
(`PORTING_NOTES.md`).  Quantity, time and globe-coordinate value types are
modelled in `RequestProject/Wikidata/Values.lean`, each with an executable
comparison — interval overlap in a shared unit, agreement at a precision within a
calendar model, coverage within a tolerance on a globe — and with the negative
result that rules out the naive reading.  Qualifiers and references are
first-class objects of the statement in `RequestProject/Wikidata/Qualifiers.lean`
rather than a shadow on the core layer, and the relation between the two layers is
proved: the temporal slice cut out by the qualifiers is a genuine slice, while the
core layer forgets qualifiers, erases expiry, drops `novalue` and `somevalue`
snaks, and cannot attribute a reference across a non-injective projection.

The remaining two gaps are closed by the same pass.  The SPARQL core fragment —
triple patterns, conjunction, union, `OPTIONAL`, `bound` / `!bound` — is modelled
in `RequestProject/Wikidata/Sparql.lean` with the classical monotonicity result:
the positive fragment never loses an answer when data arrives, and `OPTIONAL` and
negation as failure do, which is why a `!bound` answer is an absence in the base
that was queried and not a refutation.  Property characteristics — transitive,
symmetric, inverse — are modelled in `RequestProject/Wikidata/Owl.lean` as an
entailment relation with a decidable closure check, together with the boundary
results that such a declaration is an edit to the theory rather than a reading of
it, and that class equivalence must not be encoded as a subclass cycle.

Property paths, counting and named graphs — listed here as gaps when the sixth
pass was written — are modelled in `RequestProject/Wikidata/SparqlPaths.lean`
and `NamedGraphs.lean`: `P31/P279*` is proved to be the project's own instance
relation, the path fragment is proved monotone, a named graph is proved to be a
slice, and a fact derived over a dataset is shown not to be attributable to any
of its named graphs.  The aggregation layer follows in
`RequestProject/Wikidata/SparqlAggregation.lean`: `SELECT DISTINCT` and the
`GROUP BY` keys inherit the monotonicity of the positive fragment, while `COUNT`
and `HAVING` are proved *not* to — a `HAVING (COUNT(*) = 1)` answer is withdrawn
by the arrival of a statement — so monotonicity does not survive being pushed
through a function of the answer list.  `SparqlNegation.lean` adds the two
modern negations, `MINUS` and `FILTER NOT EXISTS`, and proves them distinct: with
disjoint variables the first removes nothing and the second removes everything.

OWL's class *expressions* — intersection, union, complement, `∃p.C` and `∀p.C` —
are modelled in `RequestProject/Wikidata/ClassExpressions.lean`, with the
positive fragment proved monotone, complement and the universal restriction
proved not to be, and the recorded class algebra proved sound for the expression
semantics.

Still not modelled: SPARQL's expression language (arithmetic and string filters,
subqueries, federation); OWL beyond the class and property fragments (nominals,
cardinality restrictions, datatypes); and, within the value types, unit
conversion, which is deliberately declined — the comparison refuses to compare
across units rather than converting.

## 3. The parent/progenitor tranche, and what it connects to

The source repository's later parent/progenitor work (its PR #581) is the origin
of the fourth pass, documented concept by concept in `PORTING_NOTES.md`.  Its
Wikidata-facing content is one thesis: *a parent slot is a projection of a much
richer carrier, and what the projection erases can be action-bearing.*  The
material it connects to is largely outside the ontology literature of §2.

### 3.1 Modelling parenthood in Wikidata

Wikidata records parenthood in `P22` (father), `P25` (mother), `P8810` (parent,
generic) and `P1531` (parent of this hybrid, breed or cultivar).  The properties
are deliberately thin: they record *that* a party is a recorded parent, not the
genetic, gestational, legal or social basis on which they are.  That is a
reasonable data-model decision, and it is exactly what makes the projection
theorems here bite — `Wikidata.slot_does_not_determine_semantics` and
`Wikidata.Parenting.route_not_factorsThrough`.

The biological phenomena that rule out an exact-two progeniture axiom are
established results: selective egg-cell polyspermy in *Arabidopsis*, which
produces viable triparental plants (Mao et al., *eLife* 9:e52976, 2020), and
mitochondrial replacement, in which nuclear and mitochondrial contributions come
from different parties (Tachibana et al., *Nature* 493, 2013).  They enter the
Lean development as the countermodels `triparental_has_three_progenitors` and
`mitochondrialReplacement_has_three_progenitors`; the corresponding cardinality
cap survives only as a theorem with its hypothesis attached
(`card_geneticParentsF_le_two`).

### 3.2 Observational equivalence and quotients

`Epistemic.Observer` is the elementary theory of observational equivalence: an
observer induces a partition, refinement orders observers by that partition, and
a hidden transition is a state change invisible to the observer.  These are
standard notions in the semantics of programs and in process theory; what is new
here is not the notions but their use as an *ontology* discipline, together with
the residual coordinate of `Epistemic.Quotient` that makes a projection exactly
reversible and thereby forces every hidden motion to move the residual.

### 3.3 Safety of acting on a projection

`Epistemic.DynamicSafety` is close in shape to observational determinism in
language-based security: states an observer cannot currently distinguish must
stay indistinguishable along admissible runs.  The reading here is different —
the observer is a *consumer* of a public data surface rather than an attacker —
and the interesting content is the two relativisations, to the consumer and to
the policy, with a defect for one consumer proved not to be repairable by the
safety of another (`not_plural_of_defect`).

### 3.4 Delegation and revocation

`Epistemic.Authority` models delegated authority as a chronological history of
grants and revocations, in the spirit of capability and delegation logics in
access control.  The laws proved are the ones the source tranche states
informally: revocation ends prospective authority without erasing the record, a
past grant does not restore it, an unavoidable continuation confers no new
mandate, and a supporter cannot self-authorise.  The point of formalising them
next to the ontology is the boundary between them: a recorded relation is
evidence and never a mandate (`Epistemic.support_does_not_confer_authority`).

### 3.5 What is added here

Relative to the source tranche, the additions are the executable parent engine
with its exactness theorems, the hypothesis-scoped cardinality cap, the
quantified non-factorability of the authority route, exact reopening with a
composable residual, and the two-sided comparison between the flat role
vocabulary and the carrier (`step_and_foster_collide`), which shows neither
surface is a projection of the other.

## 4. The evidence-polarity tranche, and what it connects to

The source repository's evidence-polarity / cross-pollination work (its PR #582)
is the origin of the fifth pass, documented concept by concept in
`PORTING_NOTES.md`.  Two of its themes have literatures worth naming.

### 4.1 What "evidence against" is evidence against

Bilattice-style evidence carriers (Belnap; Ginsberg) give a claim two
independent coordinates, "told true" and "told false", and the project's
`Epistemic/Tetralemma.lean` already carries that square.  What the tranche adds
is the observation that the second coordinate is only a negation *relative to an
operator*: the recorded counter-evidence may concern the converse of a relation,
the algebraic inverse of a quantity, a reading in another context, or the same
claim through another lens.  The distinction is familiar from argumentation
frameworks, where an attack relation is primitive and its soundness is a
modelling obligation, and from the ontology literature on `owl:sameAs` misuse,
where a link asserted with one intended reading is consumed with another.  Here
the obligation is discharged semantically: `Epistemic.Opposes` says the opposing
claim holds exactly when the base claim fails, and everything that treats
counter-support as refutation is proved only under that condition, with
`role_does_not_determine_opposition` showing the declared tag cannot substitute
for it.

Pooling evidence from several sources is standard (Dempster–Shafer combination,
provenance semirings, the knowledge order of a bilattice); the tranche's point
is about the *index* of the pool rather than the operation, and this pass proves
it: pooling inside one fibre — one opposition, one context — retains conflict
and retains ignorance, while pooling across fibres manufactures a conflict
corner out of readings that are individually true
(`crossContext_pool_manufactures_conflict`, `crossRole_pool_manufactures_conflict`,
and, on the artist fragment, `crossBase_pool_manufactures_conflict`).

### 4.2 Required axes and non-compensation

Data-quality frameworks routinely score a record on several dimensions and then
aggregate the scores, and Wikidata's own referencing requirements are of this
shape: a class fact may be well formed, constraint-satisfying and still
unreferenced.  `Epistemic/AxisSupport.lean` makes non-compensation exact:
resolution of the required axes is not a function of how many axes are supported
(`no_resolution_from_supportCount`), because a conflicted axis is supported and
unresolved at once, so no aggregate score can decide importability.  On the
worked fragment, `painterArtist_import_not_resolved` is a claim every checker
affirms which is still not importable.

### 4.3 Transverse readings and their join

That two projections of one object can each be blind to something the other sees
is the elementary theory of observational equivalence, already used in the fourth
pass.  What this pass adds is the *join*: `Epistemic.pairObserver_least` proves
the pair of two readings is their least common refinement, and
`not_separating_pairObserver_of_common_collision` proves the join is still not
the object.  The Wikidata instance is that the statement layer and the data
slice — the two coordinates of a view in `Epistemic/Views.lean` — are
incomparable readings of a knowledge base whose join still misses a deprecated
instance statement (`Wikidata.layerObs_incomparable_sliceObs`,
`Wikidata.viewObs_not_separating`).

### 4.4 The balanced-ternary carrier

The tranche's `3 ^ 9` interaction state space is standard balanced-ternary
notation, and the counts it records are elementary combinatorics: the number of
words of `n` trits summing to `k` is the central-trinomial-style coefficient row
of `(x⁻¹ + 1 + x) ^ n`, and the antipodal quotient of a set with an involution
having one fixed point has `(3 ^ n + 1) / 2 ` classes.  Upstream both are
recorded as the lengths of hand-written lists.  `Ternary/Balanced.lean` proves
that the coefficient row *is* the fibre count (`card_sumFibre`, whence `3139`
for the zero fibre in nine coordinates) and derives the class counts from one
involution lemma; `Ternary/Base369.lean` and `Ternary/Aggregate.lean` then use
the carrier only as a source of two transverse readings and of a strictly lossy
`9 → 4 → 3` collapse, which is the part with ontology content.

### 4.5 Learning an ontology from its own data

The tranche also states the boundary for the "the wiki solves itself over time"
workflow, in which a runtime computes feature vectors, residual graphs and
clusters over a revision-pinned snapshot and proposes ontology repairs.  The
components are familiar — ontology learning and enrichment, instance-based
schema induction, entity clustering and duplicate detection, and the class-merge
problem that every collaborative knowledge base faces — and the standard warning
in that literature is exactly the tranche's: an induced regularity is empirical,
while a class definition is normative.

`Wikidata/Learning.lean` makes the warning provable on the project's engine.
The invariant is computed from the reviewed cohort (`learned`, with
`mem_learned_iff`), a member that review did not admit changes it not at all
(`learned_ignores_untrained`), an empty admitted cohort yields the vacuous
invariant (`empty_cohort_learns_everything`), and membership is not a function
of the feature signature (`membership_not_factorsThrough_signature`), which is
the sharp form of "resemblance is not membership".  For merges the conservative
gate is executable, is proved not to be a function of the residual geometry
(`gate_not_factorsThrough_geometry`), and enacting requires both the gate and an
approval; `applied_merge_changes_instances` shows that a merge, unlike a
redundancy pruning, genuinely moves the derived relations, which is the reason
the review exists.

### 4.6 What is added here

Relative to the source tranche: the semantic notion of opposition and the proof
that a role tag cannot license refutation; fibre-indexed pooling with the two
cross-fibre countermodels; the axis layer, which upstream is named as future
work, with non-compensation strengthened to independence from any support count;
the universal property of the observer join together with its failure to
separate; and the counting theorems, which replace the upstream tabulated
constants by statements about the carrier.
