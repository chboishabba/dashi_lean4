# Porting the Wikidata bridge back to Lean 4

This project is a Lean 4 rendering of the Wikidata-facing ideas in the DASHI
Agda bridge (`chboishabba/dashi_agda` PR #555), focused on the parts that are
new and interesting there, and re-built so that the guarantees are *proved*
rather than recorded.

Everything is machine-checked, `sorry`-free, and uses only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## What was ported, and what changed in the process

The Agda bridge describes imported Lean results: it pins a source hash, records
that some theorem exists upstream, and specifies how such a *record* should be
treated epistemically. Its interesting content is the epistemic discipline:

| Idea in the Agda bridge | Lean rendering here |
| --- | --- |
| `EpistemicTrit` (supported / unresolved / contradicted) | `Epistemic.Trit`, with the full Kleene algebra (`meet`, `join`, `neg`, De Morgan, associativity) |
| fail-closed projection `theoremReceiptState` | `Epistemic.receiptState` + `receiptState_ne_contradicted` |
| open-world absence never manufactures conflict | `Epistemic.unresolved_left_never_conflicts`, `conflict_requires_opposition` |
| certified-false vs. not-observed (`ObjectVerdict`) | `Epistemic.verdictState`, `verdictState_eq_contradicted_iff` |
| `ScopedClaim` / contextual claim composition | `Epistemic.ScopedClaim`, `ScopedClaim.and`, `references_subset_and` |
| authority non-promotion (truth / edit) | `Epistemic.importEvidence_eq`, `Epistemic.enact_eq_of_not_approved`, `enact_eq_of_unsupported` |
| review-only repair with a distinct `removeRedundantSuperclass` | `Epistemic.RepairOperation`, `enact_removeBadSuperclass`, `redundancyProposal_operation` |
| truthy query projection is not epistemic truth | `Wikidata.IsTruthy` vs. `Wikidata.Example.truthy_does_not_determine_evidence` |
| cross-ontology alignment as comparison evidence | `Wikidata.Alignment`, `alignOk_iff`, `Wikidata.Example.badAlignment_refuted` |
| provenance / temporal context slices | `Wikidata.Provenanced`, `Wikidata.Timed`, `Epistemic.sliceClaim` |
| content-addressed worked fragment (artist / painter / sculptor) | `Wikidata.Example.artistKB` and the regression theorems around it |

Because this is Lean rather than a descriptive bridge, three things become
theorems instead of conventions:

1. **Support is backed.** `Epistemic.Certificate.holds_of_supported`: a
   certificate whose state is `supported` entails the ontology claim it reports.
   Every importable claim comes with an exact checker (`ClassClaim.check_iff`).
2. **Certified negatives are real.** Since the checkers are exact, a checker
   failure is a proof of the negative *for that knowledge base*
   (`Certificate.not_holds_of_refuted`) — which is what distinguishes it from a
   missing observation. `Wikidata.Example.absence_is_not_world_refutation`
   exhibits a claim that fails in one knowledge base and holds in a larger one,
   which is why a negative is never exported as a world-level refutation.
3. **The repair pipeline is safe.**
   `Epistemic.enact_redundancy_proposal_preserves_subclass` (and the instance
   version): enacting a supported redundancy proposal, under *any* review
   decision, leaves the derived subclass and instance relations unchanged.

## The ontology engine

The bridge is only meaningful with a real engine underneath, so the Wikidata
layer is built from scratch:

* `RequestProject/Wikidata/Reachability.lean` — a fuel-bounded reachability
  search with an exactness theorem (`reachIn_iff`), proved via loop removal
  (`exists_nodup_chain`) so that searching to depth "number of edges" decides
  the reflexive transitive closure.
* `RequestProject/Wikidata/Core.lean` — items, properties, ranked statements,
  the truthy projection, and the `P279`/`P31` engines with
  `isSubclassOf_iff` and `isInstanceOf_iff`.
* `RequestProject/Wikidata/ClassAlgebra.lean` — union of / intersection of /
  disjointness / disjoint union of, each with an exactness theorem
  (`unionOk_iff`, `interOk_iff`, `disjointOk_iff`, `dunOk_iff`).
* `RequestProject/Wikidata/Redundancy.lean` — deleting a redundant `P279`
  statement preserves the subclass and instance relations
  (`subclassOf_prune_iff`, `instanceOf_prune_iff`).
* `RequestProject/Wikidata/Diagnostics.lean` — an error report and an
  independently defined validity check, with `errors_eq_nil_iff_valid`,
  `valid_iff` and acyclicity of valid knowledge bases.
* `RequestProject/Wikidata/Alignment.lean` — partial cross-ontology mappings,
  subclass preservation (`alignOk_iff`) and disjointness reflection.
* `RequestProject/Wikidata/Provenance.lean` — provenance slices (asserted /
  sourced / reliable) and temporal snapshots, with monotonicity of the derived
  relations and preservation of validity under slicing.

4. **Context is real.** `Epistemic.sliceClaim` is a genuinely context-dependent
   scoped claim: support obtained from a restricted, more trustworthy provenance
   slice transfers up to the whole knowledge base
   (`sliceClaim_transfers_up`), and the converse fails
   (`Wikidata.Example.support_does_not_transfer_down`).

## Second pass: the remaining surfaces, extracted in layers and slices

The upstream inventory also lists a data-model layer tower, an RDF surface with
four separate guarantees, property/schema constraints, a mereology separation,
and the identity surfaces (matching, sitelinks, external identifiers, lexemes).
These are now modelled, organised along the two axes the source uses informally
and this port makes formal — *layers* (which projection of the data you read) and
*slices* (which part of the data you trust).

### Slices

`RequestProject/Wikidata/Slices.lean` isolates the general notion: a slice is the
sub-base cut out by a predicate on statements (`restrict`).  Slices compose
(`restrict_restrict`), are ordered by refinement (`Refines`), never derive new
facts (`subclassOf_of_restrict`, `instanceOf_of_restrict`) and inherit validity
(`valid_restrict`).  The provenance and temporal slices of the first pass are
instances (`Provenanced.slice_eq_restrict`, `Timed.snapshot_eq_restrict`).

### Layers

| Layer in the source | Lean rendering here |
| --- | --- |
| `fullStatementLayer` | `Wikidata.StatementLayer.full` |
| `truthyQueryLayer` | `Wikidata.truthyLayer`, a slice by `IsTruthy` |
| `reifiedRdfLayer` | `Wikidata.Rdf.reify` |
| `directRdfLayer` | `Wikidata.Rdf.directTriples` |

`RequestProject/Wikidata/Layers.lean` proves the truthy layer *conservative*: it
drops data (deprecated and rank-shadowed statements) but the derived graphs are
literally the same lists (`subclassEdges_truthyLayer`), so the derived relations
agree in both directions (`subclassOf_truthyLayer_iff`, `instanceOf_truthyLayer_iff`),
the projection is idempotent, and layers commute with slices on rank-free bases.

### RDF: four guarantees, kept apart

`RequestProject/Wikidata/Rdf.lean` renders each of the four upstream guarantees as
a separate theorem:

1. **losslessness** — `dereify_reify` (an exact decoder), hence `reify_injective`;
2. **soundness** — `entails_sound` against an intended model;
3. **exact `P279` entailment** — `entails_subclass_iff`;
4. **exact `P31` entailment** — `entails_instance_iff`;

plus executable agreement (`isSubclassOf_iff_entails`, `isInstanceOf_iff_entails`),
inertness outside the class predicates (`entails_inert`), and the *negative*
result that the direct layer is genuinely lossy (`direct_layer_forgets_rank`).

### Constraints, schemas, mereology

`RequestProject/Wikidata/Constraints.lean` gives single-value, distinct-value,
subject-type and value-type constraints and a `P1963`-style schema profile, each
with an exact checker, plus a report with `violations_eq_nil_iff`.  The
mereology / class-order separation becomes a theorem: any non-preferred statement
whose property is neither `P279` nor `P31` — a part-of statement in particular —
is inert for the class order (`partOf_inert`).  Parthood gets its own executable
engine (`isPartOf_iff`) and is transitive but not reflexive.

### Identity

`RequestProject/Wikidata/Identity.lean` renders matching, sitelinks, external
identifiers and lexemes through one `Matching` structure.  The upstream
"partial-bijection style identity results under explicit functionality /
injectivity constraints" become `invFun_of_toFun` / `toFun_of_invFun`, and the
hypotheses are *earned* from the constraint layer:
`functional_of_singleValue` and `injective_of_distinctValue`.  Lexeme translation
by shared denotation is symmetric but demonstrably not transitive
(`translates_not_transitive`), and identity evidence licenses no class fact
(`identity_does_not_entail_instance`).

### Evidence over the new surfaces, indexed by view

`RequestProject/Epistemic/Surfaces.lean` extends the bridge with `SurfaceClaim`
(constraint, RDF entailment, losslessness, parthood, identifier bijection), each
with an exact checker, so support is still backed (`holds_of_supported`) and
import is still fail-closed (`state_ne_contradicted`).  One member of the family
is a theorem rather than a receipt: `losslessness_always_holds`.

`RequestProject/Epistemic/Views.lean` indexes evidence by a *view* = layer ×
slice, and separates the two coordinates:

* the layer coordinate is epistemically inert (`positive_check_atLayer`,
  `viewClaim_layer_irrelevant`);
* the slice coordinate is directional — support transfers up the refinement order
  (`viewClaim_transfers_up`) and not down
  (`view_support_does_not_transfer_down`).

`RequestProject/Wikidata/ExamplesLayers.lean` runs the artist / painter /
sculptor fragment through all of it, every example decided by the executable
checkers.

## Scope

The port now covers the class / instance / rank / diagnostics / redundancy /
alignment / provenance core, the statement and RDF layers, the constraint,
mereology and identity surfaces, and the complete epistemic layer over all of
them.  Not modelled: quantity, time and coordinate value types, qualifiers as
first-class objects, and the SPARQL query surface.

## Third pass: what the source bridge still had to teach, and the surrounding work

`RELATED_WORK.md` answers two questions in detail: what the DASHI Agda bridge
contributed (with each of its eleven stated invariants traced to the Lean
declaration that now carries it), and what existing work each pillar of this
development connects to.

Three constructions from the source were not covered by the first two passes and
are ported here.

### The four-cornered support square

`RequestProject/Epistemic/Tetralemma.lean`.  The source insists that
"both sides supported" and "nothing established" must not be collapsed into one
ternary middle value.  `SupportSquare` carries evidence for and against
independently — Belnap's four-valued carrier, with the knowledge order `Knows`
and `merge` proved to be its least upper bound — and the relation to the existing
trit is settled exactly:

* `collapse_importSquare` — the square refines the trit on single imports;
* `collapse_not_injective`, `eq_of_collapse_eq_of_ne` — the collapse identifies
  the conflict corner with the ignorance corner, and identifies nothing else;
* `conflicting_iff_merge_bothSupported` — cross-source conflict *is* the top
  corner of the pooled square;
* `merge_then_collapse_ne_collapse_then_merge` — so sources must be pooled before
  the collapse;
* `importSquare_ne_both` — one source can never reach the top corner alone.

`MetaStatus` / `Qualified` add the orthogonal "why is this indeterminate"
coordinate, with `Qualified.scopeExceeded_ne_contradicted`.

### View families and lens transitions

`RequestProject/Epistemic/Lens.lean` and `RequestProject/Wikidata/Lens.lean`.
The layer tower is a family of projections of one latent object.  `Determines` is
the resulting information preorder, `Transition` the explicit two-sided
transport, and `isEmpty_transition_of_not_determines` the statement that a
transition never comes for free.  On the real layers:

* `classTransition_full_truthy` — for class facts the full and truthy layers are
  interchangeable and the transport is the identity;
* `determines_reified_direct`, `not_determines_direct_reified`, hence
  `no_transition_direct_reified` and `no_transition_reified_direct` — the RDF
  tower is strictly ordered by information and admits no transport in either
  direction.

Also ported: retention of the directed comparison (`comparePair`,
`disposition_forgets_pair`) and the gate keeping unresolved views out of a
polarised comparison (`unresolved_not_resolved`, `notObserved_not_resolved`,
`sourceMismatch_not_resolved`).

### Worked regression

`RequestProject/Wikidata/ExamplesConflict.lean` runs both over the artist
fragment: two exact checkers give opposite verdicts about `painter ⊑ artist` on
`artistKB` and `partialKB`, and the pooled square records the conflict
(`pooled_verdicts_conflict`) that the collapse would erase
(`conflict_indistinguishable_from_silence`); and the ranked variants of a single
statement witness the direct layer's collapse of rank
(`ranked_variants_agree_directly`, `ranked_variants_differ_reified`).

## Fourth pass: the parent/progenitor tranche (source PR #581)

The fourth pass ports the source repository's parent/progenitor work.  Its
Wikidata-facing content is one idea pushed hard: *a parent slot is a projection
of a much richer carrier, and what the projection erases is action-bearing.*
Around that sit a generic observer/fibre layer, an exact-reopening layer, and a
governance layer about acting on a projection over time.

As in the earlier passes, the descriptive parts of the source — boolean
"boundary records" asserting that some collapse is or is not licensed — are
replaced by theorems about a real engine.

| Idea in the source tranche | Lean rendering here |
| --- | --- |
| `GenerationEvent` with arbitrary finite `progenitors` | `Wikidata.GenerationEvent`, `progenitorCount`, `triparental_has_three_progenitors`, `mitochondrialReplacement_has_three_progenitors` |
| exact-two cardinality stays behind `BiparentalNuclearWitness` | `Wikidata.BiparentalNuclearWitness`, `exactly_two_requires_biparental_witness` |
| genetic-parent cap scoped to the two typed slots | `Wikidata.SingleGeneticSlots`, `card_geneticParentsF_le_two`, and `cap_does_not_mean_exactly_two` |
| twelve orthogonal relationship coordinates | `Wikidata.RelationVector` and the countermodels `genetic_does_not_confer_parenthood`, `parenthood_does_not_require_genetics`, `gestation_does_not_confer_parenthood`, `mitochondrial_does_not_confer_parenthood`, `disclosure_is_independent`, `progeniture_is_not_parenthood` |
| donor conception computes to one genealogical parent, two genetic contributors | `Wikidata.donorConception_counts` |
| flat eight-role vocabulary reified and refined | `Wikidata.ParentRole`, `refine_preserves_genetic/legal/social`, `recorded_tag_is_lossy`, `role_vocabulary_incomplete`, `step_and_foster_collide` |
| slot does not determine semantics | `Wikidata.slot_does_not_determine_semantics`, `recorded_statement_forgets_relation`, `recordedKB_eq` |
| observer refinement lattice (`Separating`, `Refines`, residual fibres) | `Epistemic.Observer`: `Separating`, `Refines`, `StrictlyRefines`, `AgreeOn`, `ResidualFibre`, `residualFibre_cons_subset`, `residualFibre_cons_ssubset`, `separatingFamily_iff_residualFibre_eq` |
| fibre-preserving dynamics, hidden transitions, deck symmetries | `Epistemic.SurfaceInvariant`, `HiddenTransition`, `not_injective_of_hiddenTransition`, `DescendsToSurface`, `FibreAutomorphism` |
| sectioned projection; a section is not fine reconstruction | `Epistemic.SectionedProjection`, `fibreConstant_eq_pullback`, `exists_section_not_injective` |
| exact reopening from a residual coordinate | `Epistemic.ExactRecoverable`, `eq_of_project_eq_of_residual_eq`, `residual_ne_of_hiddenTransition` |
| composite residual is the product of the stage residuals | `Epistemic.ExactRecoverable.comp`, `comp_residual_eq`; instance `Wikidata.Parenting.progressiveReopening_residual` |
| predicate pullback lattice and descent | `Epistemic.pullbackPred`, `fibreConstantPred_pullback`, `pullbackPred_meet`, `pullbackPred_join` |
| routing non-factorability | `Epistemic.FactorsThrough`, `not_factorsThrough`; instance `Wikidata.Parenting.route_not_factorsThrough` |
| consumer-relative dynamic safety and terminalisation defects | `Epistemic.DynamicSafety`, `TerminalisationDefect`, `PluralDynamicSafety`, `not_plural_of_defect` |
| policy-relative safety and policy-exposed quotient defects | `Epistemic.PolicyRelativeSafety`, `PolicyExposedQuotientDefect`, `policyRelativeSafety_of_dynamicSafety` |
| diachronic delegated authority and revocation laws | `Epistemic.Authority`: `currentAuthority`, `everGranted`, `currentAuthority_append_revoke`, `currentAuthority_eq_false_of_no_regrant`, `everGranted_append_revoke`, `supporter_cannot_self_authorise`, `unavoidable_continuation_creates_no_mandate`, `discretionary_act_requires_fresh_grant` |
| family agency is not sovereignty | `Wikidata.Parenting.parentObserver_not_separating`, `parent_report_strictly_refined_by_child_voice`, `childVoiceObserver_not_separating` |
| separation is not authority; evidence is not a mandate | `Epistemic.support_does_not_confer_authority`, `slot_evidence_cannot_route_authority` |

### What changed in the porting

1. **The parent slots get a real engine.**  `parentEdges` collects the truthy
   statements of `P22`, `P25` and `P8810`; `descendsFrom` is the fuel-bounded
   search and `descendsFrom_iff` proves it decides the reflexive transitive
   closure exactly.  The same construction over the two typed slots gives
   `geneticDescendsFrom_iff`.  Genetic descent implies recorded descent
   (`descendsFrom_of_geneticDescendsFrom`) and provably not conversely
   (`recorded_descent_not_genetic`).  The reachability engine is factored out as
   `Wikidata.Edges` so any edge set can reuse it.

2. **The cardinality cap is a theorem with its hypothesis attached.**
   `card_geneticParentsF_le_two` needs `SingleGeneticSlots`, and nothing more is
   claimed: `cap_does_not_mean_exactly_two` and `donorKB_cap` exhibit a knowledge
   base that satisfies the cap with one genetic parent.

3. **"The slot loses semantics" is strengthened to an action-facing theorem.**
   `route_not_factorsThrough` rules out *every* interpretation of the slot, not
   merely the obvious ones, because `FactorsThrough` quantifies over the
   interpretation.

4. **Boundary records become dynamics.**  Rather than asserting that hidden
   motion at fixed surface is possible, `finalizeLegal_hidden_transition` and
   `disclose_hidden_transition` exhibit it, and
   `legal_finalization_moves_residual` / `disclosure_moves_residual` derive from
   exact reopening that any such motion must move the residual.

5. **Delegated authority is a state machine, not a flag.**  `currentAuthority`
   folds a chronological history of grants and revocations; the revocation laws
   are then proved about arbitrary histories, and the historical record
   (`everGranted`) is proved to be a different function from the current
   authority.

6. **The role vocabulary comparison is two-sided.**  Besides the expected
   losses (`recorded_tag_is_lossy`, `role_vocabulary_incomplete`) the carrier is
   shown to lose something too: `step_and_foster_collide`.  Neither surface is a
   projection of the other.

### Deliberately not ported

* the source-hash pinning of Lean modules and the theorem-name receipts.  In one
  kernel a theorem is available directly, so a receipt would be strictly weaker
  than the statement; the same decision was taken in the first pass;
* the paper-reference records for the biological source material.  They are
  bibliographic metadata, not mathematics; the phenomena they support
  (polyspermy, mitochondrial replacement) are ported as the countermodels
  `triparental_has_three_progenitors` and
  `mitochondrialReplacement_has_three_progenitors`;
* the branches of the source tranche outside the Wikidata scope of this project
  (the Hecke/Brandt/Fricke observer instances).

## Fifth pass: the evidence-polarity cross-pollination tranche (source PR #582)

The fifth pass ports the source repository's evidence-polarity /
cross-pollination tranche.  Two themes in it are worth taking.

The first is *polarity*: the support square has a "counter-supported" corner,
and the tranche's observation is that what sits in that corner is not
automatically the negation of the claim in the other corner.  The second is
*transversality*: several of the tranche's carriers — the balanced-ternary
interaction state space, the block/aggregate readings of it, the binary collapse
of a three-valued comparison — are there to exhibit two readings of one object
that are each blind to something the other sees, together with counts of the
resulting quotients.

As in the earlier passes the descriptive parts are replaced by proofs: upstream
the counts are cardinalities of hand-written constructor lists and the
non-factorisations are recorded as booleans; here they are theorems about the
carriers and about *every* candidate decoding.

| Idea in the source tranche | Lean rendering here |
| --- | --- |
| the `3 ^ 9` balanced-ternary interaction carrier, `19683` states | `Ternary.Trit`, `Ternary.Word`, `Ternary.card_word`, `card_word_nine` |
| the antipode, and `0` is not a pole | `Ternary.Trit.antipode`, `antipode_involutive`, `Ternary.Word.antipode_eq_self_iff` |
| the convolution row of `(x⁻¹ + 1 + x)^n`, and the aggregate-zero fibre of size `3139` | `Ternary.rowCount` with `Ternary.card_sumFibre` (the row *counts* the words), `card_sumFibre_nine_zero`, `sum_rowCount` |
| antipodal class counts `5`, `14`, `9842` | `Ternary.two_mul_card_orbits` and its instances `card_orbits_two`, `card_orbits_three`, `card_orbits_nine`, from the generic `Ternary.two_mul_card_pairImage` |
| base-3/6/9 blocks: blockwise orientation vs. global aggregate | `Ternary.Block`, `Ternary.State`, `Ternary.blockObs`, `Ternary.State.aggregate` |
| blockwise quotient `14 ^ 3 = 2744` against the global `9842` | `Ternary.card_image_blockObs`, `Ternary.card_stateOrbits`, `Ternary.blockwise_ne_global` |
| eight states over a blockwise class of non-central blocks | `Ternary.card_fibre_blockObs`, `card_fibre_blockObs_allPos` |
| the two readings collide in both directions | `Ternary.aggregate_not_factorsThrough_blockObs`, `blockObs_not_factorsThrough_aggregate`, `blockObs_incomparable_aggregate` |
| the observer join of the two readings | `Ternary.jointObs`, `jointObs_universal`, `jointObs_not_separating` |
| transverse observers and their universal property in general | `Epistemic.Incomparable`, `incomparable_of_cross_collisions`, `Epistemic.pairObserver_least`, `factorsThrough_pairObserver`, `not_separating_pairObserver_of_common_collision` |
| factoring and refinement are the same relation | `Epistemic.refines_of_factorsThrough`, `factorsThrough_iff_refines` |
| three-element carriers are not canonically identified | `Ternary.encodeWithPolicy`, `encoding_of_unresolved_is_policy`, `no_canonical_binary_decision` |
| the binary/balanced aggregate loss `9 → 4 → 3` | `Ternary.binaryProject`, `acceptCount`, `acceptCount_erases_direction`, `direction_not_factorsThrough_acceptCount`, `binaryProject_not_separating` |
| centring a Bernoulli position onto a balanced digit | `Ternary.BernoulliPoint`, `centred_complement`, `half_complement_fixed`, `centred_injective` |
| operator roles tagging an opposition (converse, inverse, contextual, lens) | `Epistemic.OperatorRole`, `Epistemic.Opposition` |
| "evidence against" is evidence against *something*, and only sometimes the negation | `Epistemic.Opposes`, `not_holds_of_sound_against`, `sound_ne_bothSupported` |
| the role tag is a description, not a licence | `Epistemic.role_does_not_determine_opposition`, `converse_not_opposes`, `converse_support_does_not_refute` |
| pooling only inside a fibre | `Epistemic.FibreEvidence`, `pool`, `pool_conflict`, `pool_ignorance`, `crossContext_pool_manufactures_conflict`, `crossRole_pool_manufactures_conflict` |
| axis-indexed evidence with required axes and a missing axis | `Epistemic.AxisEvidenceFamily`, `RequiredAxesResolved`, `MissingRequiredAxis`, `requiredAxesResolved_iff_no_missing` |
| support on one axis does not pay for another | `Epistemic.not_resolved_of_missing`, `strong_support_does_not_compensate`, `no_resolution_from_supportCount` |
| resolved axes meet the governance layer as "obligations discharged", no more | `Epistemic.obligationOf`, `resolved_axes_do_not_open_authority` |
| the polarity discipline on an ontology surface | `Wikidata.converseOpposition`, `converse_opposition_not_uniform`, `counterposition`, `counterposition_not_opposes`, `closedWorld_counterSupport_unsound`, `openWorld_pool_is_affirmation`, `crossBase_pool_manufactures_conflict` |
| required axes on an import | `Wikidata.ImportAxis`, `requiredImportAxes`, `painterArtist_has_no_references`, `painterArtist_import_not_resolved` |
| two transverse readings of one base | `Wikidata.layerObs`, `sliceObs`, `layerObs_incomparable_sliceObs`, `viewObs`, `viewObs_universal`, `viewObs_not_separating` |
| governed residual ontology learning: cohort admission | `Wikidata.Admission`, `Admission.trains`, `admitted`, `held_does_not_train`, `unresolved_does_not_train`, `coverageIncomplete_does_not_train` |
| an empirical invariant refined only by reviewed conforming members | `Wikidata.learned`, `mem_learned_iff`, `learned_ignores_untrained`, `learned_append_subset`, `empty_cohort_learns_everything` |
| the empirical surface is not the normative one | `Wikidata.learned_has_legitimate_exception`, `learned_does_not_characterise`, `membership_not_factorsThrough_signature` |
| resemblance is context-gated | `Wikidata.ContextStatus`, `EdgeKind`, `edgeFor`, `inadmissible_context_is_masked`, `unknown_context_is_not_similarity`, `similarity_only_from_admissible` |
| geometry convergence is not a merge | `Wikidata.MergeCandidate`, `mergeMode`, `mergeGate`, `geometryOnly_fails_gate`, `gate_not_factorsThrough_geometry`, `incompatible_blocks_merge`, `conditional_distinction_preserved` |
| no solver output edits the ontology | `Wikidata.enactMerge`, `enactMerge_eq_of_not_approved`, `enactMerge_eq_of_gate_failed`, `geometryOnly_never_edits`, `applied_merge_changes_instances` |

### What changed in the porting

1. **The counts are proved about the carrier, not read off a list.**
   `Ternary.card_sumFibre` proves by induction on the number of coordinates that
   the convolution row `rowCount n k` *is* the number of words summing to `k`,
   so `3139` is a statement about the nine-coordinate state space rather than
   about a polynomial expansion; and `sum_rowCount` checks the row against
   `3 ^ n`.  Similarly the class counts come from one general lemma —
   `two_mul_card_pairImage`, that an involution on a finite type has
   `2 * #orbits = #type + #fixed points` — instantiated at the antipode, whose
   single fixed point is exactly the upstream "the centre is not a pole"
   observation.

2. **Non-factorisation is quantified over decodings.**  Upstream, two readings
   are "transverse" because a boolean record says so.  Here
   `aggregate_not_factorsThrough_blockObs` and its converse rule out *every*
   function from one reading's values to the other's, because `FactorsThrough`
   quantifies over that function; `incomparable_of_cross_collisions` reduces
   proving it to exhibiting one collision in each direction, which is how each
   instance in this pass is discharged.

3. **The join gets its universal property, and its limits.**  `pairObserver` is
   proved to be the least common refinement (`pairObserver_least`), and proved
   not to be world-complete: two readings that share a collision still miss the
   distinction (`not_separating_pairObserver_of_common_collision`,
   `jointObs_not_separating`, `viewObs_not_separating`).

4. **Polarity becomes semantic.**  The upstream operator-role tag is kept as
   `OperatorRole`, but the work is done by `Opposes`, the condition that the
   opposing claim holds exactly when the base claim fails.  Only under that
   condition does opposing support refute (`not_holds_of_sound_against`) or a
   conflict corner mean inconsistency (`sound_ne_bothSupported`), and
   `role_does_not_determine_opposition` shows no assignment of licences to tags
   can do that job.  The converse of a relation is the concrete counterexample.

5. **Fibres replace a global pool.**  `FibreEvidence` is indexed by an
   opposition and a context, and `pool` is defined only inside a fibre.  Pooling
   inside a fibre keeps conflict and keeps ignorance; the two
   `..._pool_manufactures_conflict` theorems exhibit what pooling across fibres
   invents, both across contexts and across roles, and
   `crossBase_pool_manufactures_conflict` is the same phenomenon on the
   Wikidata fragment, where the two pooled readings are both true.

6. **"The wiki solves itself" gets a workflow and a boundary.**  Upstream the
   governed-learning module is a stack of records whose boolean fields assert
   that nothing is edited automatically.  Here the invariant is computed —
   `learned` is the set of properties every admitted cohort member carries, with
   `mem_learned_iff` as its exactness theorem — and the boundary is proved:
   a member that does not train leaves the invariant *equal*
   (`learned_ignores_untrained`), an empty admitted cohort learns the whole
   vocabulary and hence nothing (`empty_cohort_learns_everything`), and class
   membership is not a function of the feature signature at all
   (`membership_not_factorsThrough_signature`), so no similarity gate recovers
   it.  For merges the gate is executable and
   `gate_not_factorsThrough_geometry` proves it is not a function of the
   geometry; enacting requires both the gate and an approval, and
   `applied_merge_changes_instances` shows why — unlike pruning a redundant
   edge, a merge really does move the derived instance relation.

7. **The axis layer is built, not just named.**  The upstream tranche points at
   axis-indexed evidence as future work; here it exists, with the
   non-compensation theorem strengthened: resolution is not a function of the
   number of supported axes at all (`no_resolution_from_supportCount`), since a
   conflicted axis is supported and unresolved at once.  Its instance on the
   worked fragment is `painterArtist_import_not_resolved` — a class fact that
   every checker affirms, still not importable, because the provenance axis is
   missing.

### Deliberately not ported

* the numeric "exactness records" themselves — upstream each count is a boolean
  field asserting that a list has a given length; here the count is the theorem
  and the record has nothing left to say;
* the tranche's regression harness over synthetic cross-domain datasets.  What
  it is for — that a polarity discipline calibrated in one domain must not be
  transported to another — is ported as the cross-fibre pooling theorems, which
  state the failure rather than sampling for it;
* the branches outside the Wikidata scope of this project: the physical and
  biological interpretations of the base-3/6/9 carrier, which carry no ontology
  content, are ported only as the carrier and its counts.

## Sixth pass: value types, qualifiers, references, queries and property characteristics

The three earlier passes worked with the *item-valued core* of a Wikidata
statement — subject, property, item value, rank — and modelled qualifiers and
references only through their shadow on that core: provenance as a function from
core statements to source names (`Wikidata.Provenanced`), validity as a function
from core statements to an interval (`Wikidata.Timed`).  `RELATED_WORK.md` §2.10
listed the two resulting gaps as the largest remaining ones.  This pass closes
them.

### Value types (`RequestProject/Wikidata/Values.lean`)

Wikidata's literal value types are not numbers, dates and coordinate pairs; each
of them carries structure that a naive reading discards, and each gets here an
executable comparison with an exactness theorem and the negative result that says
which reading is wrong.

| Wikidata surface | Rendered as | The negative result |
| --- | --- | --- |
| quantity: amount, unit, lower and upper bound | `Quantity`, with `Mem` the interval it denotes and `overlaps` the agreement test (`overlaps_iff`) | `amount_equality_is_not_quantity_agreement` — the same number in two units is not the same quantity; `overlaps_not_transitive` — uncertainty is not an equivalence |
| time: timestamp, precision, calendar model | `TimeValue`, with `keyAt` the information carried at a precision and `AgreeAt` comparison at a precision, plus the precision tower `day → month → year → decade → century` | `year_precision_does_not_determine_the_day` — the padded fields are not data; `numeric_equality_is_not_time_agreement` — the calendar model is part of the value; `order_is_calendar_blind` |
| globe coordinate: latitude, longitude, precision, globe | `Coordinate`, with `covers` (`covers_iff`) | `covers_not_symmetric`, `covers_not_transitive` — precision belongs to the record, not to the place; `same_numbers_different_globe_do_not_match` |

### Qualifiers and references (`RequestProject/Wikidata/Qualifiers.lean`)

A snak (`Snak`) is a property with a value, or one of the two special snak types
`somevalue` and `novalue`; a full statement (`FullStatement`) is a main snak with
qualifiers, references and a rank; a reference (`Reference`) is a named source
with its own snaks.  The core layer of the earlier passes is recovered as a
projection, `FullKB.core`, and the relation between the two layers becomes a
theorem rather than a modelling assumption:

* the temporal qualifiers `P580`/`P582` cut out a slice — `FullKB.temporalSlice`
  — and it is a genuine slice, so what is derivable at an instant is derivable
  from the whole base (`subclassOf_of_temporalSlice`,
  `instanceOf_of_temporalSlice`);
* the core layer **forgets qualifiers** (`core_forgets_qualifiers`) and **erases
  expiry** (`core_erases_expiry`, on the Ceres/planet fragment: the claim ended in
  1801, the temporal slice at 2020 is empty, and the core layer still derives it);
* a `novalue` snak is **invisible** to the core layer
  (`noValue_is_invisible_to_core`), so "recorded as having none" and "not
  recorded" are conflated there — the absence-is-not-refutation error of the
  source bridge, arising this time inside the data model;
* a `somevalue` snak **names no item** (`someValue_names_no_item`), and literal
  values are inert for the class engines (`literal_statement_is_inert`);
* the core-level provenance shadow is recovered from the references
  (`FullKB.shadow`), a referenced statement's projection is always sourced in it
  (`sourced_of_referenced`), and — because the projection is not injective — it
  can **credit an unreferenced statement** with a reference belonging to another
  (`projection_conflates_referenced_and_unreferenced`).  Being referenced is in
  any case not being queryable (`reference_is_not_truth`).

### Evidence over the new surfaces (`RequestProject/Epistemic/ValueEvidence.lean`)

The value and qualifier surfaces join the evidence discipline through one more
claim family, `ValueClaim`, backed by exact checkers (`ValueClaim.check_iff`), so
supported evidence still entails its claim and import is still fail-closed.  The
new coordinate is that a claim about a qualified base is a claim *at an instant*,
and that coordinate is directional in the same way as a provenance slice:
`inForce_supported_imp_core_supported` holds and
`core_support_does_not_transfer_to_the_instant` shows the converse fails.  A
coarse time record likewise does not support a fine claim
(`time_support_does_not_refine`), and a unit mismatch is a certified negative
rather than an ignorance (`unit_mismatch_is_certified`).

### The query surface (`RequestProject/Wikidata/Sparql.lean`)

Wikidata is consumed through SPARQL more often than through the dumps, so the
query surface is modelled too: triple patterns with variables, conjunction,
union, `OPTIONAL` and the `bound` / `!bound` filters, evaluated by the standard
nested-loop semantics on solution mappings against the *truthy* projection — the
layer the query service exposes.

* pattern evaluation is exact (`mem_evalPattern_iff`) and sound: every answer
  comes from a truthy statement (`evalPattern_sound`);
* the **positive fragment is monotone** (`eval_mono`): patterns, conjunction,
  union and `bound` never lose an answer when data arrives;
* **`OPTIONAL` is not** (`optional_not_monotone`), and neither is `!bound`
  (`notBound_not_monotone`): the same query loses an answer when a statement is
  added.  So an answer obtained by negation as failure is an absence in the base
  that was queried — the absence-is-not-refutation discipline, now a theorem
  about the query language;
* the query reads a projection, not the base
  (`query_reads_the_truthy_layer`, `deprecated_statement_is_unanswerable`), and a
  triple pattern is not the instance relation
  (`query_does_not_close_over_subclasses`): recovering the class closure needs a
  property path, which this fragment deliberately does not model.

`RequestProject/Epistemic/QueryEvidence.lean` imports query answers as evidence:
support from a positive query is stable under growth
(`positive_support_is_stable`) and support from negation as failure is not
(`negation_as_failure_support_is_not_stable`), so only the former may be
transported to a larger base.

### Property characteristics (`RequestProject/Wikidata/Owl.lean`)

The OWL-level vocabulary Wikidata really carries outside the class fragment is
the property characteristics: transitive (`Q18647515`), symmetric (`Q18647518`)
and inverse (`P1696`).  A `Profile` records them, `Entails` is the resulting
entailment relation over the truthy triples, closure of a base under a profile is
decided by an exact checker (`closedOk_iff`), and on a closed base entailment is
exactly membership (`mem_of_entails_of_closed`).  With no characteristics
declared the relation is inert (`entails_empty_profile_iff`).  The boundary
results: declaring a property transitive or symmetric is **not conservative**
(`transitivity_is_not_conservative`, `symmetry_is_not_conservative`) — it is an
edit to the theory, to be review-gated like a class merge; an inverse declaration
makes the converse **derived rather than recorded**
(`converse_is_derived_not_recorded`); and class equivalence must **not** be
encoded as a subclass cycle (`equivalence_by_cycle_is_invalid`), since such a
base fails this project's own validity check.

### Still not modelled

The three SPARQL gaps this section originally listed — property paths,
aggregation and named graphs — are the subject of the eighth pass below.  What
remains outside the model is SPARQL's expression language (arithmetic and string
`FILTER`s, subqueries, federation) and OWL constructs beyond
the property characteristics and the class fragment.  Within the value types,
unit *conversion* is deliberately absent: the comparison refuses to compare
across units rather than converting, which is the conservative choice for a
checker that must not invent data.

## Eighth pass: property paths, counting and named graphs

The sixth pass closed with a negative result that named its own remedy: a triple
pattern is not the instance relation, because `?x P31 Q3` reads statements and
not the class closure, and what real Wikidata queries write instead is the
property path `wdt:P31/wdt:P279*`.  This pass builds that path, and the dataset
layer around it.

### Property paths (`RequestProject/Wikidata/SparqlPaths.lean`)

The fragment is the one the queries use: an elementary step forward (`p`) or
backward (`^p`), the empty path, sequence, alternation and the Kleene star of an
elementary step, with `p+` and `p?` on top.  Evaluation runs against the truthy
projection and reuses the project's fuel-bounded reachability engine, so a path
answer is decided by computation; `mem_targets_iff` proves the evaluator and the
declarative semantics are the same relation, which is what makes `Holds`
decidable.

The headline is that the path really is the closure: `star_P279_iff_subclassOf`
identifies `P279*` with the project's subclass relation and
`instancePath_iff_instanceOf` identifies `P31/P279*` with its instance relation,
in both directions.  The gap left open by `query_does_not_close_over_subclasses`
is therefore closed by a theorem rather than by a convention.  `holds_mono` says
the whole path fragment is positive — no path answer is ever withdrawn by the
arrival of data, in contrast with `OPTIONAL` and `!bound`.

The boundary results say what a path answer is not: `p*` relates every item to
itself and that reflexive answer is not data (`star_is_not_plus`), `^p` is not
`p` (`inverse_is_not_forward`), a path reads the truthy layer and so does not
traverse rank-shadowed or deprecated statements
(`path_reads_the_truthy_layer`, `path_does_not_traverse_deprecated`), and the
endpoint of a path answer need not be recorded anywhere
(`path_answer_is_derived_not_recorded`).  Counting is included in its `DISTINCT`
form, with `count_is_not_stable_under_growth`: every answer survives growth and
the count still changes, so an aggregate reports what the base holds when it is
asked and not a quantity in the world.

### Named graphs (`RequestProject/Wikidata/NamedGraphs.lean`)

A dataset is a list of statements each labelled with the graph it was loaded
into — which is where provenance lives when dumps are loaded one source per
graph.  A named graph is proved to be a *slice* in the sense of
`Slices.lean` (`mem_graph_iff_mem_restrict`, and
`graph_eq_restrict_of_functional` when no statement is recorded twice), so the
existing slice theory applies to it unchanged; `graph_ne_restrict_of_duplicate`
shows the label belongs to the record and not to the statement.

Facts of a graph are facts of the dataset (`subclassOf_of_graph`,
`instanceOf_of_graph`, `holds_of_graph`) — the safe, slice direction.  The
converse fails in an instructive way: with one edge of a subclass chain loaded
from each of two sources, the union derives the transitive fact and neither
source does (`derived_fact_need_not_hold_in_any_graph`, and its query form
`union_answer_is_not_a_graph_answer`).  What crossed the boundary between the
graphs is the derivation, not a datum, so a derived answer over a dataset is not
attributable to a source.

### Evidence over the new surface (`RequestProject/Epistemic/PathEvidence.lean`)

As in the earlier passes, the new surface joins the evidence discipline through
an exact checker: a supported path certificate really is a path answer
(`holds_of_supported`) and import stays fail-closed
(`state_ne_contradicted`).  Because every path is positive, the interesting
coordinate is no longer the shape of the query but the *scope* it was asked of:
support is stable under growth (`path_support_is_stable`), support inside a
named graph transfers to the dataset (`graph_support_transfers_up`), and support
over the dataset leaves both named graphs unresolved
(`dataset_support_is_not_graph_support`) — the attribution result again, this
time as a statement about evidence.

## Ninth pass: grouping and counting (`RequestProject/Wikidata/SparqlAggregation.lean`)

The eighth pass counted path answers and found the count unstable.  This pass
puts the whole aggregation layer on the core fragment and asks the monotonicity
question of it properly: projection onto a `SELECT` list, `DISTINCT`, `GROUP BY`
on the value of one variable, `COUNT` and `HAVING`.  Everything is exact —
`mem_groupOf_iff`, `mem_groupKeys_iff`, `mem_havingKeys_iff`,
`mem_distinctAnswers_iff` — and grouping really is a partition: distinct keys
share no solution (`groupOf_disjoint`), each group is a sublist of the answer
list (`groupOf_sublist`), and a key has a non-empty group exactly when it is a
group key (`countOf_pos_iff`).

The result worth having is where monotonicity stops.  `SELECT DISTINCT` and the
group keys inherit it (`distinctAnswers_mono`, `groupKeys_mono`): a projected
answer and a group key survive the arrival of data.  A *count* does not
(`countOf_not_monotone`: the surviving key's count goes from 1 to 2), and
therefore neither does `HAVING` — `having_not_monotone` exhibits a `HAVING
(COUNT(*) = 1)` answer over the smaller base which is withdrawn over the larger,
with `having_failure_is_growth` confirming the two bases are ordered and
distinct.  The point is that this happens on the *positive* fragment, where the
sixth pass proved answers are never withdrawn: monotonicity is a statement about
membership in the answer list and does not survive being pushed through a
function of that list.  A `HAVING` answer is a report on the current contents of
a database, never a fact about the world.

Two further boundary results say what a number is.  A count counts *solutions*,
not facts: the same fact reached along both branches of a `UNION` is counted
twice while the `DISTINCT` projection collapses it
(`count_counts_solutions_not_facts`, `distinct_collapses_the_duplicate`), so the
number depends on the query plan as well as on the data.  And a count is a count
of the truthy layer: deprecated and rank-shadowed statements are recorded and
uncounted (`count_ignores_deprecated`, `count_ignores_rank_shadowed`), so `0` is
not silence and the total is not a census of the base.

## Tenth pass: `MINUS` and `FILTER NOT EXISTS` (`RequestProject/Wikidata/SparqlNegation.lean`)

The sixth pass modelled SPARQL's oldest negation, `OPTIONAL` plus `!bound`.
Modern SPARQL has two more, and query authors treat them as synonyms: `MINUS`
subtracts a solution set, `FILTER NOT EXISTS` tests a pattern in the scope of the
current solution.  Both are defined here as the standard has them — `NOT EXISTS`
evaluates the inner pattern with the current solution substituted in, while
`MINUS` deletes a solution only when some right-hand answer is *compatible* with
it **and shares a variable with it** — and both are proved sound in the only
sense available to a subtraction: they return a sublist of the left-hand answers
(`notExists_sublist`, `minus_sublist`), with `mem_notExists_iff` and
`mem_minus_iff` pinning the semantics exactly.

The domain-overlap side condition is the whole difference, and it is a theorem
here rather than a footnote: with variables disjoint, `MINUS` removes *nothing*
and `NOT EXISTS` removes *everything*
(`minus_with_disjoint_variables_removes_nothing`,
`notExists_with_disjoint_variables_removes_everything`,
`minus_ne_notExists`), while with the variables shared the two agree
(`minus_agrees_when_variables_are_shared`).  Rewriting one into the other is a
change of query, not a change of syntax.

Both join `!bound` on the non-monotone side (`notExists_not_monotone`,
`minus_not_monotone`, with `negation_failures_are_growth` confirming the bases
are ordered), so every negation SPARQL offers reports an absence from the base
that was queried.  Finally `not_exists_does_not_close_over_subclasses`: the
engine derives that `Q1` is an instance of `Q3` and `FILTER NOT EXISTS { ?x P31
Q3 }` still returns it, because SPARQL negation denies a triple and not a
consequence — denying the consequence is what the property path of the eighth
pass is for.

## Eleventh pass: OWL class expressions (`RequestProject/Wikidata/ClassExpressions.lean`)

The class algebra of the second pass models what Wikidata *records* about a
named class — `union of`, `intersection of`, `disjoint union of` — and the
property characteristics of the sixth pass model OWL's property fragment.  The
other half of OWL's class fragment is the *expressions*: `C ⊓ D`, `C ⊔ D`, `¬C`,
`∃p.C` and `∀p.C`.  This pass adds them, with a declarative semantics `Sat`, an
executable `sat`, and `sat_iff` proving the two the same relation — which is what
makes satisfaction decidable and every example below a computation.

The named class is read through the project's own instance engine, so `cls c`
carries the subclass closure; the restrictions read the truthy *fillers* of a
property, so they carry only what is recorded.  That split is the source of the
results.  The positive fragment — named classes, intersection, union and `∃p.C` —
is monotone (`sat_mono`, on the lemma `mem_fillersOf_mono` that truthy fillers
only grow).  Complement is not (`complement_is_not_monotone`): `¬C` holds of an
item exactly while nothing has been recorded about it, so under this semantics a
complement is an absence and not a refutation.  Nor is the universal restriction:
`∀P31.⊥` is *true* of an item with no recorded type at all
(`universal_restriction_is_vacuous`) and false as soon as one arrives
(`universal_restriction_is_not_monotone`), while `∃p.C` is only ever gained
(`existential_restriction_is_gained`).  And the two layers must not be
conflated: the engine derives that `Q1` is an instance of `Q3` while
`∀P31.(cls Q3)` fails of `Q1`, because the recorded filler is the *subclass* `Q2`
(`restriction_does_not_close_over_subclasses`).

The pass closes by tying the expressions back to the recorded algebra, so that
the two are one theory rather than two: a recorded `intersection of` statement
entails the corresponding fact about the intersection expression
(`class_algebra_intersection_sound`), a recorded `union of` statement likewise
(`class_algebra_union_sound`), and recorded disjointness refutes the intersection
expression outright (`disjointness_refutes_the_intersection`).  The entailment
needs the statement: without it an item can satisfy the expression and belong to
no such class (`intersection_expression_needs_the_recorded_class`).

## Twelfth pass: blank nodes and simple entailment (`RequestProject/Wikidata/BlankNodes.lean`)

`Wikidata/Rdf.lean` gives the RDF layers of a knowledge base with ground triples
only.  RDF's other kind of term, the blank node, is the one genuinely logical
device in the data model: a graph is read as the existential closure of its
triples.  This pass adds it.

* **Syntax.**  `BTerm` (a name of `Rdf.Term`, or a blank node), `BTriple`,
  `BGraph`, and the instance mappings `Subst` from blank nodes to terms.
  Instantiation is functorial: `substGraph_id` and `substGraph_comp`.
* **Semantics.**  A model is presented as the graph of the triples it makes
  true; `Models I g` says some instance of `g` sits inside `I`, and `Entails g e`
  is "every model of `g` is a model of `e`".
* **The interpolation lemma** (`entails_iff_instance_subset`).  That
  model-theoretic relation coincides with the syntactic one — `g` entails `e`
  exactly when some instance of `e` is a subgraph of `g` — because `g` is its own
  canonical model (`models_self`).  Reflexivity, transitivity, monotonicity in
  the data (`entails_mono`) and the collapse to containment on ground conclusions
  (`ground_entails_iff_subset`) follow.
* **What a blank node is not.**  A blank node may be introduced for the object of
  any recorded triple (`entails_blank_generalisation`), but it is not a witness:
  the existential entails none of its instances (`blank_is_not_a_witness`).
  Hence entailment does not distribute over a union whose two halves share a
  blank node (`entails_union_needs_standardising_apart`) — which is exactly why
  the RDF merge operation standardises blank nodes apart — and two equivalent
  graphs can differ in size (`redundant_blank_is_removable`).
* **Leanness.**  `IsLean` says no proper subgraph entails the graph.  Ground
  graphs are lean (`ground_isLean`); the two-blank graph above is not
  (`twoBlanks_not_isLean`).
* **The merge.**  Standardising the blank nodes apart repairs that failure:
  `entails_merge_iff` proves that a graph entails the merge of two graphs exactly
  when it entails each of them, so the merge — and not the concatenation — is the
  conjunction of two graphs in the entailment preorder
  (`merge_repairs_the_shared_blank` is the failing example, repaired).
* **A decision procedure.**  `entailsCheck` searches the finitely many maps from
  the blank nodes of the conclusion into the terms of the premise;
  `entailsCheck_iff` proves it exact, and the resulting `Decidable` instance lets
  the kernel settle concrete entailments by `decide`.
* **The bridge back.**  The direct triples of a knowledge base embed into
  blank-node graphs, where they entail exactly themselves
  (`entails_embed_directTriples`), and blanking the object of a truthy statement
  is a consequence of the base that does not pin the object down
  (`kb_entails_blanked_object`).

Unlike the SPARQL operators of the eighth to tenth passes, simple entailment is
monotone: new data never withdraws a consequence.

## Seventh pass: reading the upstream Agda with Lean itself

Every pass above is a *port*: an upstream idea is restated in Lean and proved
there.  That leaves a question the porting cannot answer — how much of the
upstream source is Lean able to read *as it stands*?  This pass answers it, and
the answer is measured rather than asserted: the corpus is checked into
`upstream/dashi_agda`, an Agda front end for Lean is built in three layers, and
two generated Lean libraries put the corpus through it at build time, so the
coverage figures below are exactly what `lake build` verifies.

### The front end, in three layers

* `RequestProject/Agda/Prelude.lean` — the *vocabulary*: `Set`, `Set₁`, `Level`,
  `_≡_`/`refl`/`sym`/`trans`/`cong`, `⊥`, `⊤`, `_∷_`, and the rest of the small
  fragment the upstream development uses.  Each Agda name is *definitionally*
  the Lean one, and the theorems at the foot of the module check that, so the
  correspondence is proved and not merely declared.  Where the two foundations
  differ the module says so in the docstring rather than papering over it:
  Agda's `Set`-valued `⊥` and `_≡_` are rendered by Lean's `Prop`-valued `False`
  and `Eq`, which is what the upstream proofs need, and Agda's `Setω` has no
  exact Lean counterpart.
* `RequestProject/Agda/Syntax.lean` — the *grammar*: the Lean command
  `agda_module M where …`, accepting `data`, `record` with `constructor` and
  `field`, `open import M using (…)`, `open R public`, signature-plus-clauses
  definitions including absurd clauses, and Agda's arrow binders.  It elaborates
  to ordinary `inductive`/`structure`/`def` commands, so Lean's kernel checks the
  results exactly as if they had been written by hand.  It is a front end, not a
  second logic.
* `RequestProject/Agda/Verbatim.lean` — the same thing with the pre-pass moved
  *inside* Lean: `agda_verbatim r#"…"#` and `agda_include "path.agda"` take
  genuine Agda source, normalise it (comments, binder arrows, `import … as`,
  hyphenated identifiers, binary mixfix operators) at elaboration time, and
  elaborate the result.

Nothing is postulated anywhere in this layer.  A signature with no clauses is an
Agda `postulate`, and the front end *refuses* it with an error rather than
turning it into a Lean `axiom`; that refusal is the reason several upstream
modules are out of reach, and it is the right trade.

### Two routes over the corpus, and what each measures

| route | tool | output | what it shows |
| --- | --- | --- | --- |
| offline | `tools/agda2lean.py` | `AgdaVendor/` | the Agda rewritten into the `agda_module` front end, checked in, so the translation is auditable line by line |
| direct | `tools/agdacheck.py` | `AgdaCheck/` | Lean reading the raw `.agda` file itself at build time, with no pre-pass at all |

Both libraries are default `lake` targets, so both are rebuilt and kernel-checked
with the rest of the development.  Of the 1,055 Agda modules in the corpus, the
offline route carries 28 (one of which, `DASHI.Foundations.Base369Nat`, is a
hand-written shim whose docstring states what it stands in for and why the
rendering is faithful — it uses an instance argument the front end does not
cover), and the direct route carries 96.

Three generated reports record the measurement, each produced by the front end
itself rather than by a mirror of its rules written in Python:

* `docs/AGDA_FRONTEND_PARSE.txt` — which files the front end can *read*
  (608 of them), from `tools/AgdaParse.lean`;
* `docs/AGDA_FRONTEND_COVERAGE.txt` — the offline route, with every refusal and
  its reason;
* `docs/AGDA_DIRECT_CHECK.txt` — the direct route, likewise.

### What stops the rest, and why the number is small

Two effects dominate.  The first is *transitivity*: `AgdaCheck` attempts a module
only when every module it imports is attempted too, so a single refusal keeps
its whole downstream out — 483 modules are excluded for that reason alone, and
`tools/agdablame.py` ranks the refusals by how many modules each one blocks (the
worst blocks 433).  The second is the fragment itself: 322 modules use syntax the
front end does not read (`with`-abstraction, clause-level `where` blocks,
copatterns, `private`/`abstract` blocks) and 119 are refused explicitly, chiefly
for `postulate`.

A third, smaller class is modules that the front end *reads* but that do not
elaborate.  These are listed one by one, with the reason, in
`tools/agdacheck_skipped.txt`, so the gap is documented rather than hidden; there
are 19 of them and every one is a place where Agda's foundation or its scoping
differs from Lean's:

* **Prop versus Set** — an upstream abbreviation declared to land in `Set` whose
  body is a proposition, e.g. `x ≢ y = x ≡ y → ⊥`.  This is the visible price of
  the prelude's (deliberate, documented) `Prop` rendering of `⊥` and `_≡_`.
* **record-local mixfix** — a record field called `_+_`, `_≤_` or `-_` is a new
  operator scoped to that record; Lean fixes its token table before elaborating
  a command, so such an operator cannot be introduced from inside a declaration.
* **`open R v`** — Agda's record modules put a record value's fields into scope
  as bare names; Lean has no corresponding scoping, so those names are unbound.
* **vocabulary the prelude does not carry** — `Data.Vec`, the standard library's
  `≤-refl`/`z≤n`, negative float literals.
* **genuine dependent pattern matching** — absurd patterns away from the last
  argument, and matching on `refl` to force an index.

Refresh the whole measurement with

```
lake env lean tools/AgdaParse.lean > docs/AGDA_FRONTEND_PARSE.txt
python3 tools/agda2lean.py --emit  && python3 tools/agda2lean.py --report > docs/AGDA_FRONTEND_COVERAGE.txt
python3 tools/agdacheck.py  --emit && python3 tools/agdacheck.py  --report > docs/AGDA_DIRECT_CHECK.txt
```

## Provenance: which side of the port each declaration comes from

Since the port mixes three kinds of material — ideas taken from the DASHI Agda
bridge, the Wikidata data model itself, and constructions introduced here — the
attribution is now recorded rather than left implicit.

Each declaration whose idea comes from the bridge carries, immediately above it,
a comment of the form

    -- @source DASHI Agda bridge (PR #555/#581): <the upstream idea>

where the text is the very row of the correspondence tables above that the
declaration was traced to; and each module opens with a generated block stating
how many of its declarations come from each of the three sources.  Nothing about
the mathematics changed: these are comments.

The rule used is deliberately mechanical and auditable.  A declaration counts as
bridge-derived exactly when this file or the first section of `RELATED_WORK.md`
names it as the rendering of an upstream idea.  Otherwise it counts as Wikidata
material when it lives in a data-model module and states Wikidata vocabulary
(item and property identifiers, ranks, the truthy projection, statements, RDF,
constraints, identifiers, provenance), and as original to this port in every
other case — which is where the executable engines, their exactness theorems,
the generic epistemic machinery and the countermodels fall.

On the present state of the development that gives 244 bridge-derived, 781
Wikidata and 1,170 original declarations, out of 2,195 across 79 modules.

Two further artefacts come out of the same analysis:

* the **dependency graph** of the development, read off the compiled kernel
  environment rather than off the `import` lines, so that an edge means a
  declaration really uses another declaration.  It is rendered in
  `docs/status/dependencies.svg`, exported for Graphviz in
  `dependencies.dot`, and carried inside Lean — with its acyclicity proved —
  in `RequestProject/Meta/Provenance.lean`;
* the **needs** figures: for every declaration, the transitive set of project
  declarations its statement and proof depend on, split by source.  1,088 of the
  2,195 declarations (50%) need at least one bridge-derived declaration, 1,324
  (60%) need Wikidata material and 1,233 (56%) need something original to this
  port; the median support set has 6 declarations and the largest has 91.

`docs/status/PROVENANCE.md` has the full tables, including every bridge-derived
declaration with the idea it renders, and `docs/status/dashi.svg` is the
infographic version.  Regenerate the lot with

```
lake env lean tools/DepDump.lean && python3 tools/provenance.py --annotate
```

## Recovering the rest of the upstream branches

A later pass fetched *every* upstream branch, not just the pull request this
port started from, and asked mechanically what they carry that was not here.
`docs/UPSTREAM_RECOVERY.md` reports the survey and the vendoring; the summary
is that the corpus grew by 274 Agda modules (182 that exist only on a branch,
46 ontology/evidence modules a branch changes from `master`, and 46
`Ontology`/`Knowledge` modules of `master` itself), and that upstream has no
Wikidata-named module the corpus was missing.

Four ideas in the recovered material are about knowledge representation, and
each is rendered here as a theorem about the executable engine rather than as a
recorded claim:

| Recovered idea | Lean rendering |
| --- | --- |
| non-factorability survives further coarsening | `Epistemic.not_factorsThrough_postcomp` (`Epistemic/OrderDescent.lean`) |
| hidden update order does not descend through a surface it leaves fixed | `Epistemic.not_factorsThrough_orderedEndpoint`; on the ontology, `Wikidata.classSurface_cannot_decode_editOrder` (`Wikidata/EditOrder.lean`) |
| bounded accumulation is not the commitment threshold, and the threshold is not truth | `Epistemic.commitment_does_not_determine_state` (`Epistemic/Commitment.lean`) |
| capture without secrecy: a public rule surface with held interpretation | `Wikidata.isSubclassOf_submit_shadowed`, `Wikidata.answer_not_factorsThrough_unranked` (`Wikidata/Capture.lean`) |
| retrieval bias is not a formal defect | `Wikidata.defect_not_factorsThrough_retrieval`, `Wikidata.retrieval_not_factorsThrough_defect` (`Wikidata/Retrieval.lean`) |

The same pass re-ran the two Agda front-end routes over the enlarged corpus, so
the recovered modules are also carried mechanically: `AgdaVendor` (offline
transliteration, kernel-checked) and `AgdaCheck` (Lean reading the upstream
source directly) both grew.

A fifth recovered idea — that several receipts derived from one source episode
are not several confirmations, and that a change at a source carries a
reopening obligation down the dependency closure — is
`RequestProject/Epistemic/Independence.lean`
(`Epistemic.naive_counting_commits_independent_does_not`,
`Epistemic.reopens_iff_transGen`).
