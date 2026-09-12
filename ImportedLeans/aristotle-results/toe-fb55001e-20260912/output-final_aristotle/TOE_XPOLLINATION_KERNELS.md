# Cross-pollination round: eleven kernel owners for recurring motifs

This round does two things.

1. It closes the one **documentation overstatement** identified in the review of
   the previous tranche, by adding the object the overstated sentence was
   describing and proving the theorem about it.
2. It extracts, into `Integration.Kernel.*`, the generic theorem-bearing shape
   of the Agda work that the Lean integration layer did not yet own — plus four
   further owners for motifs that recur, in different vocabulary, across
   several lanes.

Everything below is Lean 4 / Mathlib, sorry-free, and audited by
`Integration.AxiomAuditKernel`.  Nothing in this round transports an Agda proof
term: where an Agda module motivated a Lean owner, the section "What the Agda
source actually contains" in that Lean file states exactly what the Agda side
has and what it does not.

---

## 0. The claim-surface correction

`Integration.Kernel.Instances.SourceStage` previously had

```lean
theorem no_combination_of_non_proof_carriers
    (c : Carrier) (h : c ≠ Carrier.checkedProofTerm) : Inhabits c = false
```

documented as "rules out the other three jointly".  It did not: it quantified
over carriers one at a time, and there was no bundle, set, list or aggregation
rule anywhere in the module.  Fixed by doing both of the things the review
suggested:

* the per-carrier statement is renamed
  **`every_non_proof_carrier_fails_to_inhabit`**, and its docstring says
  explicitly that it is a statement about carriers one at a time;
* a bundle really is introduced —

  ```lean
  abbrev Bundle : Type := Finset Carrier
  def BundleInhabits (S : Bundle) : Prop := Carrier.checkedProofTerm ∈ S
  ```

  with `bundleInhabits_iff_exists_member` (a bundle inhabits exactly when one of
  its members does, so possession is not additive),
  `bundle_without_proof_term_does_not_inhabit`,
  `bundleInhabits_insert_of_ne` (adding non-proof carriers never moves the
  predicate), and the name `no_combination_of_non_proof_carriers` now carrying

  ```lean
  theorem no_combination_of_non_proof_carriers : ¬ BundleInhabits nonProofBundle
  ```

  for `nonProofBundle = {externalMachineReceipt, externalNumericCertificate,
  statementCorrespondence}`.

`TOE_CONSUMER_QUOTIENT.md` is corrected in the same terms and records that the
earlier wording overstated the theorem.  `Inhabits` and `BundleInhabits` remain
**stipulated predicates on finite labels**; nothing in the module inspects a
Lean term, environment, proposition or proof object.  `SourceStage` now has 25
theorems (was 20).

---

## 1. What was extracted, and from what

The 6 September Agda tranche shipped with this project
(`toe-dashi-agda-tranche-20260906-from-f2eb0e61.tar.gz`) is the source read for
this round; the `Agda/` tree in the repository is the earlier snapshot and does
not contain these modules.  The archive was **read but deliberately not merged**
into `Agda/`: it also contains Navier–Stokes closure modules
(`DASHI/Physics/Closure/NSTriad*`), which this cutset excludes, so unpacking it
wholesale would reintroduce excluded material.  Only the modules named in the
table below were read, and only for their generic shape.  Each Lean file names its motivating Agda module and
states the boundary.

| new Lean owner | motivating Agda module (6 Sep tranche) | what the Agda side actually has | what is Lean-side new |
| --- | --- | --- | --- |
| `Integration.Kernel.EvidenceDependence` | `DASHI/Biology/DrosophilaSameTrialProvenanceDependenceExact.agda` | `ProvenanceRootKind`/`EvidenceRelation`/`DependenceBoundary` datatypes; `ProvenanceGraph` with `sharedRoot`, `sharedRootSound` as **`Set`-valued interface fields**; `EvidenceDependenceAssessment` with the independence rules as **`Bool` fields with `≡ true`/`≡ false` obligations**; `DependenceAwareResidualAggregation` as a record of aggregation *functions* | roots as a `Finset`; independence **defined** as disjointness; the blocking rule proved; non-transitivity of root sharing proved; the class discipline that licenses two-stage aggregation proved; count-vs-support non-descent |
| `Integration.Kernel.ConsumerPromotion` | `DASHI/Biology/DrosophilaConsumerIndexedEvidencePromotionExact.agda` | `EvidenceConsumer`, `EvidenceChannel`, a genuine `required`/`optional` policy; but `allRequiredPresent`, `provenanceAdequate`, `promotionAdmissible`, `transferAdmissible` are **`Bool` fields** | adequacy **computed** from the policy; `bridge_iff_transfers` (transfer for all bundles ⇔ a bridge exists); receipts carrying a **proof** of adequacy; adequacy non-descent through the bundle |
| `Integration.Kernel.QueryResidual` | `DASHI/Cognition/PNF/SensibLawIssueIndexedAdjudicativeHyperfabricExact.agda` | a real executable `firstAdjudicativeResidual : Query → Cutset → Residual` cascade, plus `discriminatorFor`/`workKindFor` total matches — for one fixed legal vocabulary, with no theorems about the compiler | generic compiler over arbitrary types; residual proved to be in the query's own cutset and open; closure characterised; resolution proved to remove the residual; residual proved to be a function of the **pair** and of neither coordinate |
| `Integration.Kernel.PartialIdentification` | `DASHI/Cognition/PNF/SensibLawLegalOutcomeIdentifiabilityBidiExact.agda` | `outcomeDegeneracyRefutesGlobalIdentifiability` is a **real proof**; the fibre/consumer-goal half is a `Bool` field read by `goalStatus` on one fixture, and the boundaries are empty-type `→ ⊥` declarations | the compatible fibre as a first-class object: soundness, singleton ⇔ point identification, the set-valued answer proved to descend while the point answer does not, and reopening to a singleton via `Kernel.Quotient.Reopening` |
| `Integration.Kernel.BoundaryKind` | `DASHI/Core/KnowledgeBoundaryKindBidiExact.agda` | `BoundaryKind` datatype and `TypedBoundaryTransition` are real; the inequalities live in `BoundaryKindBoundary` as **`Bool` fields with `≡ false`** | generic orthogonality of transition and mechanism, the "only constants descend" strengthening, and the seven-label instance with the named inequalities proved |
| `Integration.Kernel.Instances.ProjectionHierarchy` | the joint-conditional-missingness lane (already conceptually crossed: `Integration.SourceExactWelds.marginals_do_not_determine_interaction`) | — | the **hierarchy** rather than another interaction kernel: one-way < pairwise < full joint, with descent proved upward and both strictness witnesses (a contrast pair and the two parity cubes) |

Four further owners are motifs, not single-module extractions.  They were built
because the same shape appears independently in several lanes:

| new Lean owner | the motif |
| --- | --- |
| `Integration.Kernel.DeclaredRealised` | declared ≠ authorised ≠ acknowledged ≠ realised, and the outcome test belongs to the consumer |
| `Integration.Kernel.AppendOnlyHistory` | repair adds history rather than rewriting provenance; a state snapshot is a quotient of the log |
| `Integration.Kernel.BraidedTrace` | strands coordinated without fusion; a crossing must commute with a declared invariant or it is free |
| `Integration.Kernel.LineageEdge` | edge semantics matter: amplification is not generation, and a chain of non-generative edges adds no root |
| `Integration.Kernel.PromotionTransport` | promotion is four obligations, not one: the artefact exists, it corresponds to the statement, the statement transport is sound, and a term inhabits the target |

`PromotionTransport` is the "evidence-promotion/transport receipt kernel" the
review of the previous tranche named as the next extraction.  Its point is
`holds_does_not_give_inhabitance`: even with the first three obligations
discharged for every statement, the target can hold and no term inhabit it, so
external evidence never closes the fourth step by itself.  A `Receipt` carries
all four as proofs and is the only thing in the file that yields a term.

---

## 2. Dependency map

```
Integration.Kernel.ResidualFibre
        │
        ▼
Integration.Kernel.Quotient ─────────────────────────────────────────────┐
   │        │          │            │            │           │           │
   ▼        ▼          ▼            ▼            ▼           ▼           ▼
Evidence  Query    Partial      Boundary     Declared    AppendOnly   Braided
Dependence Residual Identification Kind       Realised    History      Trace
                                                                   PromotionTransport
   │  │                                                                  
   │  └────────────────────────► Instances.ProjectionHierarchy (independent)
   ▼
ConsumerPromotion         LineageEdge
(imports EvidenceDependence)  (imports EvidenceDependence)
```

Every one of the eleven files imports only `Integration.Kernel.Quotient` or
`Integration.Kernel.EvidenceDependence` (which itself imports only
`Quotient`).  All are imported by the `Integration` aggregate and audited in
`Integration.AxiomAuditKernel`.

Welds actually used (not just referenced in prose):

* `ConsumerPromotion.independence_required_is_a_separate_gate` uses
  `EvidenceDependence.Independent` and its blocking theorem: channel adequacy
  and provenance independence are proved to be two different gates.
* `LineageEdge.amplified_copies_are_not_independent_replication` derives an
  `EvidenceDependence` non-independence from the typed-edge propagation law.
* `PartialIdentification.reopening_gives_point_identification` consumes
  `Quotient.Reopening.fibre_pair_eq_singleton`.
* `ProjectionHierarchy` and every non-descent in the round go through
  `Quotient.not_descendsThrough_of_collision` /
  `Quotient.descendsThrough_iff_refinedBy`.

---

## 3. Headline theorems

* `EvidenceDependence.shared_root_blocks_independent_replication`,
  `sharesRoot_not_transitive`, `independent_of_different_class`,
  `count_does_not_determine_root_support`, `amplification_is_not_generation`.
* `ConsumerPromotion.bridge_iff_transfers`, `adequacy_is_consumer_relative`,
  `receipt_does_not_transfer_without_bridge`,
  `adequacy_does_not_descend_through_bundle`.
* `QueryResidual.closed_iff_all_closed`, `resolve_removes_residual`,
  `residual_does_not_descend_through_state`,
  `residual_does_not_descend_through_query`, `residual_descends_through_pair`.
* `PartialIdentification.pointIdentified_iff_compatible_singleton`,
  `fibre_answer_descends`, `fibre_closes_while_point_stays_open`,
  `reopening_gives_point_identification`.
* `BoundaryKind.released_publicly_does_not_determine_mechanism`,
  `no_transition_level_test_separates_mechanisms`,
  `like_for_like_requires_the_kind_coordinate`.
* `ProjectionHierarchy.oneWay_descends_through_pairwise`,
  `pairwise_does_not_descend_through_oneWay`,
  `cube_does_not_descend_through_pairwise`, `hierarchy_is_strict`.
* `DeclaredRealised.no_link_of_the_chain_is_automatic`,
  `acknowledgement_alone_is_not_a_receipt`,
  `success_is_not_a_function_of_the_world`.
* `AppendOnlyHistory.earlier_entries_unchanged`,
  `rewriting_is_not_an_extension`, `state_does_not_determine_history`.
* `BraidedTrace.pool_does_not_determine_authority`,
  `every_pair_admits_a_trivial_crossing`,
  `no_lawful_crossing_of_different_invariant`.
* `LineageEdge.roots_constant_along_amplification`,
  `amplified_copies_are_not_independent_replication`,
  `edge_kind_does_not_descend_through_roots`.
* `PromotionTransport.holds_of_corresponds_and_sound`,
  `artifact_does_not_give_correspondence`,
  `correspondence_does_not_give_transport_soundness`,
  `holds_does_not_give_inhabitance`, `first_three_do_not_close_the_fourth`,
  `receipt_yields_term`, `receipt_needs_all_four`.

Counts: 147 theorems across the eleven new files (`EvidenceDependence` 19,
`AppendOnlyHistory` 16, `BoundaryKind` 16, `QueryResidual` 16,
`ConsumerPromotion` 14, `PartialIdentification` 14, `DeclaredRealised` 12,
`ProjectionHierarchy` 12, `LineageEdge` 11, `BraidedTrace` 9,
`PromotionTransport` 8), plus five added to `SourceStage`.

---

## 4. Build and audit receipt

Reproduced in this environment:

* `lake build Integration` — **8 265 jobs, no errors**.
* `lake build Synthesis` (8 108), `lake build Spine` (8 049), `lake build Cuisine`
  (8 078) and `lake build Promoted` (8 085) — no errors.
* `Integration.AxiomAuditKernel` now emits **406** `#print axioms` lines; the
  complete set of axiom multisets reported across all of them is
  `[]`, `[propext]`, `[Quot.sound]`, `[Classical.choice]`,
  `[propext, Quot.sound]`, `[propext, Classical.choice, Quot.sound]` — i.e.
  every line is a subset of `{propext, Classical.choice, Quot.sound}`.
* `rg "sorry|^axiom |native_decide|implemented_by" Lean/Integration/Kernel/`
  — no matches.

**Pre-existing, not introduced here:** `lake build` on the default target set
fails during job computation for the `AgdaMirror` library, because
`Lean/AgdaMirror/Physics/YangMills.lean` is imported by that tree but absent
from this cutset (it is excluded by the Yang–Mills/Navier–Stokes filter).  The
lakefile and the `AgdaMirror` tree are untouched by this round, and repairing
that target would mean reintroducing the excluded material, which is out of
scope.  Every other default target builds.

---

## 5. Honest frontier

What these files do **not** do:

* **Nothing is transported across languages.**  No Agda proof term is checked,
  imported or mirrored here; no Agda toolchain is available in this
  environment, so no Agda module is claimed to have been rechecked this round.
  The Agda modules named above were *read* as sources of architecture.
* **Every classifier is stipulated.**  `Inhabits`, `BundleInhabits`,
  `Generative` and the `Mechanism`/`EdgeKind`/`Stage` label types record
  distinctions this corpus wants to keep; none of them inspects a term, a
  kernel environment, a document, an experiment or a world.
* **The finite fixtures are fixtures.**  `twoConsumerPolicy`,
  `twoQueryCompiler`, `starLineage`, the parity cubes and the `Episode`
  constants exist to make existential statements true; they are not models of
  anything.
* **`Provenance`, `Policy`, `Compiler` and `Lineage` are interfaces.**  A
  domain lane that wants these theorems has to supply the data and, for
  `Lineage`, discharge `amplification_preserves_roots` — that field is a `Prop`
  obligation precisely so it cannot be asserted.  Only `Lineage`'s law is
  currently discharged by an in-file instance (`starLineage`,
  `generativeLineage`); no domain instance of any of the four interfaces exists
  yet.

Exact remaining obligations this round leaves open:

1. **No domain instance.**  None of `EvidenceDependence.Provenance`,
   `ConsumerPromotion.Policy`, `QueryResidual.Compiler` or
   `LineageEdge.Lineage` is instantiated by a real corpus lane.  The natural
   first ones are the Drosophila channel policy and the adjudicative cutset,
   both of which exist in Agda as concrete data.
2. **`ClassSeparates` is a hypothesis, not a construction.**  The two-stage
   aggregation theorem assumes a dependence-respecting class map.  Building one
   from a provenance graph — the transitive closure of root sharing — and
   proving it minimal is not done.
3. **Aggregation itself is not modelled.**  `EvidenceDependence` proves *when*
   units may be treated as independent; it does not define a numerical
   aggregate or prove anything about combining residuals.
4. **`ConsumerPromotion` has no partial-order of consumers from data.**
   `Bridge` is proved to be a preorder, but no lane supplies its consumers, and
   the connection to `Integration.PromotionEvidence`'s registry rows is by
   architecture only: no registry row is reclassified.
5. **`QueryResidual` proves no progress/termination theorem.**  Resolving the
   first residual is proved to remove *that* residual; that the loop terminates
   under repeated resolution, and that the produced work discharges the
   obligation, are not proved.
6. **`PartialIdentification` has no measure of how partial.**  The fibre is
   returned; nothing bounds its size or ranks candidates, and the "rare residual
   carries decisive information" question is not formalised at all.
7. **`BraidedTrace` invariants are supplied, not derived.**  A lawful crossing
   commutes with an invariant the user chooses; there is no theory of which
   invariant is the right one, and nothing here models authority, permission or
   reciprocal obligation as anything other than a label attached to an index.
8. **`LineageEdge` has no reachability/closure algebra.**  `AmplifiedFrom` is
   the non-generative reachability relation; generative reachability, mixed
   paths, and "how many independent generative sources does this node have" are
   not defined.
9. **`PromotionTransport` has no frame from the corpus.**  `Holds` and
   `Inhabits` are supplied by the frame; the file deliberately does not
   interpret them as Lean truth and Lean proof, and no lane supplies a frame.
   Connecting a frame to `Integration.PromotionEvidence`'s receipt types is the
   obvious next step and is not done.
10. **`DeclaredRealised` does not connect to `Kernel.Reopen`.**  The selective
   reopening of failed coordinates is owned by `Kernel.Reopen` and referenced in
   prose; no theorem here links an unrealised coordinate to the certificates it
   should reopen.

Deliberately **not** attempted this round, and why:

* A `listen`/`deliberate` operation for the think/look/test/act controller.  It
  is a good idea, but its content is that an agent's situated perspective
  changes the *state*, not just the information — that needs a model of
  multi-agent state revision, which does not exist here and would be a lane of
  its own rather than a kernel extraction.
* Anything quantitative about a "small residual carrying decisive information"
  (the regular-bulk/residual pattern).  Formalising *information per state*
  requires a measure the kernel does not have; the qualitative half is already
  covered by the collision/descent machinery.
* The speculative physical bridges (self-limiting cycles ↔ consensus,
  charging ↔ path-dependent response, interference ↔ multi-source
  corroboration, quorum sensing ↔ thresholds).  These are analogies without a
  stated common structure yet; the honest move is to leave them on the
  whiteboard rather than to formalise a resemblance.
* Yang–Mills and Navier–Stokes material, in any form.
