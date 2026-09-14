import Integration.ProvenanceIdentifier

/-!
# The Lean ↔ Agda lineage ledger

`Agda owner → Lean carrier → Lean adapter → Lean consumer → proof/status →
provenance`, as a typed Lean value with checked policy theorems.

The Agda owner of this shape is
`DASHI.Interop.CrossLaneProofArchaeologyLedgerExact`, whose `ClayLaneRouter`,
`DatedAnchor`, `PaymentStatus`, `IdentityStatus` and `IbrahimPolicy` records
carry the same columns.  Three of that module's discipline clauses are `Bool`
fields pinned by `refl` (`sourceIdentityCoordinateOnly`, `qidCoordinateOnly`,
`deweyCoordinateOnly`, `firstLinkCreatesTheoremImplication = false`,
`funnelRankCreatesAuthority = false`).  Here they are **theorems** instead:
`Integration.ProvenanceId.provenance_does_not_determine_status` and its
companions, applied to this ledger in `ledger_status_not_a_function_of_provenance`
below.

What the rows are, and are not:

* a row is a bookkeeping statement about *where a structure lives*, not a
  mathematical claim.  Its `status` field records which of the seven classes the
  underlying content belongs to, and the three Lean-asserting classes carry the
  Lean declaration name, so a row cannot claim closure without a receipt;
* the receipts themselves are the `#print axioms` lines of the corresponding
  audit modules (`Spine.AxiomAudit`, `Synthesis.AxiomAudit`, `Cuisine.AxiomAudit`,
  `Welds`), not anything asserted here;
* `openPayment` and `falsePinned` rows are *retained deliberately*.  The
  `falsePinned` ones quote in-corpus Boolean ledger flags that are literally
  `false` in the Agda source (`round584ClayPromotion`,
  `round584AnyLiveNestedSlotClassNormPaymentConstructed`,
  `round504ClayPromotion`, `clayYangMillsPromoted`), i.e. explicit records of
  non-payment.  No Clay problem is claimed here in any direction.

Policy theorems proved below, all by kernel computation over the finite ledger:

* `canonical_ownership` — **no parallel definitions**: two rows with the same
  structure key name the same Lean carrier;
* `proved_rows_name_a_receipt` — every row whose status asserts Lean content
  names a Lean declaration;
* `receipted_rows_have_a_consumer` — and names an actual consumer, so a carrier
  is never registered as closed without something that uses it;
* `payments_have_no_receipt` — open/false-pinned/conjectural rows carry no Lean
  receipt;
* `ledger_status_not_a_function_of_provenance` — the firewall, instantiated:
  the ledger contains rows with identical provenance and different status, so
  no identifier scheme can be read as conferring proof status.
-/

namespace Integration.Lineage

open Integration.ProvenanceId

/-! ## 1.  Lanes and rows -/

/-- The retained lanes of the garden. -/
inductive Lane
  | navierStokes | yangMills | riemannHypothesis | grQuantum
  | monsterMoonshine | cuisine | education | ontologyWikidata | biology | law
  | cognition | chemistry | governance | physicsGeneral | provenanceMeta
  deriving DecidableEq, Fintype, Repr

/-- One lineage row.  `leanCarrier` is the canonical owner of `structureKey`;
`""` in an optional slot means "none recorded", which the policy theorems then
constrain. -/
structure Row where
  lane : Lane
  /-- The abstract structure the row is about.  Canonical ownership is keyed on
  this, not on the module name. -/
  structureKey : String
  /-- The Agda module that owns (or owned) the structure, `""` if Lean-native. -/
  agdaOwner : String
  /-- The canonical Lean carrier module or declaration. -/
  leanCarrier : String
  /-- The thin adapter, if the consumer needs one. -/
  leanAdapter : String
  /-- The actual consumer that factors through the carrier. -/
  leanConsumer : String
  /-- Hypotheses the row's content is conditional on. -/
  hypotheses : List String
  status : ProofStatus
  provenance : List Ident
  /-- Predecessor/supersession relation, `""` if none. -/
  supersedes : String
  /-- Named unresolved payments. -/
  payments : List String
  deriving DecidableEq, Repr

private def agda (m : String) : Ident := ⟨Scheme.agdaModule, m⟩
private def lean (m : String) : Ident := ⟨Scheme.leanModule, m⟩

/-! ## 2.  The ledger -/

/-- The lineage ledger.  Every Lean name occurring in a `provedTheorem`,
`conditionalCompiler` or `noGo` status is a declaration that exists in this
project and is printed in one of the axiom-audit modules. -/
def ledger : List Row :=
  -- Navier–Stokes -----------------------------------------------------------
  [ { lane := .navierStokes
    , structureKey := "rate-block-schur-kernel"
    , agdaOwner := "DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact"
    , leanCarrier := "Spine.RateBlockSchur"
    , leanAdapter := "ClayNS.SpineAdapter.sum_resForm_le_blockMultiplicity_ofSpine"
    , leanConsumer := "ClayNS.Schur.GramOperatorBound"
    , hypotheses := ["DyadicRateBlocks lam modes blk", "BlockMultiplicity modes blk m",
                     "0 < nu", "wsq p ≠ 0 on modes"]
    , status := .conditionalCompiler
        "ClayNS.SpineAdapter.gramOperatorBound_of_rateBlockMultiplicity_ofSpine"
        ["DyadicRateBlocks", "BlockMultiplicity", "0 < nu", "wsq ≠ 0"]
    , provenance := [agda "DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact",
                     lean "RequestProject.NavierStokes.SpineRateBlockAdapter"]
    , supersedes := "RequestProject.NavierStokes.RateBlockGramBound (private copy of the kernel)"
    , payments := ["truncation-uniform constant must come from signed Gram cancellation"] }
  , { lane := .navierStokes
    , structureKey := "euclidean-pi-carrier"
    , agdaOwner := ""
    , leanCarrier := "Spine.RateBlockSchurPiCarrier"
    , leanAdapter := "Welds.NSRateBlockPi.herm_eq_hermPi"
    , leanConsumer := "ClayNS.Schur.GramOperatorBound"
    , hypotheses := []
    , status := .provedTheorem "Welds.NSRateBlockPi.ns_herm_eq_euclidean_inner"
    , provenance := [lean "Spine.RateBlockSchurPiCarrier", lean "Welds.NSRateBlockPiWeld"]
    , supersedes := "the `Fin 3 → ℂ` sup-norm carrier mismatch recorded in SpineRateBlockAdapter"
    , payments := [] }
  , { lane := .navierStokes
    , structureKey := "gram-consumer-from-pair-estimate"
    , agdaOwner := ""
    , leanCarrier := "Welds.NSRateBlockPi.gramOperatorBound_of_pair_estimate"
    , leanAdapter := "Welds.NSRateBlockPi.gramOperatorBound_viaPiCarrier"
    , leanConsumer := "ClayNS.Schur.GramOperatorBound"
    , hypotheses := ["the rate-block pair estimate at lam = viscousPairRate", "0 < nu",
                     "wsq p ≠ 0 on modes"]
    , status := .conditionalCompiler "Welds.NSRateBlockPi.gramOperatorBound_viaPiCarrier"
        ["pair estimate", "0 < nu", "wsq ≠ 0"]
    , provenance := [lean "Welds.NSRateBlockPiWeld"]
    , supersedes := "two inline copies of the viscous-rate massaging"
    , payments := [] }
  , { lane := .navierStokes
    , structureKey := "gram-ledger-two-presentations"
    , agdaOwner := "DASHI.Physics.Closure.NSTriadKNPartnerBlockGramLedgerRound181Exact"
    , leanCarrier := "Spine.GramLedger"
    , leanAdapter := ""
    , leanConsumer := "Spine.GramLedger (list recursion ≡ Finset double sum)"
    , hypotheses := ["real inner-product space"]
    , status := .provedTheorem "Spine.GramLedger.gramList_eq_gramSum"
    , provenance := [agda "DASHI.Physics.Closure.NSTriadKNPartnerBlockGramLedgerRound181Exact"]
    , supersedes := ""
    , payments := [] }
  , { lane := .navierStokes
    , structureKey := "slot-kernel-anti-parallel"
    , agdaOwner := "DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact"
    , leanCarrier := "RequestProject.NavierStokes.SlotKernelAntiParallel"
    , leanAdapter := ""
    , leanConsumer := "RequestProject.NavierStokes.TransverseFrameSplit"
    , hypotheses := ["anti-parallel helicity slot geometry"]
    , status := .conditionalCompiler "RequestProject.NavierStokes.SlotKernelAntiParallel"
        ["slot geometry hypotheses of the module"]
    , provenance := [agda "DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact"]
    , supersedes := ""
    , payments := ["R145 intra-shell L² aggregation"] }
  , { lane := .navierStokes
    , structureKey := "nested-slot-class-norm-payment-584"
    , agdaOwner := "DASHI.Physics.Closure.NSTriadKNNestedSlotBonyClassNormBidiRound584Exact"
    , leanCarrier := ""
    , leanAdapter := ""
    , leanConsumer := ""
    , hypotheses := []
    , status := .falsePinned "round584AnyLiveNestedSlotClassNormPaymentConstructed = false"
    , provenance := [agda "DASHI.Physics.Closure.NSTriadKNNestedSlotBonyClassNormBidiRound584Exact"]
    , supersedes := ""
    , payments := ["nested-slot class-norm payment", "outer weight / spectator spacetime seam",
                   "round584ClayPromotion = false"] }
  , { lane := .navierStokes
    , structureKey := "clay-terminal-cutset-504"
    , agdaOwner := "DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact"
    , leanCarrier := ""
    , leanAdapter := ""
    , leanConsumer := ""
    , hypotheses := []
    , status := .falsePinned "round504ClayPromotion = false"
    , provenance := [agda "DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact"]
    , supersedes := ""
    , payments := ["round504SignedCrossPaymentClosed = false",
                   "round504CriticalProductionSliceClosed = false"] }
  , { lane := .navierStokes
    , structureKey := "centered-partner-difference-route"
    , agdaOwner := "DASHI.Physics.Closure.NSTriadKNCenteredPartnerDifferenceAdapterExact"
    , leanCarrier := ""
    , leanAdapter := ""
    , leanConsumer := ""
    , hypotheses := []
    , status := .openPayment "no Lean carrier: centered partner-difference route not transported"
    , provenance := [agda "DASHI.Physics.Closure.NSTriadKNCenteredPartnerDifferenceAdapterExact",
                     agda "DASHI.Physics.Closure.NSTriadKNCenteredPartnerSlotDefectExact"]
    , supersedes := ""
    , payments := ["centered partner-difference slot-defect transport to a Lean carrier"] }
  , { lane := .navierStokes
    , structureKey := "gronwall-comparison"
    , agdaOwner := ""
    , leanCarrier := "Spine.GronwallComparison"
    , leanAdapter := ""
    , leanConsumer := "Spine.GronwallComparison.le_div_radius_of_deriv_le"
    , hypotheses := ["differentiable comparison function", "derivative inequality"]
    , status := .conditionalCompiler "Spine.GronwallComparison.le_div_radius_of_deriv_le"
        ["deriv ≤ hypothesis"]
    , provenance := [lean "Spine.GronwallComparison"]
    , supersedes := "the historical DASHI enstrophy/BKM chain (ns1_enstrophy_passage)"
    , payments := [] }
  , { lane := .navierStokes
    , structureKey := "gram-profile-consumer-factorisation"
    , agdaOwner := ""
    , leanCarrier := "Proposed.FibreRoutingProjectionAdapter"
    , leanAdapter := "RequestProject.NavierStokes.GramConsumerFactorisation"
    , leanConsumer := "ClayNS.Schur.GramOperatorBound"
    , hypotheses := ["the consumer reads only the signed Gram profile"]
    , status := .conditionalCompiler "RequestProject.NavierStokes.GramConsumerFactorisation"
        ["consumer reads the Gram profile only"]
    , provenance := [lean "Proposed.FibreRoutingProjectionAdapter"]
    , supersedes := ""
    , payments := ["masses alone provably cannot pay the consumer (retained no-go)"] }
  -- Yang–Mills ---------------------------------------------------------------
  , { lane := .yangMills
    , structureKey := "ym-clay-promotion"
    , agdaOwner := "DASHI.Physics.YangMills (Balaban round owners)"
    , leanCarrier := "AgdaMirror.Physics.YangMills.YMSourceAuthoritySurface"
    , leanAdapter := ""
    , leanConsumer := "AgdaMirror.Physics.YangMills.ProofTargetSurface"
    , hypotheses := []
    , status := .falsePinned "clayYangMillsPromoted = false"
    , provenance := [lean "AgdaMirror.Physics.YangMills.YMSourceAuthoritySurface"]
    , supersedes := ""
    , payments := ["continuum construction", "mass gap", "one-sided Hessian obligations"] }
  , { lane := .yangMills
    , structureKey := "ym-quantitative-clustering"
    , agdaOwner := "DASHI.Physics.YangMills.BalabanClayDirectQuantitativeClusteringRound274Exact"
    , leanCarrier := ""
    , leanAdapter := ""
    , leanConsumer := "DASHI.Physics.YangMills.BalabanClayCanonicalMassGapConsumerRound270Exact"
    , hypotheses := []
    , status := .openPayment "quantitative clustering → mass gap chain has no Lean carrier"
    , provenance := [agda "DASHI.Physics.YangMills.BalabanClayDirectQuantitativeClusteringRound274Exact",
                     agda "DASHI.Physics.YangMills.BalabanPairwiseClusteringStandardMassGapRound305Exact"]
    , supersedes := ""
    , payments := ["CMP98/CMP109/CMP116 source-object binding", "Path 13 vs Path 4 selection"] }
  -- Riemann ------------------------------------------------------------------
  , { lane := .riemannHypothesis
    , structureKey := "taper-second-moment"
    , agdaOwner := "DASHI.Analysis.RiemannG2FinalNearLiteralKernelExact"
    , leanCarrier := "Spine.RiemannBridge"
    , leanAdapter := ""
    , leanConsumer := "Spine.RiemannBridge.taper_cosh_excess_ge"
    , hypotheses := ["plateau taper hypotheses of the module"]
    , status := .conditionalCompiler "Spine.RiemannBridge.plateau_second_moment_ge"
        ["taper plateau hypotheses"]
    , provenance := [agda "DASHI.Analysis.RiemannG2FinalNearLiteralKernelExact"]
    , supersedes := ""
    , payments := ["explicit-cutoff near/far transport onto the Agda carrier"] }
  , { lane := .riemannHypothesis
    , structureKey := "rh-statement"
    , agdaOwner := "DASHI.Interop.CrossLaneProofArchaeologyLedgerExact (rhRouter)"
    , leanCarrier := ""
    , leanAdapter := ""
    , leanConsumer := ""
    , hypotheses := []
    , status := .conjectural "RH remains unproved; the Agda Lean-return receipt is provenance"
    , provenance := [agda "DASHI.Interop.CrossLaneProofArchaeologyLedgerExact"]
    , supersedes := ""
    , payments := ["signed finite near payment", "same-taper Gamma precision"] }
  -- Monster / moonshine -------------------------------------------------------
  , { lane := .monsterMoonshine
    , structureKey := "monster-order-factorisation"
    , agdaOwner := "DASHI.Moonshine (Monster order owners)"
    , leanCarrier := "Synthesis.MonsterOrder"
    , leanAdapter := ""
    , leanConsumer := "Spine.JMD.MonsterMoonshine"
    , hypotheses := []
    , status := .provedTheorem "Synthesis.MonsterOrder.monsterOrderNumeral_primeFactors"
    , provenance := [lean "Synthesis.MonsterOrder"]
    , supersedes := "a `native_decide` numeral check in the JMD archive module"
    , payments := [] }
  , { lane := .monsterMoonshine
    , structureKey := "character-determines-simple"
    , agdaOwner := "DASHI.Moonshine.Monster3BFiniteStoneVonNeumannWitnessFrontierCorrectionExact"
    , leanCarrier := "Synthesis.MonsterCharacterDetermination"
    , leanAdapter := ""
    , leanConsumer := "Synthesis.MonsterCharacterMultiplicityRegression"
    , hypotheses := ["algebraically closed field", "finite group with invertible order",
                     "simple finite-dimensional representations"]
    , status := .conditionalCompiler "Synthesis.nonempty_iso_of_character_eq"
        ["IsAlgClosed k", "Invertible (card G : k)", "Simple V", "Simple W"]
    , provenance := [lean "Synthesis.MonsterCharacterDetermination"]
    , supersedes := ""
    , payments := ["no Monster-specific same-object identification is made"] }
  -- Cuisine / culture ---------------------------------------------------------
  , { lane := .cuisine
    , structureKey := "declared-carrier-exhaustiveness"
    , agdaOwner := "DASHI.Culture.Cuisine.CuisineKnowledgeSourceAtlas"
    , leanCarrier := "Integration.DeclaredCarrier"
    , leanAdapter := "Cuisine.SourceAtlas"
    , leanConsumer := "Cuisine.SourceAtlas.sourceCount_eq_22"
    , hypotheses := ["the enumeration is exhaustive of the declared carrier"]
    , status := .provedTheorem "Cuisine.SourceAtlas.sourceIds_nodup"
    , provenance := [agda "DASHI.Culture.Cuisine.CuisineKnowledgeSourceAtlas"]
    , supersedes := ""
    , payments := [] }
  , { lane := .cuisine
    , structureKey := "publication-fail-closed"
    , agdaOwner := "DASHI.Culture.Cuisine.ControlledSuccessCore"
    , leanCarrier := "Cuisine.Publication"
    , leanAdapter := ""
    , leanConsumer := "Cuisine.Publication.TightAssessment.abstains_of_any_component_high"
    , hypotheses := ["the join law on overallRisk"]
    , status := .provedTheorem "Cuisine.Publication.publish_iff_low"
    , provenance := [agda "DASHI.Culture.Cuisine.ControlledSuccessCore"]
    , supersedes := "the LooseAssessment record, whose overallRisk field is unconstrained"
    , payments := [] }
  , { lane := .cuisine
    , structureKey := "channel-dependent-provenance"
    , agdaOwner := "DASHI.Culture.Cuisine.ProvenanceRoutingBridge"
    , leanCarrier := "Cuisine.Provenance"
    , leanAdapter := ""
    , leanConsumer := "Cuisine.Provenance.no_source_determined_channel"
    , hypotheses := []
    , status := .noGo "Cuisine.Provenance.no_source_determined_channel"
    , provenance := [agda "DASHI.Culture.Cuisine.ProvenanceRoutingBridge"]
    , supersedes := ""
    , payments := [] }
  -- Chemistry / cognition / language ------------------------------------------
  , { lane := .chemistry
    , structureKey := "reachability-closure"
    , agdaOwner := "DASHI.Chemistry (reachability flag owners)"
    , leanCarrier := "Integration.ReachabilityBarrier"
    , leanAdapter := "Welds.ReachabilityCarrier.ofStep"
    , leanConsumer := "Integration.ChemistryReachability.reachB"
    , hypotheses := ["finite vertex type", "Bool-valued step relation"]
    , status := .provedTheorem "Welds.ReachabilityCarrier.reachable_ofStep_iff_reflTransGen"
    , provenance := [lean "Welds.ReachabilityCarrierWeld"]
    , supersedes := "the lane-local `Relation.ReflTransGen (stepRel step)` encoding"
    , payments := [] }
  , { lane := .cognition
    , structureKey := "language-indexed-reachability"
    , agdaOwner := "DASHI.Cognition (action-language owners)"
    , leanCarrier := "Integration.ReachabilityBarrier"
    , leanAdapter := "Integration.LanguageReachability.restrict"
    , leanConsumer := "Integration.LanguageReachability.barrier_report"
    , hypotheses := ["a declared action language"]
    , status := .provedTheorem "Integration.LanguageReachability.reachableIn_mono"
    , provenance := [lean "Integration.LanguageReachability"]
    , supersedes := ""
    , payments := [] }
  -- Provenance meta -----------------------------------------------------------
  , { lane := .provenanceMeta
    , structureKey := "identifier-authority-firewall"
    , agdaOwner := "DASHI.Interop.CrossLaneProofArchaeologyLedgerExact (IbrahimPolicy)"
    , leanCarrier := "Integration.ProvenanceIdentifier"
    , leanAdapter := "Integration.Lineage.ledger"
    , leanConsumer := "Integration.Lineage.ledger_status_not_a_function_of_provenance"
    , hypotheses := []
    , status := .provedTheorem "Integration.ProvenanceId.provenance_does_not_determine_status"
    , provenance := [agda "DASHI.Interop.CrossLaneProofArchaeologyLedgerExact"]
    , supersedes := "the Bool pins sourceIdentityCoordinateOnly / qidCoordinateOnly / deweyCoordinateOnly"
    , payments := [] }
  , { lane := .provenanceMeta
    , structureKey := "attributed-source-non-promotion"
    , agdaOwner := "DASHI.Core.AttributedSourceCore"
    , leanCarrier := "Integration.ProvenanceIdentifier"
    , leanAdapter := "Cuisine.SourceAtlas"
    , leanConsumer := "Cuisine.SourceAtlas.citationCreatesAuthority_eq_false"
    , hypotheses := []
    , status := .provedTheorem "Integration.ProvenanceId.receipt_without_provenance"
    , provenance := [agda "DASHI.Core.AttributedSourceCore"]
    , supersedes := ""
    , payments := [] } ]

/-! ## 3.  Policy theorems -/

/-- **No parallel definitions.**  Two rows about the same structure name the
same canonical Lean carrier. -/
theorem canonical_ownership :
    ∀ r ∈ ledger, ∀ s ∈ ledger, r.structureKey = s.structureKey →
      r.leanCarrier = s.leanCarrier := by decide

/-- Every row that asserts Lean content names a Lean declaration. -/
theorem proved_rows_name_a_receipt :
    ∀ r ∈ ledger, carriesLeanReceipt r.status = true → (leanName? r.status).isSome = true := by
  intro r _ h
  rw [leanName?_isSome_iff]
  exact h

/-- Every receipted row names an actual consumer: a carrier is never filed as
closed without something that uses it. -/
theorem receipted_rows_have_a_consumer :
    ∀ r ∈ ledger, carriesLeanReceipt r.status = true → r.leanConsumer ≠ "" := by decide

/-- Every receipted row names a carrier. -/
theorem receipted_rows_have_a_carrier :
    ∀ r ∈ ledger, carriesLeanReceipt r.status = true → r.leanCarrier ≠ "" := by decide

/-- Is this status one of the unpaid classes? -/
def isPayment : ProofStatus → Bool
  | .openPayment _ => true
  | .falsePinned _ => true
  | .conjectural _ => true
  | _ => false

/-- Is this status a false-pinned in-corpus ledger flag? -/
def isFalsePin : ProofStatus → Bool
  | .falsePinned _ => true
  | _ => false

/-- Open payments, false pins and conjectures carry no Lean receipt. -/
theorem payments_have_no_receipt :
    ∀ r ∈ ledger, isPayment r.status = true → carriesLeanReceipt r.status = false := by decide

/-- Every false-pinned row records at least one unresolved payment, so a pin is
never bare. -/
theorem false_pins_record_payments :
    ∀ r ∈ ledger, isFalsePin r.status = true → r.payments ≠ [] := by decide

/-- Re-attributing a row to different sources leaves its status untouched. -/
@[simp] theorem row_status_invariant_under_reprovenance (r : Row) (p : List Ident) :
    ({ r with provenance := p } : Row).status = r.status := rfl

/-- Two rows differing only in their status column, used to state the firewall. -/
private def provedSpecimen : Row :=
  Row.mk Lane.provenanceMeta "k" "" "C" "" "C" [] (ProofStatus.provedTheorem "T") [] "" []

private def openSpecimen : Row :=
  Row.mk Lane.provenanceMeta "k" "" "C" "" "C" [] (ProofStatus.openPayment "T") [] "" []

/-- **The firewall, at the ledger's own row type.**  There is no function
computing the status column from the provenance column: the two specimens above
share their provenance and differ in status. -/
theorem ledger_status_not_a_function_of_provenance :
    ¬ ∃ f : List Ident → ProofStatus, ∀ r : Row, r.status = f r.provenance := by
  rintro ⟨f, hf⟩
  have h₁ := hf provedSpecimen
  have h₂ := hf openSpecimen
  rw [show provedSpecimen.provenance = openSpecimen.provenance from rfl] at h₁
  exact absurd (h₁.trans h₂.symm) (by decide)

/-! ## 4.  Queries -/

/-- The rows of one lane. -/
def rowsOfLane (l : Lane) : List Row := ledger.filter (fun r => r.lane = l)

/-- The consumers currently attached to a carrier. -/
def consumersOf (carrier : String) : List String :=
  (ledger.filter (fun r => r.leanCarrier = carrier)).map (·.leanConsumer)

/-- Every unresolved payment in the ledger, with its lane key. -/
def openPayments : List (String × List String) :=
  (ledger.filter (fun r => !r.payments.isEmpty)).map (fun r => (r.structureKey, r.payments))

end Integration.Lineage
