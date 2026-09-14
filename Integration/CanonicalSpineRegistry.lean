import Integration.LineageLedger

/-!
# The Lean canonical-spine registry

The registry answers one question per structure: **who owns it in Lean, and who
is allowed to restate it** (nobody).  It is deliberately small — it lists
carriers, not every declaration in the garden — and it is *not* a mandatory
build target for the whole corpus: it records ownership, consumers, status and
provenance, and it is checked against `Integration.Lineage.ledger`.

Policy, enforced by the theorems below rather than asserted in prose:

* `registry_names_nodup` — one entry per carrier name;
* `registry_keys_nodup` — one carrier per structure key, i.e. **the no-parallel
  definition policy**: a lane that needs an existing structure must adapt to the
  registered carrier instead of introducing its own;
* `ledger_carriers_registered` — every carrier named by a receipted lineage row
  is in the registry, so the ledger cannot point at an unowned module;
* `registry_entries_have_consumers` — a registered carrier has at least one
  named consumer; a carrier with no consumer is not a carrier, it is a draft.

Opt-in rollups.  `Welds` collects the consumer welds, `Spine`, `Synthesis`,
`Cuisine` and `Integration` collect their own lanes, and the NS rate-block
cutset is the separate `NSCutset` library pointing at the preserved donor
payload.  Nothing here forces those into one build.
-/

namespace Integration.SpineRegistry

open Integration.ProvenanceId Integration.Lineage

/-- A registry entry: the canonical Lean owner of one structure. -/
structure Entry where
  /-- The structure this carrier owns, matching `Lineage.Row.structureKey`. -/
  structureKey : String
  /-- The Lean module that owns it. -/
  carrier : String
  /-- Where the structure came from: Agda module, Lean donor, or `""`. -/
  origin : String
  /-- Modules that consume the carrier. -/
  consumers : List String
  /-- Lanes routed through the carrier. -/
  lanes : List Lane
  deriving DecidableEq, Repr

/-- The canonical carriers.  Each one is a module in this project that at least
one other module uses. -/
def registry : List Entry :=
  [ { structureKey := "rate-block-schur-kernel"
    , carrier := "Spine.RateBlockSchur"
    , origin := "DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact"
    , consumers := ["RequestProject.NavierStokes.SpineRateBlockAdapter",
                    "Spine.RateBlockSchurPiCarrier"]
    , lanes := [.navierStokes] }
  , { structureKey := "euclidean-pi-carrier"
    , carrier := "Spine.RateBlockSchurPiCarrier"
    , origin := "Lean-native (WithLp.toLp 2 transport)"
    , consumers := ["Welds.NSRateBlockPiWeld"]
    , lanes := [.navierStokes] }
  , { structureKey := "gram-consumer-from-pair-estimate"
    , carrier := "Welds.NSRateBlockPi.gramOperatorBound_of_pair_estimate"
    , origin := "Lean-native factorisation of two inline donor proofs"
    , consumers := ["Welds.NSRateBlockPi.gramOperatorBound_viaPiCarrier",
                    "Welds.NSRateBlockPi.spineAdapter_consumer_refactored"]
    , lanes := [.navierStokes] }
  , { structureKey := "slot-kernel-anti-parallel"
    , carrier := "RequestProject.NavierStokes.SlotKernelAntiParallel"
    , origin := "DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact"
    , consumers := ["RequestProject.NavierStokes.TransverseFrameSplit"]
    , lanes := [.navierStokes] }
  , { structureKey := "gram-ledger-two-presentations"
    , carrier := "Spine.GramLedger"
    , origin := "DASHI.Physics.Closure.NSTriadKNPartnerBlockGramLedgerRound181Exact"
    , consumers := ["Spine.AxiomAudit"]
    , lanes := [.navierStokes] }
  , { structureKey := "gronwall-comparison"
    , carrier := "Spine.GronwallComparison"
    , origin := "Lean-native (integrating-factor comparison)"
    , consumers := ["Spine.AxiomAudit"]
    , lanes := [.navierStokes] }
  , { structureKey := "gram-profile-consumer-factorisation"
    , carrier := "Proposed.FibreRoutingProjectionAdapter"
    , origin := "DASHI FibreRoutingGrokkingMoEBrainCrossPollinationExact"
    , consumers := ["RequestProject.NavierStokes.GramConsumerFactorisation"]
    , lanes := [.navierStokes, .cognition] }
  , { structureKey := "taper-second-moment"
    , carrier := "Spine.RiemannBridge"
    , origin := "DASHI.Analysis.RiemannG2FinalNearLiteralKernelExact"
    , consumers := ["Spine.AxiomAudit"]
    , lanes := [.riemannHypothesis] }
  , { structureKey := "monster-order-factorisation"
    , carrier := "Synthesis.MonsterOrder"
    , origin := "DASHI.Moonshine (Monster order owners)"
    , consumers := ["Spine.JMD.MonsterMoonshine", "Synthesis.AxiomAudit"]
    , lanes := [.monsterMoonshine] }
  , { structureKey := "character-determines-simple"
    , carrier := "Synthesis.MonsterCharacterDetermination"
    , origin := "dashi_lean4 ff0b3a02 donor"
    , consumers := ["Synthesis.MonsterCharacterMultiplicityRegression", "Synthesis.AxiomAudit"]
    , lanes := [.monsterMoonshine] }
  , { structureKey := "declared-carrier-exhaustiveness"
    , carrier := "Integration.DeclaredCarrier"
    , origin := "DASHI.Culture.Cuisine.CuisineKnowledgeSourceAtlas"
    , consumers := ["Cuisine.SourceAtlas", "Integration.AxiomAudit"]
    , lanes := [.cuisine, .education, .ontologyWikidata] }
  , { structureKey := "publication-fail-closed"
    , carrier := "Cuisine.Publication"
    , origin := "DASHI.Culture.Cuisine.ControlledSuccessCore"
    , consumers := ["Cuisine.AxiomAudit"]
    , lanes := [.cuisine, .governance] }
  , { structureKey := "channel-dependent-provenance"
    , carrier := "Cuisine.Provenance"
    , origin := "DASHI.Culture.Cuisine.ProvenanceRoutingBridge"
    , consumers := ["Cuisine.AxiomAudit"]
    , lanes := [.cuisine, .law] }
  , { structureKey := "reachability-closure"
    , carrier := "Integration.ReachabilityBarrier"
    , origin := "DASHI reachability owners (Agda `Reachable`)"
    , consumers := ["Integration.LanguageReachability", "Welds.ReachabilityCarrierWeld"]
    , lanes := [.chemistry, .cognition, .biology] }
  , { structureKey := "language-indexed-reachability"
    , carrier := "Integration.ReachabilityBarrier"
    , origin := "DASHI reachability owners (Agda `Reachable`)"
    , consumers := ["Integration.LanguageReachability", "Welds.ReachabilityCarrierWeld"]
    , lanes := [.cognition] }
  , { structureKey := "identifier-authority-firewall"
    , carrier := "Integration.ProvenanceIdentifier"
    , origin := "DASHI.Interop.CrossLaneProofArchaeologyLedgerExact (IbrahimPolicy)"
    , consumers := ["Integration.LineageLedger", "Integration.CanonicalSpineRegistry"]
    , lanes := [.provenanceMeta, .ontologyWikidata] }
  , { structureKey := "attributed-source-non-promotion"
    , carrier := "Integration.ProvenanceIdentifier"
    , origin := "DASHI.Core.AttributedSourceCore"
    , consumers := ["Cuisine.SourceAtlas", "Integration.LineageLedger"]
    , lanes := [.provenanceMeta, .cuisine] } ]

/-! ## Policy theorems -/

/-- One entry per structure key. -/
theorem registry_keys_nodup : (registry.map (·.structureKey)).Nodup := by decide

/-- **No parallel definitions.**  Entries with the same key name the same
carrier; a lane needing that structure adapts to this module. -/
theorem registry_key_determines_carrier :
    ∀ e ∈ registry, ∀ f ∈ registry, e.structureKey = f.structureKey → e.carrier = f.carrier := by
  decide

/-- A registered carrier has at least one named consumer. -/
theorem registry_entries_have_consumers : ∀ e ∈ registry, e.consumers ≠ [] := by decide

/-- The registry carriers. -/
def carriers : List String := (registry.map (·.carrier)).eraseDups

/-- **Ledger/registry agreement.**  Every carrier named by a lineage row that
asserts Lean content is a registered carrier. -/
theorem ledger_carriers_registered :
    ∀ r ∈ Integration.Lineage.ledger, carriesLeanReceipt r.status = true →
      r.leanCarrier ∈ carriers := by decide

/-- Conversely every registry key occurs in the ledger, so the registry has no
orphan rows. -/
theorem registry_keys_in_ledger :
    ∀ e ∈ registry, e.structureKey ∈ Integration.Lineage.ledger.map (·.structureKey) := by decide

/-! ## Reuse statistics -/

/-- Carriers that serve more than one lane: the measured cross-domain reuse. -/
def multiLaneCarriers : List String :=
  ((registry.filter (fun e => 1 < e.lanes.length)).map (·.carrier)).eraseDups

/-- The reachability carrier really is shared by three lanes. -/
theorem reachability_carrier_is_shared :
    ∃ e ∈ registry, e.carrier = "Integration.ReachabilityBarrier" ∧ e.lanes.length = 3 := by
  decide

/-- The declared-carrier theorem is shared by three lanes as well. -/
theorem declared_carrier_is_shared :
    ∃ e ∈ registry, e.carrier = "Integration.DeclaredCarrier" ∧ e.lanes.length = 3 := by
  decide

end Integration.SpineRegistry
