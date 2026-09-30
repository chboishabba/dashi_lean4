import AgdaMirror.Governance.IRGCOpenLetter2026ArgumentGraph
import AgdaMirror.Governance.IranianRevolutionaryIntellectualGenealogy

namespace AgdaMirror.Governance.IRGCReviewedEventDualChronologyPacket

open AgdaMirror.Governance.IRGCOpenLetter2026.ArgumentGraph
open AgdaMirror.Governance.IranianRevolutionaryIntellectualGenealogy

inductive PacketLayer
  | publicationEventLayer
  | primaryArgumentLayer
  | secondaryReportLayer
  | historicalGenealogyLayer
  deriving DecidableEq, Repr

structure ExactSpanDemand where
  propositionRef : String
  sourceRef : String
  requiredLocator : String
  reviewRef : String
  unresolvedReason : String
  mayPromoteTruth : Bool := false

structure SourceLocalEvent where
  eventRef : String
  layer : PacketLayer
  sourceRef : String
  temporalRef : String
  independentlyEstablishesUnderlyingPoliticalClaim : Bool := false

structure IRGCDualChronologyPacket where
  sourceArgumentTopology : SourceArgumentTopology
  eventTimeEntries : List SourceLocalEvent
  knowledgeTimeRefs : List String
  exactSpanDemands : List ExactSpanDemand
  sourceRolesPaid : Bool := true
  sourceArgumentTopologyPaid : Bool := true
  dualChronologyRepresented : Bool := true
  exactPrimarySpansPaid : Bool := false
  reviewedEventJoinPaid : Bool := false
  historicalMechanismClosed : Bool := false
  worldTruthPromoted : Bool := false

def peopleStateSpanDemand : ExactSpanDemand :=
  ⟨"irgc:argument:people-state-distinction",
   "IRGC 2026 primary English PDF",
   "exact PDF page/span for people-versus-government distinction",
   "review:irgc:people-state",
   "source topology is paid, but exact passage coordinates are not yet attached"⟩

def commonOppressorSpanDemand : ExactSpanDemand :=
  ⟨"irgc:argument:common-oppressor",
   "IRGC 2026 primary English PDF",
   "exact PDF page/span for common-oppressor framing",
   "review:irgc:common-oppressor",
   "argument graph records the move but not an exact reviewed passage"⟩

def agencySpanDemand : ExactSpanDemand :=
  ⟨"irgc:argument:popular-agency",
   "IRGC 2026 primary English PDF",
   "exact PDF page/span for political-agency appeal",
   "review:irgc:popular-agency",
   "primary structure alone cannot substitute for a reviewed source span"⟩

def canonical : IRGCDualChronologyPacket :=
  ⟨canonicalTopology,
   [
     ⟨"event:irgc-letter:publication", .publicationEventLayer,
      "IRGCOpenLetter2026SourceAtlasExact.irgcPrimaryLetter", "2026-09-29"⟩,
     ⟨"event:knowledge:reuters-irgc-letter", .secondaryReportLayer,
      "IRGCOpenLetter2026SourceAtlasExact.reutersReport", "2026-09-30"⟩
   ],
   ["knowledge:matin-asgari:2018", "knowledge:boroujerdi:2000"],
   [peopleStateSpanDemand, commonOppressorSpanDemand, agencySpanDemand]⟩

theorem packet_is_review_fail_closed :
    canonical.sourceRolesPaid = true ∧
    canonical.sourceArgumentTopologyPaid = true ∧
    canonical.dualChronologyRepresented = true ∧
    canonical.exactPrimarySpansPaid = false ∧
    canonical.reviewedEventJoinPaid = false ∧
    canonical.historicalMechanismClosed = false ∧
    canonical.worldTruthPromoted = false := by
  decide

def fieldContinuityEdges : List GenealogyEdge := [
  marxianFieldToShariati,
  thirdWorldismToShariati,
  shariatiToRevolutionaryGeneration,
  iranianLeftToKhomeiniWestGrammar
]

end AgdaMirror.Governance.IRGCReviewedEventDualChronologyPacket
