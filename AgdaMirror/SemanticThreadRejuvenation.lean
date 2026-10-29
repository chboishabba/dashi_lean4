/-! Secondary mirror of DASHI.Interop.SemanticThreadRejuvenationExact.
Agda is authoritative. This does not prove runtime/database correctness. -/
namespace AgdaMirror.SemanticThreadRejuvenation

structure Thread where
  identifier : String

structure PNF (source : Thread) where
  factorCount : Nat

structure World (source : Thread) (factors : PNF source) where
  registeredCount : Nat

structure WorldRelative (source : Thread) (factors : PNF source)
    (registered : World source factors) where
  capsule : String

inductive Database where
  | postgresql
  deriving DecidableEq

structure CommittedWorld (source : Thread) (factors : PNF source) where
  store : Database
  registered : World source factors

theorem soleStore {t : Thread} {p : PNF t}
    (w : CommittedWorld t p) : w.store = Database.postgresql := by
  cases w.store
  rfl

structure Rejuvenated (source : Thread) (factors : PNF source)
    (registered : World source factors)
    (relativeState : WorldRelative source factors registered) where
  child : Thread
  lineageRecorded : Bool
  lineageRecordedTrue : lineageRecorded = true
  proofPromotionByEnrichment : Bool
  proofPromotionByEnrichmentFalse : proofPromotionByEnrichment = false

theorem lineagePreserved {t : Thread} {p : PNF t} {w : World t p}
    {r : WorldRelative t p w} (result : Rejuvenated t p w r) :
    result.lineageRecorded = true := result.lineageRecordedTrue

theorem enrichmentCannotPromoteProof {t : Thread} {p : PNF t}
    {w : World t p} {r : WorldRelative t p w}
    (result : Rejuvenated t p w r) :
    result.proofPromotionByEnrichment = false :=
  result.proofPromotionByEnrichmentFalse


/- Topic 1 syntax mirror. Agda remains authoritative; this does not verify execution. -/
inductive TopicOperation where
  | collapseProperty (value : String)
  | expandTemporal (value : String)
  deriving DecidableEq

structure TopicOnePlan where
  autoCollapse : TopicOperation
  lastCollapse : TopicOperation
  nowExpansion : TopicOperation

def canonicalTopicOne : TopicOnePlan :=
  ⟨.collapseProperty "auto", .collapseProperty "last", .expandTemporal "now"⟩

theorem topicOneAutoPreserved :
    canonicalTopicOne.autoCollapse = .collapseProperty "auto" := rfl

theorem topicOneLastPreserved :
    canonicalTopicOne.lastCollapse = .collapseProperty "last" := rfl

theorem topicOneNowPreserved :
    canonicalTopicOne.nowExpansion = .expandTemporal "now" := rfl


/- Worker 01 lexical motif mirror; no semantic equivalence is asserted. -/
inductive ComparativeChangeMotif where
  | ratherThan (preferred alternative : String)
  | change (label : String)
  deriving DecidableEq

structure Worker01Motif where
  comparison : ComparativeChangeMotif
  mutation : ComparativeChangeMotif

def canonicalWorker01 : Worker01Motif :=
  ⟨.ratherThan "rather" "than", .change "change"⟩

theorem worker01ComparisonPreserved :
    canonicalWorker01.comparison = .ratherThan "rather" "than" := rfl

theorem worker01ChangePreserved :
    canonicalWorker01.mutation = .change "change" := rfl


/- Worker 06: parsed input is supplied, not proven correct. -/
structure ParsedAutoNode where
  parsedText : String
  expanded : Bool
  deriving DecidableEq

def collapseAuto (node : ParsedAutoNode) : ParsedAutoNode :=
  ⟨node.parsedText, false⟩

theorem collapseAutoPreservesText (node : ParsedAutoNode) :
    (collapseAuto node).parsedText = node.parsedText := rfl

theorem collapseAutoHides (node : ParsedAutoNode) :
    (collapseAuto node).expanded = false := rfl

theorem collapseAutoIdempotent (node : ParsedAutoNode) :
    collapseAuto (collapseAuto node) = collapseAuto node := by
  cases node with
  | mk parsedText expanded =>
    rfl

end AgdaMirror.SemanticThreadRejuvenation
