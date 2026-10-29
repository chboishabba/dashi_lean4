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

end AgdaMirror.SemanticThreadRejuvenation
