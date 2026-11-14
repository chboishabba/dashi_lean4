import Integration.OpenAIMath.UpstreamPin

namespace Integration.OpenAIMath

/-- Authority level of an upstream OpenAI mathematics artefact. -/
inductive UpstreamAuthorityLevel where
  | manuscript
  | catalogueEntry
  | leanDeclaration
  | upstreamKernelReceipt
  deriving DecidableEq, Repr

/-- Promotion state of a result as it crosses the OpenAI -> DASHI Lean -> Agda boundary. -/
inductive PromotionStatus where
  | manuscriptOnly
  | catalogueIndexed
  | upstreamDeclared
  | upstreamKernelChecked
  | dashiPorted
  | dashiKernelChecked
  | agdaImportedFormalSource
  | agdaTheorem
  deriving DecidableEq, Repr

/-- A source receipt names exactly which upstream layer has actually been observed. -/
structure UpstreamFormalizationReceipt where
  familyId : String
  manuscriptId : String
  declaration : String
  authority : UpstreamAuthorityLevel
  upstreamSha : String := upstreamCommit
  deriving Repr

/-- A DASHI promotion receipt is deliberately separate from the upstream receipt. -/
structure DASHIPromotionReceipt where
  upstream : UpstreamFormalizationReceipt
  localDeclaration : String
  status : PromotionStatus
  sameObjectTransportDeclared : Bool
  deriving Repr

/-- Catalogue metadata alone never constructs a DASHI port. -/
def catalogueAutomaticallyPromotes : Bool := false

/-- An upstream kernel receipt alone never constructs an Agda theorem. -/
def upstreamKernelAutomaticallyPromotesToAgda : Bool := false

/-- A topical/relevance edge alone never constructs same-object transport. -/
def relevanceAutomaticallyPromotes : Bool := false

end Integration.OpenAIMath
