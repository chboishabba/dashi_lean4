namespace AgdaMirror.Cognition.PNF.SensibLawITIRNarrativeComparisonTransport

inductive LinkKind
  | asserts | attributesTo | supports | undermines | cites
  deriving DecidableEq, Repr

inductive LinkType
  | attributionLink | causalSupport | causalDispute | citationLink | nonCausalAssociation
  deriving DecidableEq, Repr

inductive Confidence
  | high | medium | low | abstain
  deriving DecidableEq, Repr

inductive ArgumentFamily
  | cprsBlocking | woolworthsPrice | governmentCapacity | etsDelayAuthority
  | fallacies | otherArgumentFamily
  deriving DecidableEq, Repr

inductive ClaimModality
  | alleged | denied | corroborated | refuted | unresolved | interpreted
  deriving DecidableEq, Repr

structure SourceSpan where
  sourceId : String
  spanId : String
  textRef : String
  publicReproducible : Bool

structure AttributedProposition where
  propositionId : String
  predicateKey : String
  sourceSpan : SourceSpan
  speaker : String
  attributedAuthority : String
  modality : ClaimModality
  argumentFamily : ArgumentFamily

structure ClaimLink where
  linkId : String
  kind : LinkKind
  fromProposition : String
  toProposition : String
  linkType : LinkType
  confidence : Confidence
  counterHypothesisRef : String
  provenanceReceipt : String
  completeForPublicArtifact : Bool

structure NarrativeLane where
  laneId : String
  propositions : List AttributedProposition
  links : List ClaimLink
  hiddenTruthScore : Bool := false
  canonicalVerdict : Bool := false

inductive ComparisonStatus
  | shared | leftOnly | rightOnly | disputed | unresolved
  deriving DecidableEq, Repr

structure ComparisonRow where
  rowId : String
  status : ComparisonStatus
  leftPropositionRef : String
  rightPropositionRef : String
  reasoningDifference : String
  sourceLocalReceipt : String
  promotesTruth : Bool := false

structure NarrativeComparison where
  left : NarrativeLane
  right : NarrativeLane
  rows : List ComparisonRow
  disagreementPreserved : Bool := true
  abstentionPreserved : Bool := true
  mergedCanonicalStory : Bool := false
  truthScoreProduced : Bool := false

def canonicalLaneBoundary
    (id : String)
    (props : List AttributedProposition)
    (links : List ClaimLink) : NarrativeLane :=
  ⟨id, props, links⟩

def canonicalComparison
    (left right : NarrativeLane)
    (rows : List ComparisonRow) : NarrativeComparison :=
  ⟨left, right, rows⟩

theorem canonical_comparison_is_noncollapsing
    (l r : NarrativeLane) (rows : List ComparisonRow) :
    (canonicalComparison l r rows).disagreementPreserved = true ∧
    (canonicalComparison l r rows).abstentionPreserved = true ∧
    (canonicalComparison l r rows).mergedCanonicalStory = false ∧
    (canonicalComparison l r rows).truthScoreProduced = false := by
  decide

end AgdaMirror.Cognition.PNF.SensibLawITIRNarrativeComparisonTransport
