import Integration.OpenAIMath.Everything

namespace Integration.OpenAIMath.OpenAIMathCorpusRegression

open Integration.OpenAIMath

example : upstreamCommit = "1581d4cbdd69a0faf34b2089614fe2a814316a6a" := rfl
example : upstreamLeanToolchain = "leanprover/lean4:v4.34.1" := rfl
example : upstreamRepository = "https://github.com/openai/math" := rfl
example : upstreamLicense = "Apache-2.0" := rfl
example : upstreamFormalizationCatalogue = "lean/formalization.yaml" := rfl

example : manuscriptClaimIsLeanTheorem = false := rfl
example : catalogueEntryIsKernelReceipt = false := rfl
example : upstreamLeanTheoremIsDASHIPort = false := rfl
example : upstreamLeanTheoremIsAgdaTheorem = false := rfl
example : topicalRelevanceIsSameObjectTransport = false := rfl

example : RelevanceClass.directFrontier ≠ RelevanceClass.backgroundOnly := by decide
example : PromotionStatus.upstreamDeclared ≠ PromotionStatus.dashiPorted := by decide
example : PromotionStatus.upstreamKernelChecked ≠ PromotionStatus.dashiKernelChecked := by decide

example : (priorityFor DASHIProgramme.riemannHypothesis).relevance = RelevanceClass.directFrontier := rfl
example : (priorityFor DASHIProgramme.ellipticCM).relevance = RelevanceClass.directFrontier := rfl
example : (priorityFor DASHIProgramme.exceptionalRepresentation).relevance = RelevanceClass.lemmaDonor := rfl

end Integration.OpenAIMath.OpenAIMathCorpusRegression
