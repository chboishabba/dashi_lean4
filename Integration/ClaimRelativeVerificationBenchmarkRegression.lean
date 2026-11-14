import Integration.ClaimRelativeVerificationBenchmark

namespace Integration.ClaimRelativeVerificationBenchmarkRegression

open Integration.ClaimRelativeVerificationBenchmark

example : canonicalBoundary.formalVerificationCreatesTranslationAdequacy = false := rfl
example : canonicalBoundary.weakVerificationCreatesDecisionAuthority = false := rfl
example : canonicalBoundary.validatorSuccessCreatesConsumerSuccess = false := rfl
example : canonicalBoundary.postHocAbstentionCountsAsSuccessfulAbstention = false := rfl
example : canonicalBoundary.abstentionEvaluationUsesPairedActAbstainCases = true := rfl
example : canonicalBoundary.agdaHumanReviewReceiptImportedIntoLean = false := rfl

def pair : PairedActionAbstentionCase Unit Bool :=
  { environment := ()
    shouldActTask := true
    shouldAbstainTask := false
    controlledPerturbationReference := "single controlled perturbation"
    criticalActionReference := "critical action"
    pairReference := "fixture pair" }


def result : PairedActionAbstentionResult pair :=
  { shouldActObserved := .acted
    shouldAbstainObserved := .abstainedBeforeCriticalAction
    traceReference := "fixture trace"
    outcomeReference := "fixture outcome" }

example : PairedCorrect result := ⟨rfl, rfl⟩

end Integration.ClaimRelativeVerificationBenchmarkRegression
