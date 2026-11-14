import Dashi.Biology.SourceCueTruthNoncollapseExact

namespace Dashi.Biology.SourceCueTruthNoncollapseRegression

open Dashi.Biology.SourceCueTruthNoncollapseExact

example : canonicalSourceCueReliabilityReceipt.healthProfessionalCueRaisedPerceivedReliability = true := rfl
example : canonicalSourceCueReliabilityReceipt.effectLargelyExplainedByPerceivedSourceCredibility = true := rfl
example : canonicalSourceCueReliabilityReceipt.highEngagementRaisedMisleadingPostReliability = false := rfl
example : canonicalSourceCueTruthBoundary.sourceCueChangesClaimAccuracy = false := rfl
example : canonicalSourceCueTruthBoundary.perceivedReliabilityCreatesTruthAuthority = false := rfl
#check sourceCredibilityDoesNotDetermineTruth

end Dashi.Biology.SourceCueTruthNoncollapseRegression
