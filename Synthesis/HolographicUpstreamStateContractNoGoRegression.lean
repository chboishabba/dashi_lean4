import Synthesis.HolographicUpstreamStateContractNoGo

namespace Synthesis.HolographicUpstreamStateContractNoGoRegression

open Synthesis.HolographicUpstreamStateContractNoGo

example :
    upstreamPureDensityDepthOne ≠ upstreamDiagonalContractDepthOne :=
  upstreamStateContractMismatchDepthOne

example : upstreamStateContractSameObjectImpossibleAsWritten = true := rfl
example : upstreamDefinitionsMustChangeForStateContractWeld = true := rfl
example : correctedRTStateStillRequiresExplicitSourceReplacement = true := rfl

end Synthesis.HolographicUpstreamStateContractNoGoRegression
