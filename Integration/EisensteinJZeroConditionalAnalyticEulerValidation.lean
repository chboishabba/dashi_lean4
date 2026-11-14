import Integration.EisensteinJZeroConditionalAnalyticEulerExact

namespace Integration.EisensteinJZeroConditionalAnalyticEulerValidation

open Integration.EisensteinJZeroFiniteEulerProductExact
open Integration.EisensteinJZeroConditionalAnalyticEulerExact

example (p : RationalPrime) (s : ℂ) :
    ellipticComplexLocalDenominator p s = heckeComplexLocalDenominator p s :=
  elliptic_hecke_complexLocal_agreement p s

example (p : RationalPrime) (s : ℂ) :
    ellipticEulerTerm p s = heckeEulerTerm p s :=
  elliptic_hecke_EulerTerm_agreement p s

example (s : ℂ)
    (h : Multipliable (fun p : RationalPrime => ellipticEulerTerm p s)) :
    (∏' p : RationalPrime, ellipticEulerTerm p s) =
      ∏' p : RationalPrime, heckeEulerTerm p s :=
  conditionalAnalyticEulerProduct_agreement s h

end Integration.EisensteinJZeroConditionalAnalyticEulerValidation
