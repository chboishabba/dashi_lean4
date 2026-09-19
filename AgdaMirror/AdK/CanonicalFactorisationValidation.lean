import AgdaMirror.IntersectionalNonFactorability
import AgdaMirror.AdK.NonFactorability

/-!
# AdK canonical factorisation-spine validation

This validation requires the AdK theorem to inhabit the repository-wide
IntersectionalNonFactorability surface rather than a lane-local reconstruction.

Attribution boundary:
- Crenshaw 1991 motivates the source Agda lane conceptually.
- The factorisation criterion and witness compiler are DASHI mathematics.
- Li-Liu-Ji / Prohaska remain owners only of their AdK source roles.
-/

namespace AgdaMirror.AdK.CanonicalFactorisationValidation

open AgdaMirror.IntersectionalNonFactorability
open AgdaMirror.AdK.NonFactorability

#check adkConfigurationNonFactorabilityWitness
#check adkThreeCVInput_not_factors_through
#check witnessRulesOutEveryFlatFactorisation

example :
    ¬ FactorsThrough
      (fun configuration =>
        AgdaMirror.AdK.CVProjection.threeCVInputSurface configuration
          .backbone)
      (fun configuration : AgdaMirror.AdK.AtomisticConfiguration.Configuration =>
        configuration) :=
  adkThreeCVInput_not_factors_through

#print axioms adkThreeCVInput_not_factors_through

end AgdaMirror.AdK.CanonicalFactorisationValidation
