import AgdaMirror.AdK.NonFactorability

/-!
# AdK exact-CV kernel validation

This validation root was committed before the production theorem spine and now
checks the terminal AdK result through the repository-wide canonical
IntersectionalNonFactorability surface.

Attribution remains upstream:
- Li-Liu-Ji 2015 owns the source-facing CV selection/domain roles.
- Prohaska et al. owns the adopted rounded atomic-mass convention.
- Crenshaw 1991 is conceptual motivation for the generic source lane, not owner
  of the DASHI factorisation theorem.
- DASHI owns the exact rational reconstruction and bridge mathematics.

`#print axioms` remains so future elaboration exposes the terminal theorem's
actual kernel dependency surface.
-/

namespace AgdaMirror.AdK.KernelValidation

open AgdaMirror.AdK.NonFactorability

#check adkConfigurationNonFactorabilityWitness
#check adkThreeCVInput_not_factors_through
#check adkThreeCVRecharting_not_factors_through

#print axioms adkThreeCVInput_not_factors_through
#print axioms adkThreeCVRecharting_not_factors_through

end AgdaMirror.AdK.KernelValidation
