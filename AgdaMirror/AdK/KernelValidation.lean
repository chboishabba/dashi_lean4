import AgdaMirror.AdK.NonFactorability

/-!
# AdK exact-CV kernel validation

This validation root is intentionally committed before the production theorem
spine.  It requires the terminal constructive non-factorability theorem and
serves as the narrow Lean elaboration/axiom-audit entry point.

The next commit after the workflow exists is intentionally validation-only so
GitHub Actions can record a genuine compiler RED against the absent production
module before implementation begins.

Attribution remains upstream:
- Li-Liu-Ji 2015 owns the source-facing CV selection/domain roles.
- Prohaska et al. owns the adopted rounded atomic-mass convention.
- DASHI owns the exact rational reconstruction and the bridge theorems.
-/

namespace AgdaMirror.AdK.KernelValidation

open AgdaMirror.AdK.NonFactorability

#check adkThreeCVInputCollision
#check adkThreeCVInput_not_factors_through
#check collision_not_factors_through

end AgdaMirror.AdK.KernelValidation
