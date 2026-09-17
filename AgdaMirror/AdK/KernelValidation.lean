import AgdaMirror.AdK.NonFactorability

/-!
# AdK exact-CV kernel validation

This validation root was committed before the production theorem spine.  It
requires the terminal constructive non-factorability theorem and serves as the
narrow Lean elaboration/axiom-audit entry point.

Attribution remains upstream:
- Li-Liu-Ji 2015 owns the source-facing CV selection/domain roles.
- Prohaska et al. owns the adopted rounded atomic-mass convention.
- DASHI owns the exact rational reconstruction and the bridge theorems.

`#print axioms` is intentionally retained so any future local/CI elaboration
receipt exposes the terminal theorem's actual kernel dependency surface in the
log rather than relying only on a source grep.
-/

namespace AgdaMirror.AdK.KernelValidation

open AgdaMirror.AdK.NonFactorability

#check adkThreeCVInputCollision
#check adkThreeCVInput_not_factors_through
#check collision_not_factors_through

#print axioms adkThreeCVInput_not_factors_through

end AgdaMirror.AdK.KernelValidation
