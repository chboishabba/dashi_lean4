import Integration.EisensteinJZeroPointCMExact

namespace Dashi.EisensteinJZeroPointCMValidation

open Dashi.EisensteinJZeroPointCMExact

example : omega ^ 3 = (1 : EisensteinField) := omega_cube
example : omegaPoint 0 = 0 := omegaPoint_zero
example (P : jZeroCurve.Point) :
    omegaPoint (omegaPoint (omegaPoint P)) = P := omegaPoint_order_three P

-- The final promotion target is deliberately a group endomorphism, not merely
-- a point permutation.  This import is RED until the production owner exists.
#check omegaPointEndomorphism
#check omegaPointEndomorphism_order_three

end Dashi.EisensteinJZeroPointCMValidation
