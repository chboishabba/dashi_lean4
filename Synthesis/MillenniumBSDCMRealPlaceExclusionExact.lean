import Synthesis.MillenniumBSDExplicitSelmerSubgroup
import Synthesis.MillenniumBSDCMClaySelmerAllPlaceWitnessExact
import Mathlib.Tactic

/-!
# Concrete real-place obstruction in the CM two-Selmer donor

The worked curve is E : y² = x(x - 1)(x + 1). Its real local Kummer image
allows sign pairs with equal coordinates. Consequently the global square-class
pair ([-1], [1]) is NOT in the actual all-place Selmer group.

This is a literal arithmetic exclusion on the independently defined
Selmer subset, not a consequence of the purely group-theoretic
UniversalTwoDescentResidualOn exact-sequence interface.
-/

namespace Synthesis.Millennium.BSD

/-- A genuine global pair of rational square classes with opposite signs. -/
def mixedSignGlobalClass : RatSquareClass × RatSquareClass :=
  (squareClassOf negOneNZ, squareClassOf oneNZ)

/-- Both signs are calculated on actual rational square-class representatives. -/
theorem mixedSignGlobalClass_realLocalization :
    realKummerLocalization mixedSignGlobalClass = (true, false) := by
  simp [mixedSignGlobalClass, realKummerLocalization,
    squareClassSignBit_mk, signBit_neg_one, signBit_one]

/-- The pair fails the true real-place Kummer condition. -/
theorem mixedSignGlobalClass_not_realKummerImage :
    realKummerLocalization mixedSignGlobalClass ∉ RealKummerImage := by
  rw [mixedSignGlobalClass_realLocalization]
  change ¬ (true = false)
  decide

/-- Therefore the concrete all-place two-Selmer intersection rejects it. -/
theorem mixedSignGlobalClass_not_selmer :
    mixedSignGlobalClass ∉ ExplicitTwoSelmerIntersection := by
  intro h
  exact mixedSignGlobalClass_not_realKummerImage h.1

/-- The actual CM subgroup also excludes the mixed-sign class. -/
theorem mixedSignGlobalClass_not_selmerSubgroup :
    mixedSignGlobalClass ∉ explicitTwoSelmerSubgroup := by
  intro h
  exact mixedSignGlobalClass_not_realKummerImage h.1

/-!
This example demonstrates an actual local arithmetic restriction on the
worked CM Selmer carrier. It does not construct Sel_2(E) for general E, nor
does it prove the Sha[2] identification or BSD rank comparison.
-/

end Synthesis.Millennium.BSD
