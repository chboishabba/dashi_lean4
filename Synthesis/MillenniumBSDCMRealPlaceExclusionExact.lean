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

/-- The all-place CM two-Selmer subgroup is genuinely smaller than the
unrestricted square-class product, as witnessed by the explicit mixed-sign
class. This is arithmetic content absent from a bare exact-sequence shape. -/
theorem explicitTwoSelmerSubgroup_ne_top :
    explicitTwoSelmerSubgroup ≠ ⊤ := by
  intro htop
  have hmember : mixedSignGlobalClass ∈ explicitTwoSelmerSubgroup := by
    rw [htop]
    exact Subgroup.mem_top _
  exact mixedSignGlobalClass_not_selmerSubgroup hmember

/-- The literal Kummer class of ANY rational point on the worked CM
curve avoids the explicitly excluded mixed-sign square-class pair. -/
theorem cmGlobalKummer_ne_mixedSign
    (P : RationalProjectivePoint) :
    totalGlobalKummer P ≠ mixedSignGlobalClass := by
  intro h
  apply mixedSignGlobalClass_not_selmerSubgroup
  rw [← h]
  exact totalGlobalKummer_mem_explicitTwoSelmer P

/-- The actual rational-point Kummer map into the unrestricted global
square-class product is NOT surjective: local conditions obstruct the
displayed point. This does not assert a nontrivial Sha residual. -/
theorem cmGlobalKummer_not_surjective :
    ¬ Function.Surjective totalGlobalKummer := by
  intro h
  obtain ⟨P, hP⟩ := h mixedSignGlobalClass
  exact cmGlobalKummer_ne_mixedSign P hP

/-- The corresponding map on the exact Clay-facing curve has the SAME
excluded global class, because its Kummer hom lands in the actual all-place
Selmer subgroup. -/
theorem cmClayGlobalKummer_ne_mixedSign
    (P : CMClayRationalPoint) :
    ((cmClayGlobalKummerHom (Multiplicative.ofAdd P)).1 :
      RatSquareClass × RatSquareClass) ≠ mixedSignGlobalClass := by
  intro h
  apply mixedSignGlobalClass_not_selmerSubgroup
  rw [← h]
  exact (cmClayGlobalKummerHom (Multiplicative.ofAdd P)).property

/-!
This example demonstrates an actual local arithmetic restriction on the
worked CM Selmer carrier. It does not construct Sel_2(E) for general E, nor
does it prove the Sha[2] identification or BSD rank comparison.
-/

end Synthesis.Millennium.BSD
