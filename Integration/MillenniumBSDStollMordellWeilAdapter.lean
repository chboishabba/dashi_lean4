import EllipticCurves.MordellWeil
import Synthesis.MillenniumBSDCMFGAbelianRankZeroFromModTwoExact
import Synthesis.MillenniumBSDActualRationalPointGroup
import Mathlib.GroupTheory.Finiteness

/-!
# K3 optional: actual Mordell–Weil finite-generation producer from Stoll

THIS MODULE IS OPT-IN AND IS NOT IMPORTED BY Synthesis.lean.

Donor: Michael Stoll, EllipticCurves/MordellWeil.lean
  WeierstrassCurve.Affine.fg_point_of_numberField :
    IsAddFG W.Point
for any elliptic Weierstrass model over a number field.

Pinned upstream source:
  MichaelStollBayreuth/EllipticCurves
  bad38e242a187dea006fc302a0ef0fd53eedd4ba
  Lean 4.35.0; Mathlib v4.35.0; Apache-2.0

Original selected model:
  Synthesis.Millennium.BSD.cmWeierstrass.toAffine.Point
is related to the ACTUAL repository RationalProjectivePoint through
the previously proved group equivalence
  rationalProjectivePointAddEquivMathlib.

The proof below consumes the DONOR's actual finite generation, not
a new assumed [AddGroup.FG] instance. It then discharges the explicit
remaining hypothesis of cmSelectedOriginalMordellWeil_ZRank_zero.

K0 VERSION FIREWALL:
  Project Lean 4.35.0-rc3 + mathlib v4.28.0 DOES NOT have the
  donor dependency. This module cannot be part of the default build
  before an isolated Lean/mathlib 4.35.0 local proof-replay with
  the donor as a pinned Lake dependency. Do not promote this module
  to local kernel accepted or claim K3 is closed from a source file.
-/

namespace Synthesis.Millennium.BSD

/-- Literal original rational-point carrier is finitely generated,
transported from Stoll's actual number-field Mordell–Weil theorem. -/
theorem cmRationalProjectivePoint_isAddFG_fromStoll :
    IsAddFG RationalProjectivePoint := by
  classical
  have hMW : IsAddFG cmWeierstrass.toAffine.Point :=
    WeierstrassCurve.Affine.fg_point_of_numberField
      (W := cmWeierstrass.toAffine)
  exact (isAddFG_congr rationalProjectivePointAddEquivMathlib).mpr hMW

/-- Reuse the full original descent's rank-zero theorem with the
actual external theorem, not an invented rank/dimension receipt. -/
theorem cmOriginalMordellWeil_rank_zero_fromStoll :
    Module.rank ℤ RationalProjectivePoint = 0 := by
  classical
  letI : AddGroup.FG RationalProjectivePoint :=
    cmRationalProjectivePoint_isAddFG_fromStoll
  exact cmSelectedOriginalMordellWeil_ZRank_zero

end Synthesis.Millennium.BSD
