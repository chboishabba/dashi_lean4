import BSDStoll.ActualArithmeticSelmerDefect
import BSDStoll.ActualAllPlaceSelmer

/-!
# Same-object weld: literal DASHI rational elliptic curve → real arithmetic

The local response, Selmer kernel, global rational-point Kummer image and
its canonical arithmetic defect ALL use the SAME curve E.1.toAffine,
the same base field ℚ, ℤ finite places and InfinitePlace ℚ completions.

The only extra restriction is Stoll's normal-form condition
E.1.toAffine.IsCharNeTwoNF. No freely selected Selmer/Residual group occurs.

All-curve transport from arbitrary Weierstrass coefficients to this
normal form, cohomological Sha[2], and BSD analytic rank remain open.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

noncomputable section

/-- Complete arithmetic response at the SAME literal rational curve. -/
noncomputable def actualClayNormalFormCompleteResponse
    (E : RationalEllipticCurve)
    [E.1.toAffine.IsCharNeTwoNF] :
    E.1.toAffine.M →*
      BSDStoll.CompleteArithmeticResponseGroup
        E.1.toAffine ℤ
        (fun v : InfinitePlace ℚ => v.Completion) := by
  letI : E.1.IsElliptic := E.2
  exact BSDStoll.completeArithmeticResponse
    E.1.toAffine ℤ
    (fun v : InfinitePlace ℚ => v.Completion)

/-- Complete arithmetic response kernel = independently defined genuine
all-place 2-Selmer subgroup on the exact same DASHI rational curve. -/
theorem actualClayNormalFormResponseKernel_isSelmer
    (E : RationalEllipticCurve)
    [E.1.toAffine.IsCharNeTwoNF] :
    (actualClayNormalFormCompleteResponse E).ker =
      actualNormalFormTwoSelmer E := by
  letI : E.1.IsElliptic := E.2
  exact BSDStoll.completeArithmeticResponse_ker_eq_selmer
    E.1.toAffine ℤ
    (fun v : InfinitePlace ℚ => v.Completion)

/-- Canonical arithmetic residual, not the freely chosen residual of the
old exact-sequence carrier. Its quotient source is actualNormalFormTwoSelmer. -/
abbrev actualClayNormalFormSelmerDefect
    (E : RationalEllipticCurve)
    [E.1.toAffine.IsCharNeTwoNF] : Type _ :=
  BSDStoll.ActualTwoSelmerDefect
    E.1.toAffine ℤ
    (fun v : InfinitePlace ℚ => v.Completion)

/-- Every same-curve globally rational point has trivial arithmetic
Selmer defect, by real Kummer image inclusion into the selected Selmer. -/
theorem actualClayNormalFormKummerDefect_zero
    (E : RationalEllipticCurve)
    [E.1.toAffine.IsCharNeTwoNF]
    (P : Multiplicative E.1.toAffine.Point) :
    BSDStoll.actualSelmerResidualMap
      E.1.toAffine ℤ
      (fun v : InfinitePlace ℚ => v.Completion)
      (BSDStoll.globalKummerIntoActualSelmer
        E.1.toAffine ℤ
        (fun v : InfinitePlace ℚ => v.Completion) P) = 1 := by
  letI : E.1.IsElliptic := E.2
  exact BSDStoll.globalKummer_has_zero_arithmetic_defect
    E.1.toAffine ℤ
    (fun v : InfinitePlace ℚ => v.Completion) P

end

end Synthesis.Millennium.BSD
