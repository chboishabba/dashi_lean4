import Synthesis.MillenniumBSDUniversalRankInequalityMechanisms
import Synthesis.MillenniumBSDExplicitSelmerCokernelExact
import Mathlib.Tactic

/-!
# BSD same-curve Selmer defect decomposition

The existing worked case already has the literal short-exact shape

  E(Q)/2E(Q) -> Sel_2(E) -> ExplicitTwoSelmerCokernel.

This file lifts only the STRUCTURAL lesson to the universal Clay-facing rank
interface. On each exact RationalEllipticCurve E we keep

  Selmer rank(E) = MW rank(E) + defect rank(E).

The defect is same-curve data. No identification with Sha(E) is asserted here.
The worked ExplicitTwoSelmerCokernel remains the concrete donor showing what a
literal residual carrier should look like; identifying a universal residual
with Sha[p] is a separate arithmetic theorem.

The payoff is directional:

* MW <= analytic tolerates nonzero defect when Selmer <= analytic.
* analytic <= MW through Selmer needs the same-curve defect to vanish.

So Selmer <= MW is no longer an opaque premise: under the exact decomposition
it is equivalent to zero defect.
-/

namespace Synthesis.Millennium.BSD

structure UniversalSelmerDefectDecomposition
    (bg : BSDEstablishedBackground) where
  selmerRank : RationalEllipticCurve → ℕ
  defectRank : RationalEllipticCurve → ℕ
  selmer_eq_mordellWeil_add_defect :
    ∀ E : RationalEllipticCurve,
      selmerRank E = bg.algebraic.rank E + defectRank E

namespace UniversalSelmerDefectDecomposition

variable {bg : BSDEstablishedBackground}
variable (d : UniversalSelmerDefectDecomposition bg)

theorem mordellWeil_le_selmer
    (E : RationalEllipticCurve) :
    bg.algebraic.rank E ≤ d.selmerRank E := by
  rw [d.selmer_eq_mordellWeil_add_defect E]
  exact Nat.le_add_right _ _

theorem selmer_le_mordellWeil_iff_defect_zero
    (E : RationalEllipticCurve) :
    d.selmerRank E ≤ bg.algebraic.rank E ↔ d.defectRank E = 0 := by
  rw [d.selmer_eq_mordellWeil_add_defect E]
  omega

theorem selmer_eq_mordellWeil_iff_defect_zero
    (E : RationalEllipticCurve) :
    d.selmerRank E = bg.algebraic.rank E ↔ d.defectRank E = 0 := by
  rw [d.selmer_eq_mordellWeil_add_defect E]
  omega

end UniversalSelmerDefectDecomposition

structure UniversalSelmerDefectAnalyticBridge
    (bg : BSDEstablishedBackground) where
  arithmetic : UniversalSelmerDefectDecomposition bg
  selmer_le_analytic :
    ∀ E : RationalEllipticCurve,
      arithmetic.selmerRank E ≤ bg.analytic.rank E
  analytic_le_selmer :
    ∀ E : RationalEllipticCurve,
      bg.analytic.rank E ≤ arithmetic.selmerRank E

theorem lowerRankBound_of_selmerDefectBridge
    (bg : BSDEstablishedBackground)
    (bridge : UniversalSelmerDefectAnalyticBridge bg) :
    UniversalBSDLowerRankBound bg := by
  intro E
  exact
    (bridge.arithmetic.mordellWeil_le_selmer E).trans
      (bridge.selmer_le_analytic E)

def UniversalSelmerDefectZero
    (bg : BSDEstablishedBackground)
    (d : UniversalSelmerDefectDecomposition bg) : Prop :=
  ∀ E : RationalEllipticCurve, d.defectRank E = 0

theorem upperRankBound_of_selmerDefectBridge_and_zero
    (bg : BSDEstablishedBackground)
    (bridge : UniversalSelmerDefectAnalyticBridge bg)
    (hZero : UniversalSelmerDefectZero bg bridge.arithmetic) :
    UniversalBSDUpperRankBound bg := by
  intro E
  exact
    (bridge.analytic_le_selmer E).trans
      ((bridge.arithmetic.selmer_le_mordellWeil_iff_defect_zero E).2
        (hZero E))

theorem defect_zero_of_selmer_le_mordellWeil
    (bg : BSDEstablishedBackground)
    (d : UniversalSelmerDefectDecomposition bg)
    (E : RationalEllipticCurve)
    (h : d.selmerRank E ≤ bg.algebraic.rank E) :
    d.defectRank E = 0 :=
  (d.selmer_le_mordellWeil_iff_defect_zero E).1 h

theorem bsdClayCore_of_selmerDefectBridge_and_zero
    (bg : BSDEstablishedBackground)
    (bridge : UniversalSelmerDefectAnalyticBridge bg)
    (hZero : UniversalSelmerDefectZero bg bridge.arithmetic) :
    BSDClayCoreObligation bg :=
  bsdClayCore_of_independent_rank_bounds bg
    (lowerRankBound_of_selmerDefectBridge bg bridge)
    (upperRankBound_of_selmerDefectBridge_and_zero bg bridge hZero)

abbrev WorkedCaseSelmerResidualCarrier :=
  ExplicitTwoSelmerCokernel

theorem workedCaseResidualMap_surjective :
    Function.Surjective explicitTwoSelmerCokernelMap :=
  explicitTwoSelmerCokernelMap_surjective

theorem workedCaseResidualKernel_is_globalKummerImage :
    explicitTwoSelmerCokernelMap.ker
      = globalKummerQuotientToSelmer.range := by
  symm
  exact globalKummer_range_eq_cokernel_kernel

/-!
## Frontier

Paid at the universal rank-interface level:

  Selmer(E) = MW(E) + defect(E)

turns the reverse arithmetic comparison into the exact theorem

  defect(E) = 0.

Still unpaid:

* a universal elliptic Selmer carrier on the frozen RationalEllipticCurve;
* a literal universal residual quotient/cokernel on that SAME curve;
* identification/control of that residual (classically a Sha-type defect);
* the analytic comparison(s).

Thus this file sharpens the BSD obstruction without pretending the worked
2-Selmer cokernel is already universal.
-/

end Synthesis.Millennium.BSD
