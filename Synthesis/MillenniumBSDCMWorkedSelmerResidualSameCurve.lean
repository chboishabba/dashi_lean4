import Synthesis.MillenniumBSDUniversalRankWeld
import Synthesis.MillenniumBSDActualRationalPointGroup
import Synthesis.MillenniumBSDExplicitSelmerCokernelExact
import Mathlib.Tactic

/-!
# CM worked two-descent residual on the exact Clay curve

The explicit Kummer/Selmer/cokernel development predates the universal
RationalEllipticCurve Clay surface, but its rational point carrier is already
proved additively equivalent to Mathlib's literal point group of cmWeierstrass.

This file pins that worked descent chain to the exact Clay object

  cmRationalEllipticCurve : RationalEllipticCurve.

It does NOT universalize the construction.  It proves only that the existing
worked E(Q)/2E(Q) -> Sel_2(E) -> residual cokernel is genuinely on the same CM
curve used by the Clay-facing rank owner.
-/

namespace Synthesis.Millennium.BSD

theorem cmClayCurve_weierstrass_sameObject :
    cmRationalEllipticCurve.1 = cmWeierstrass :=
  rfl

abbrev CMClayRationalPoint :=
  cmRationalEllipticCurve.1.toAffine.Point

noncomputable def rationalProjectivePointAddEquivCMClay :
    RationalProjectivePoint ≃+ CMClayRationalPoint := by
  simpa [CMClayRationalPoint, cmRationalEllipticCurve] using
    rationalProjectivePointAddEquivMathlib

theorem rationalProjectivePointAddEquivCMClay_bijective :
    Function.Bijective rationalProjectivePointAddEquivCMClay :=
  rationalProjectivePointAddEquivCMClay.bijective

/-- The worked source of the global Kummer quotient, explicitly labelled as
the Mordell--Weil-mod-2 carrier of the exact CM Clay curve. -/
abbrev CMClayMordellWeilModuloTwo :=
  Multiplicative RationalProjectivePoint ⧸ globalDoubleSubgroup

/-- The worked all-place 2-Selmer carrier on the same CM curve. -/
abbrev CMClayExplicitTwoSelmer :=
  explicitTwoSelmerSubgroup

/-- The literal residual quotient after the Kummer image. -/
abbrev CMClayTwoSelmerResidual :=
  ExplicitTwoSelmerCokernel

noncomputable def cmClayKummerToSelmer :
    CMClayMordellWeilModuloTwo →*
      CMClayExplicitTwoSelmer :=
  globalKummerQuotientToSelmer

noncomputable def cmClaySelmerToResidual :
    CMClayExplicitTwoSelmer →*
      CMClayTwoSelmerResidual :=
  explicitTwoSelmerCokernelMap

theorem cmClayKummerToSelmer_injective :
    Function.Injective cmClayKummerToSelmer :=
  globalKummerQuotientToSelmer_injective

theorem cmClaySelmerToResidual_surjective :
    Function.Surjective cmClaySelmerToResidual :=
  explicitTwoSelmerCokernelMap_surjective

theorem cmClay_twoDescent_exact_middle :
    ∀ s : CMClayExplicitTwoSelmer,
      cmClaySelmerToResidual s = 1
        ↔
      ∃ q : CMClayMordellWeilModuloTwo,
        cmClayKummerToSelmer q = s :=
  explicitTwoSelmerCokernel_exact_middle

theorem cmClay_kummer_range_eq_residual_kernel :
    cmClayKummerToSelmer.range
      =
    cmClaySelmerToResidual.ker :=
  globalKummer_range_eq_cokernel_kernel

/-!
## Same-object coefficient receipt

The Agda short-Weierstrass donor uses y^2 = x^3 + a x + b with
a = -1 and b = 0.  The literal Lean CM curve is exactly
<0,0,0,-1,0>, hence represents y^2 = x^3 - x.

These equalities do not create a cross-language proof bridge; they pin the
mathematical donor to the same coefficients.
-/

theorem cmClay_a1_zero : cmRationalEllipticCurve.1.a₁ = 0 := by
  rfl

theorem cmClay_a2_zero : cmRationalEllipticCurve.1.a₂ = 0 := by
  rfl

theorem cmClay_a3_zero : cmRationalEllipticCurve.1.a₃ = 0 := by
  rfl

theorem cmClay_short_a4_minusOne : cmRationalEllipticCurve.1.a₄ = -1 := by
  rfl

theorem cmClay_short_a6_zero : cmRationalEllipticCurve.1.a₆ = 0 := by
  rfl

/-!
## Frontier

Worked-case same-object status is now sharp:

  exact Clay CM curve
      <- explicit point-group equivalence ->
  worked Kummer source
      -> explicit Sel_2
      -> literal residual cokernel.

Still unpaid:

* a construction for arbitrary RationalEllipticCurve;
* a universal exact sequence on that literal same curve;
* identification of the residual with Sha(E)[2];
* passage from one finite 2-Selmer layer to the stable Selmer/rank defect.

Thus the next BSD implementation is a universal curve-indexed carrier, not
another rank mediator.
-/

end Synthesis.Millennium.BSD
