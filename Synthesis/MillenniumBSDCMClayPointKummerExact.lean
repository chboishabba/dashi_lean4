import Synthesis.MillenniumBSDCMWorkedSelmerResidualSameCurve
import Synthesis.MillenniumBSDGlobalKummerKernelExact
import Synthesis.MillenniumBSDUniversalTwoDescentResidualCarrier
import Mathlib.Tactic

/-!
# Actual point-level CM Kummer map on the literal Clay curve

The legacy CM two-descent is on RationalProjectivePoint.  The repository has
already proved an additive equivalence with the Mathlib rational point group
of the exact Clay-facing curve cmRationalEllipticCurve.

Transport the genuine global Kummer hom through that equivalence.  This file
does not define a fresh "Selmer observer" or use an abstract rank mediator.

The output is an actual homomorphism on the Clay point carrier and an exact
kernel = doubles theorem. Together with the existing residual quotient this
is the point-level input for an eventual concrete inhabitant of
UniversalTwoDescentResidualOn cmRationalEllipticCurve.
-/

namespace Synthesis.Millennium.BSD

noncomputable section

private noncomputable instance : cmRationalEllipticCurve.1.IsElliptic :=
  cmRationalEllipticCurve.2

/-- Genuine group hom from the Clay curve's rational points to the legacy
rational point carrier, transported along the existing additive equivalence. -/
noncomputable def cmClayPointsToLegacy :
    Multiplicative CMClayRationalPoint →*
      Multiplicative RationalProjectivePoint where
  toFun point :=
    Multiplicative.ofAdd
      (rationalProjectivePointAddEquivCMClay.symm point.toAdd)
  map_one' := by
    change Multiplicative.ofAdd
      (rationalProjectivePointAddEquivCMClay.symm (0 : CMClayRationalPoint))
      = 1
    simp
  map_mul' := by
    intro x y
    change Multiplicative.ofAdd
      (rationalProjectivePointAddEquivCMClay.symm (x.toAdd + y.toAdd))
      =
      Multiplicative.ofAdd
        (rationalProjectivePointAddEquivCMClay.symm x.toAdd +
          rationalProjectivePointAddEquivCMClay.symm y.toAdd)
    rw [map_add]

/-- Literal CM Clay Kummer hom into the already constructed all-place Selmer. -/
noncomputable def cmClayGlobalKummerHom :
    Multiplicative CMClayRationalPoint →*
      explicitTwoSelmerSubgroup :=
  globalKummerSelmerHom.comp cmClayPointsToLegacy

/-- The same CM point, expressed either through Clay's additive point type
or the legacy projective point type, has the same Kummer output. -/
theorem cmClayGlobalKummerHom_apply
    (P : CMClayRationalPoint) :
    cmClayGlobalKummerHom (Multiplicative.ofAdd P) =
      globalKummerSelmerHom
        (Multiplicative.ofAdd
          (rationalProjectivePointAddEquivCMClay.symm P)) :=
  rfl

/-- The transported map has exactly the rational doubles as kernel. -/
theorem cmClayGlobalKummerHom_kernel_iff_double
    (P : CMClayRationalPoint) :
    cmClayGlobalKummerHom (Multiplicative.ofAdd P) = 1
      ↔
    IsRationalPointDouble cmRationalEllipticCurve P := by
  have hLegacy :
      globalKummerSelmerHom
        (Multiplicative.ofAdd
          (rationalProjectivePointAddEquivCMClay.symm P)) = 1
        ↔
      ∃ Q : RationalProjectivePoint,
        rationalProjectivePointAddEquivCMClay.symm P = Q + Q := by
    rw [← globalDoubleSubgroup_eq_selmerKernel]
    rfl
  change
    globalKummerSelmerHom
      (Multiplicative.ofAdd
        (rationalProjectivePointAddEquivCMClay.symm P)) = 1
      ↔
    ∃ Q : CMClayRationalPoint, P = Q + Q
  constructor
  · intro h
    rcases hLegacy.mp h with ⟨Q, hQ⟩
    refine ⟨rationalProjectivePointAddEquivCMClay Q, ?_⟩
    have mapped := congrArg rationalProjectivePointAddEquivCMClay hQ
    simpa only [map_add,
      rationalProjectivePointAddEquivCMClay.apply_symm_apply] using mapped
  · rintro ⟨Q, hQ⟩
    apply hLegacy.mpr
    refine ⟨rationalProjectivePointAddEquivCMClay.symm Q, ?_⟩
    rw [hQ, map_add]

/-!
Remaining worked-instance debt: turn the existing exact-middle quotient theorem
into a point-level exact-middle proof on the transported Clay map. After that,
the literal residual map can be installed as an actual concrete
UniversalTwoDescentResidualOn cmRationalEllipticCurve. No all-curve statement
or Sha identification follows from the present theorem.
-/

end

end Synthesis.Millennium.BSD
