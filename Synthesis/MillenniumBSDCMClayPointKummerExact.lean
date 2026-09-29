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
    change
      (Multiplicative.ofAdd
        (rationalProjectivePointAddEquivCMClay.symm P)) ∈
          globalKummerSelmerHom.ker
        ↔
      (Multiplicative.ofAdd
        (rationalProjectivePointAddEquivCMClay.symm P)) ∈
          globalDoubleSubgroup
    rw [← globalDoubleSubgroup_eq_selmerKernel]
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
## Literal exact-middle transport

The explicit cokernel's middle exactness was originally stated with the
quotient MW/2 source. Its source quotient is a genuine quotient group, so a
quotient witness can be represented by an actual rational point. This permits
the exact same statement on the point-level Kummer hom.
-/

/-- Every quotient-class Kummer value is obtained from an actual legacy
rational point, by quotient induction rather than a chosen representative. -/
theorem cmLegacyKummerQuotient_hasPointRepresentative
    (q : CMClayMordellWeilModuloTwo) :
    ∃ P : RationalProjectivePoint,
      globalKummerSelmerHom (Multiplicative.ofAdd P)
        = cmClayKummerToSelmer q := by
  refine Quotient.inductionOn q ?_
  intro point
  refine ⟨point.toAdd, ?_⟩
  rfl

/-- Exactness at the Selmer term on the actual Clay curve's point carrier. -/
theorem cmClayGlobalKummer_exactMiddle
    (s : explicitTwoSelmerSubgroup) :
    explicitTwoSelmerCokernelMap s = 1
      ↔
    ∃ P : CMClayRationalPoint,
      cmClayGlobalKummerHom (Multiplicative.ofAdd P) = s := by
  constructor
  · intro h
    rcases (explicitTwoSelmerCokernel_exact_middle s).mp h with ⟨q, hq⟩
    rcases cmLegacyKummerQuotient_hasPointRepresentative q with ⟨P, hP⟩
    refine ⟨rationalProjectivePointAddEquivCMClay P, ?_⟩
    change
      globalKummerSelmerHom
        (Multiplicative.ofAdd
          (rationalProjectivePointAddEquivCMClay.symm
            (rationalProjectivePointAddEquivCMClay P))) = s
    simpa only [rationalProjectivePointAddEquivCMClay.symm_apply_apply]
      using hP.trans hq
  · rintro ⟨P, hP⟩
    apply (explicitTwoSelmerCokernel_exact_middle s).mpr
    refine
      ⟨QuotientGroup.mk' globalDoubleSubgroup
        (cmClayPointsToLegacy (Multiplicative.ofAdd P)), ?_⟩
    change
      globalKummerSelmerHom
        (cmClayPointsToLegacy (Multiplicative.ofAdd P)) = s at hP
    exact hP

/--
Actual concrete inhabitant of the universal two-descent *structure* for the
worked CM curve y²=x³-x, obtained from the repo's point-level Kummer map and
its explicit global/local Selmer cokernel.
-/
noncomputable def cmClayTwoDescentResidual :
    UniversalTwoDescentResidualOn cmRationalEllipticCurve where
  Selmer := explicitTwoSelmerSubgroup
  Residual := ExplicitTwoSelmerCokernel
  selmerGroup := inferInstance
  residualGroup := inferInstance
  kummer := cmClayGlobalKummerHom
  residualMap := explicitTwoSelmerCokernelMap
  kummerKernelExactlyDoubles :=
    cmClayGlobalKummerHom_kernel_iff_double
  residualSurjective :=
    explicitTwoSelmerCokernelMap_surjective
  exactMiddle :=
    cmClayGlobalKummer_exactMiddle

/-!
This is a worked-curve inhabitant only. It does not produce Selmer data on
an arbitrary RationalEllipticCurve or identify the residual with Sha[2].
The all-curve theorem, higher descent tower and analytic-rank comparison
remain open, as does exact-head kernel verification of this new file.
-/

end

end Synthesis.Millennium.BSD
