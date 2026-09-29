import Synthesis.MillenniumBSDUniversalTwoDescentResidualCarrier
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic

/-!
# BSD tautological two-descent exact-sequence model

The current UniversalTwoDescentResidualOn E interface allows any group whose
kernel and image give an exact sequence. For every curve we can take:

 Selmer := E(Q)/2E(Q)
 Residual := PUnit
 kummer := canonical quotient
 residualMap := constant map to PUnit.

This produces a universal inhabitant WITHOUT a global/local Selmer group,
Galois cohomology, or Sha(E)[2]. The repaired arithmetic target must require
an independently defined all-place Selmer carrier.
-/

namespace Synthesis.Millennium.BSD

noncomputable section

abbrev QuotientOnlyTwoSelmer (E : RationalEllipticCurve) :=
  letI : E.1.IsElliptic := E.2
  Multiplicative E.1.toAffine.Point ⧸ rationalDoubleSubgroup E

def quotientOnlyResidualMap (E : RationalEllipticCurve) :
    QuotientOnlyTwoSelmer E →* PUnit where
  toFun := fun _ => PUnit.unit
  map_one' := rfl
  map_mul' := by intros; rfl

theorem quotientOnlyKummerKernelExactlyDoubles
    (E : RationalEllipticCurve) :
    letI : E.1.IsElliptic := E.2
    ∀ P : E.1.toAffine.Point,
      (QuotientGroup.mk' (rationalDoubleSubgroup E))
          (Multiplicative.ofAdd P) = 1
        ↔ IsRationalPointDouble E P := by
  letI : E.1.IsElliptic := E.2
  intro P
  simpa [IsRationalPointDouble, QuotientGroup.mk'_apply,
    rationalDoubleSubgroup] using
    (QuotientGroup.eq_one_iff
      (N := rationalDoubleSubgroup E)
      (Multiplicative.ofAdd P))

noncomputable def quotientOnlyDescent
    (E : RationalEllipticCurve) :
    UniversalTwoDescentResidualOn E where
  Selmer := QuotientOnlyTwoSelmer E
  Residual := PUnit
  selmerGroup := inferInstance
  residualGroup := inferInstance
  kummer := by
    letI : E.1.IsElliptic := E.2
    exact QuotientGroup.mk' (rationalDoubleSubgroup E)
  residualMap := quotientOnlyResidualMap E
  kummerKernelExactlyDoubles :=
    quotientOnlyKummerKernelExactlyDoubles E
  residualSurjective := by
    intro r
    cases r
    exact ⟨1, rfl⟩
  exactMiddle := by
    letI : E.1.IsElliptic := E.2
    intro s
    constructor
    · intro _
      obtain ⟨P, hP⟩ :=
        QuotientGroup.mk'_surjective
          (rationalDoubleSubgroup E) s
      exact ⟨P.toAdd, hP⟩
    · intro _
      rfl

theorem oldUniversalTwoDescentCarrier_isTautologicallyInhabited :
    UniversalTwoDescentResidualCarrier :=
  fun E => ⟨quotientOnlyDescent E⟩

theorem quotientOnlyResidualSubsingleton
    (E : RationalEllipticCurve) :
    Subsingleton (quotientOnlyDescent E).Residual :=
  inferInstance

/-!
This is a strength countermodel, not actual elliptic Selmer arithmetic.
The existing CM worked curve has genuine local-condition-defined Selmer data.
An all-curves arithmetic theorem must retain that independent definition,
not simply inhabit the old exact-sequence record.
-/

end

end Synthesis.Millennium.BSD
