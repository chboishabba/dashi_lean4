import Synthesis.MillenniumBSDUniversalTwoDescentResidualCarrier
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Universal two-descent structure: a tautological quotient countermodel

The structure `UniversalTwoDescentResidualOn E` records a short exact
sequence but DOES NOT require the middle group to be an independently
defined all-place Selmer group.

For every E one can choose

  Selmer := E(Q) / 2 E(Q)
  Residual := PUnit,

with the quotient homomorphism followed by the trivial homomorphism.

Thus the *existing universal structure is trivially inhabitable* and its
residual can be zero on all curves by definition.  Neither theorem can
possibly imply genuine Selmer arithmetic, Sha[2]-identification or BSD.

This is a concrete semantic countermodel, not another hypothetical
interface.  It closes the search for an inhabitant of the bare structure
and redirects work to the actual arithmetic Selmer construction.
-/

namespace Synthesis.Millennium.BSD

noncomputable def quotientOnlyTwoDescent
    (E : RationalEllipticCurve) :
    UniversalTwoDescentResidualOn E := by
  letI : E.1.IsElliptic := E.2
  let G := Multiplicative E.1.toAffine.Point
  let N : Subgroup G := rationalDoubleSubgroup E
  letI : N.Normal := Subgroup.normal_of_comm N
  letI : CommGroup (G ⧸ N) := inferInstance
  refine {
    Selmer := G ⧸ N
    Residual := PUnit
    selmerGroup := inferInstance
    residualGroup := inferInstance
    kummer := QuotientGroup.mk' N
    residualMap := 1
    kummerKernelExactlyDoubles := ?_
    residualSurjective := ?_
    exactMiddle := ?_
  }
  · intro P
    change (QuotientGroup.mk' N) (Multiplicative.ofAdd P) = 1 ↔
      IsRationalPointDouble E P
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  · intro r
    exact ⟨1, Subsingleton.elim _ _⟩
  · intro s
    constructor
    · intro _
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N s
      exact ⟨x.toAdd, hx⟩
    · intro _
      exact Subsingleton.elim _ _

/-- The bare all-curve structure has a universal inhabitant without any
global/local cohomology, arithmetic Selmer subgroup or analytic input. -/
theorem bareUniversalTwoDescentCarrier :
    UniversalTwoDescentResidualCarrier :=
  fun E => ⟨quotientOnlyTwoDescent E⟩

/-- In this countermodel the residual is definitionally the one-point group.
No claim about the genuine Tate--Shafarevich group follows. -/
theorem quotientOnlyResidualSubsingleton
    (E : RationalEllipticCurve) :
    Subsingleton (quotientOnlyTwoDescent E).Residual :=
  inferInstance

end Synthesis.Millennium.BSD
