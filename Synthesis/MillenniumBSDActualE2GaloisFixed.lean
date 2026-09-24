import Synthesis.MillenniumBSDActualAlgClosureTwoTorsionExact
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Tactic

/-!
# The actual algebraic-closure E[2] is pointwise Galois-fixed

The absolute Galois group acts coordinatewise on the base-changed CM curve.
Because the four 2-torsion points have rational coordinates 0, ±1, every
`Q`-algebra automorphism fixes them.  Combined with the literal four-point
classification, the actual kernel of `[2]` is pointwise fixed.
-/

namespace Synthesis.Millennium.BSD

abbrev RatAbsoluteGalois := RatAlgClosure ≃ₐ[ℚ] RatAlgClosure

def cmAlgClosureGaloisAction
    (σ : RatAbsoluteGalois) :
    CMAlgClosureProjectivePoint → CMAlgClosureProjectivePoint
  | .infinity => .infinity
  | .affine x y h =>
      .affine (σ x) (σ y) (by
        have hm := congrArg σ h
        simpa using hm)

@[simp] theorem cmAlgClosureGaloisAction_infinity
    (σ : RatAbsoluteGalois) :
    cmAlgClosureGaloisAction σ .infinity = .infinity := rfl

@[simp] theorem cmAlgClosureGaloisAction_zeroPoint
    (σ : RatAbsoluteGalois) :
    cmAlgClosureGaloisAction σ
      (.affine 0 0 (by norm_num) : CMAlgClosureProjectivePoint) =
      .affine 0 0 (by norm_num) := by
  simp [cmAlgClosureGaloisAction]

@[simp] theorem cmAlgClosureGaloisAction_onePoint
    (σ : RatAbsoluteGalois) :
    cmAlgClosureGaloisAction σ
      (.affine 1 0 (by norm_num) : CMAlgClosureProjectivePoint) =
      .affine 1 0 (by norm_num) := by
  simp [cmAlgClosureGaloisAction]

@[simp] theorem cmAlgClosureGaloisAction_negOnePoint
    (σ : RatAbsoluteGalois) :
    cmAlgClosureGaloisAction σ
      (.affine (-1) 0 (by norm_num) : CMAlgClosureProjectivePoint) =
      .affine (-1) 0 (by norm_num) := by
  simp [cmAlgClosureGaloisAction]

theorem cmAlgClosureGaloisAction_zero
    (σ : RatAbsoluteGalois) :
    cmAlgClosureGaloisAction σ 0 = 0 := by
  rw [cmAlgClosure_zero_eq_infinity]
  simp

/-- Every actual 2-torsion point of the base-changed elliptic curve is Galois-fixed. -/
theorem cmAlgClosure_twoTorsion_galoisFixed
    (σ : RatAbsoluteGalois)
    (P : CMAlgClosureProjectivePoint)
    (hP : IsCMAlgClosureTwoTorsion P) :
    cmAlgClosureGaloisAction σ P = P := by
  rcases (cmAlgClosure_twoTorsion_classification P).mp hP with
      h0 | hzero | hone | hneg
  · subst P; exact cmAlgClosureGaloisAction_zero σ
  · subst P; simp
  · subst P; simp
  · subst P; simp

theorem cmAlgClosure_twoTorsionSubgroup_pointwise_fixed
    (σ : RatAbsoluteGalois)
    (P : cmAlgClosureTwoTorsionSubgroup) :
    cmAlgClosureGaloisAction σ P.1 = P.1 := by
  exact cmAlgClosure_twoTorsion_galoisFixed σ P.1 P.2

/--
The live Galois-module seam no longer includes pointwise invariance: the
remaining work is to package this coordinate action as the actual continuous
`TopRep` and identify its four-element additive carrier with the existing
trivial `(Z/2)^2` representation.
-/
structure ActualE2GaloisFixedReceipt where
  actualAlgClosurePointGroupPaid : Prop
  exactKernelClassificationPaid : Prop
  coordinateGaloisActionPaid : Prop
  actualE2PointwiseFixedPaid : Prop
  additiveEquivZ2SquaredPaid : Prop
  continuousTopRepSameObjectPaid : Prop

def actualE2GaloisFixedReceipt : ActualE2GaloisFixedReceipt where
  actualAlgClosurePointGroupPaid := True
  exactKernelClassificationPaid := True
  coordinateGaloisActionPaid := True
  actualE2PointwiseFixedPaid := True
  additiveEquivZ2SquaredPaid := False
  continuousTopRepSameObjectPaid := False

end Synthesis.Millennium.BSD
