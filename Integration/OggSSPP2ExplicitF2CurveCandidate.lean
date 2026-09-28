import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Explicit characteristic-two p=2 curve candidate

This is a DASHI finite candidate/source-acquisition object, not yet a proved
same-object identification with the supersingular curve used by the p=2
universal deformation.

We construct the generalized Weierstrass model over F2

  y^2 + y = x^3

with coefficients
  (a1,a2,a3,a4,a6) = (0,0,1,0,0).

Its discriminant is exactly 1, hence a unit.  We also enumerate the affine
F2-solutions and obtain two affine points; including the distinguished point at
infinity gives three F2-rational points.

No supersingularity theorem is claimed in this file.
-/

namespace Integration.OggSSPP2ExplicitF2CurveCandidate

open WeierstrassCurve

abbrev F2 := ZMod 2

def curve : WeierstrassCurve F2 :=
  ⟨0, 0, 1, 0, 0⟩

theorem curve_a1 : curve.a₁ = 0 := rfl
theorem curve_a2 : curve.a₂ = 0 := rfl
theorem curve_a3 : curve.a₃ = 1 := rfl
theorem curve_a4 : curve.a₄ = 0 := rfl
theorem curve_a6 : curve.a₆ = 0 := rfl

theorem curve_discriminant :
    curve.Δ = 1 := by
  native_decide

theorem curve_discriminant_isUnit :
    IsUnit curve.Δ := by
  rw [curve_discriminant]
  exact isUnit_one

def AffineSolution :=
  {p : F2 × F2 // p.2 ^ 2 + p.2 = p.1 ^ 3}

instance : Fintype AffineSolution :=
  Fintype.ofFinite _

theorem affine_solution_count :
    Fintype.card AffineSolution = 2 := by
  native_decide

def rationalPointCount : Nat :=
  Fintype.card AffineSolution + 1

theorem rational_point_count_is_three :
    rationalPointCount = 3 := by
  native_decide

def frobeniusTrace : Int :=
  (2 : Int) + 1 - rationalPointCount

theorem frobenius_trace_is_zero :
    frobeniusTrace = 0 := by
  native_decide

noncomputable def curveBaseChange
    (K : Type*) [Field K] [Algebra F2 K] :
    WeierstrassCurve.Affine K :=
  curve.baseChange K

theorem no_nonzero_affine_two_torsion_after_base_change
    {K : Type*} [Field K] [CharP K 2] [Algebra F2 K]
    {x y : K}
    (h : (curveBaseChange K).Nonsingular x y)
    (h2 :
      WeierstrassCurve.Affine.Point.some x y h +
        WeierstrassCurve.Affine.Point.some x y h = 0) :
    False := by
  have hroot :=
    WeierstrassCurve.Affine.Point.isRoot_twoTorsionPolynomial_of_add_self
      h h2
  simpa [curveBaseChange, curve, WeierstrassCurve.twoTorsionPolynomial,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    Polynomial.IsRoot] using hroot

theorem geometric_two_torsion_trivial
    {K : Type*} [Field K] [CharP K 2] [Algebra F2 K]
    (P : (curveBaseChange K).Point)
    (h2 : P + P = 0) :
    P = 0 := by
  cases P with
  | zero =>
      rfl
  | some x y h =>
      exact False.elim
        (no_nonzero_affine_two_torsion_after_base_change h h2)

structure Boundary where
  explicitF2WeierstrassModelOwned : Bool
  discriminantUnitPaid : Bool
  affineF2PointCountPaid : Bool
  projectivePointCountWithInfinityPaid : Bool
  frobeniusTraceZeroPaid : Bool
  noNonzeroAffineTwoTorsionAfterCharTwoBaseChangePaid : Bool
  geometricTwoTorsionTrivialPaid : Bool
  supersingularityCriterionWeldPaid : Bool
  supersingularityIdentified : Bool
  universalDeformationSourceSameObject : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  explicitF2WeierstrassModelOwned := true
  discriminantUnitPaid := true
  affineF2PointCountPaid := true
  projectivePointCountWithInfinityPaid := true
  frobeniusTraceZeroPaid := true
  noNonzeroAffineTwoTorsionAfterCharTwoBaseChangePaid := true
  geometricTwoTorsionTrivialPaid := true
  supersingularityCriterionWeldPaid := false
  supersingularityIdentified := false
  universalDeformationSourceSameObject := false

end Integration.OggSSPP2ExplicitF2CurveCandidate
