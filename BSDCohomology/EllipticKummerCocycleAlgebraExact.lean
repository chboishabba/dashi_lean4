import BSDCohomology.EllipticTwoTorsionAction
import Mathlib.Tactic

/-!
# Algebraic Kummer crossed cocycle from a geometric half

For an actual geometric point P fixed by the absolute Galois group, choose a
geometric half Q with 2Q=P.  The classical Kummer cocycle is

  c_Q(σ) = σ(Q) - Q.

This file proves on the literal Mathlib elliptic-point carrier that:

* c_Q(σ) lies in the actual kernel E[2];
* c_Q(στ) = c_Q(σ) + σ(c_Q(τ));
* changing Q by a Galois-fixed two-torsion point does not change the cocycle.

No H¹ quotient or continuity is postulated here; those are separate topological
and homological packaging obligations.
-/

namespace BSDCohomology

open WeierstrassCurve

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- A point of E(Kbar) fixed by every absolute-Galois automorphism. -/
def IsGaloisFixedPoint (P : GeometricPoint W) : Prop :=
  ∀ σ : Field.absoluteGaloisGroup K, galoisPointMap W σ P = P

/-- A chosen geometric half of a fixed point. -/
structure GeometricHalfData (P : GeometricPoint W) where
  half : GeometricPoint W
  double_half : (2 : ℕ) • half = P

/-- The raw Kummer difference σ(Q)-Q. -/
noncomputable def kummerDifference
    (Q : GeometricPoint W)
    (σ : Field.absoluteGaloisGroup K) : GeometricPoint W :=
  galoisPointMap W σ Q - Q

/-- For a fixed target P and a chosen half Q, the Kummer difference is killed
by two and hence lies in the literal E[2] subgroup. -/
theorem kummerDifference_mem_twoTorsion
    {P : GeometricPoint W}
    (hP : IsGaloisFixedPoint W P)
    (Q : GeometricHalfData W P)
    (σ : Field.absoluteGaloisGroup K) :
    kummerDifference W Q.half σ ∈ EllipticTwoTorsion W := by
  rw [mem_ellipticTwoTorsion_iff]
  unfold kummerDifference
  rw [nsmul_sub]
  rw [← galoisPointMap_double W σ Q.half]
  rw [Q.double_half, hP σ, Q.double_half]
  exact sub_self P

/-- The actual E[2]-valued Kummer function. -/
noncomputable def kummerCocycleValue
    {P : GeometricPoint W}
    (hP : IsGaloisFixedPoint W P)
    (Q : GeometricHalfData W P)
    (σ : Field.absoluteGaloisGroup K) : EllipticTwoTorsion W :=
  ⟨kummerDifference W Q.half σ,
    kummerDifference_mem_twoTorsion W hP Q σ⟩

@[simp] theorem kummerCocycleValue_coe
    {P : GeometricPoint W}
    (hP : IsGaloisFixedPoint W P)
    (Q : GeometricHalfData W P)
    (σ : Field.absoluteGaloisGroup K) :
    (kummerCocycleValue W hP Q σ).1 =
      galoisPointMap W σ Q.half - Q.half := rfl

/-- The literal crossed-cocycle identity. -/
theorem kummerCocycleValue_mul
    {P : GeometricPoint W}
    (hP : IsGaloisFixedPoint W P)
    (Q : GeometricHalfData W P)
    (σ τ : Field.absoluteGaloisGroup K) :
    kummerCocycleValue W hP Q (σ * τ) =
      kummerCocycleValue W hP Q σ +
        galoisTwoTorsionMap W σ (kummerCocycleValue W hP Q τ) := by
  apply Subtype.ext
  change galoisPointMap W (σ * τ) Q.half - Q.half =
    (galoisPointMap W σ Q.half - Q.half) +
      galoisPointMap W σ (galoisPointMap W τ Q.half - Q.half)
  rw [galoisPointMap_mul]
  rw [map_sub]
  abel

/-- The Kummer cocycle is normalized at the identity. -/
@[simp] theorem kummerCocycleValue_one
    {P : GeometricPoint W}
    (hP : IsGaloisFixedPoint W P)
    (Q : GeometricHalfData W P) :
    kummerCocycleValue W hP Q 1 = 0 := by
  apply Subtype.ext
  simp [kummerCocycleValue, kummerDifference, galoisPointMap_one]

/-- Two halves of the same point differ by literal E[2]. -/
noncomputable def halfDifferenceTwoTorsion
    {P : GeometricPoint W}
    (Q₁ Q₂ : GeometricHalfData W P) : EllipticTwoTorsion W := by
  refine ⟨Q₂.half - Q₁.half, ?_⟩
  rw [mem_ellipticTwoTorsion_iff, nsmul_sub,
    Q₂.double_half, Q₁.double_half, sub_self]

/-- If E[2] is pointwise Galois-fixed, then the selected Kummer cocycle is
independent of the chosen geometric half, pointwise (stronger than merely
cohomologous).  This is the situation of the selected CM regression curve. -/
theorem kummerCocycleValue_eq_of_twoTorsion_fixed
    {P : GeometricPoint W}
    (hP : IsGaloisFixedPoint W P)
    (Q₁ Q₂ : GeometricHalfData W P)
    (hfix : ∀ (σ : Field.absoluteGaloisGroup K)
      (T : EllipticTwoTorsion W), galoisTwoTorsionMap W σ T = T)
    (σ : Field.absoluteGaloisGroup K) :
    kummerCocycleValue W hP Q₁ σ =
      kummerCocycleValue W hP Q₂ σ := by
  let T := halfDifferenceTwoTorsion W Q₁ Q₂
  have hT := congrArg Subtype.val (hfix σ T)
  change galoisPointMap W σ Q₁.half - Q₁.half =
    galoisPointMap W σ Q₂.half - Q₂.half
  change galoisPointMap W σ (Q₂.half - Q₁.half) =
    Q₂.half - Q₁.half at hT
  rw [map_sub] at hT
  abel

/-!
MAX-CUT STATUS

PAID:
* actual geometric half data on the literal E(Kbar) carrier;
* literal E[2]-valued Kummer difference;
* crossed-cocycle law;
* normalization;
* exact half-choice independence when E[2] is pointwise fixed.

NEXT:
* prove continuity of σ |-> c_Q(σ) from Krull open stabilizers;
* package this crossed cocycle into Mathlib's homogeneous-cochain H¹ quotient;
* specialize to the selected CM curve and compare through the same-object H¹
  square-class equivalence with the explicit x-T Kummer map.
-/

end

end BSDCohomology
