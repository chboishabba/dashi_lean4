import Integration.EisensteinEuclideanDomainExact
import Integration.EisensteinJZeroCMEndomorphismExact

/-!
# Concrete j=0 CM fixture on the fraction field of DASHI's Eisenstein integers

The field in this owner is not a fresh complex surrogate.  It is literally the
fraction field of the `QuadraticAlgebra Int (-1) (-1)` carrier already used by
the Eisenstein norm-shell / Euclidean-domain / representation-counting chain.
Thus the arithmetic lattice and the elliptic j=0 action share one declared
Eisenstein arithmetic lineage.

Mathlib supplies the fraction field, Weierstrass curve, native affine point
group and j-invariant.  DASHI supplies the same-object specialization and the
bridge to the already-proved order-three group endomorphism.
-/

namespace Integration.EisensteinJZeroCMConcreteExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinEuclideanDomainExact
open WeierstrassCurve

noncomputable section

/-- Fraction field of the exact Eisenstein integer carrier used by PR #69. -/
abbrev EisensteinField := FractionRing EisensteinQA

local instance : DecidableEq EisensteinField := Classical.decEq _

/-- The same quadratic-algebra generator, embedded into its fraction field. -/
def eisensteinOmega : EisensteinField :=
  algebraMap EisensteinQA EisensteinField QuadraticAlgebra.omega

private theorem integralOmega_cube :
    (QuadraticAlgebra.omega : EisensteinQA) ^ 3 = 1 := by
  calc
    (QuadraticAlgebra.omega : EisensteinQA) ^ 3 =
        QuadraticAlgebra.omega * (QuadraticAlgebra.omega : EisensteinQA) ^ 2 := by ring
    _ = QuadraticAlgebra.omega * (-(1 : EisensteinQA) - QuadraticAlgebra.omega) := by
      rw [omega_square_relation]
    _ = -QuadraticAlgebra.omega - (QuadraticAlgebra.omega : EisensteinQA) ^ 2 := by ring
    _ = 1 := by
      rw [omega_square_relation]
      ring

/-- The fraction-field generator is an exact cube root of unity. -/
theorem eisensteinOmega_cube : eisensteinOmega ^ 3 = 1 := by
  have h := congrArg (algebraMap EisensteinQA EisensteinField) integralOmega_cube
  simpa [eisensteinOmega] using h

private theorem integralOmega_ne_one :
    (QuadraticAlgebra.omega : EisensteinQA) ≠ 1 := by
  intro h
  have him := congrArg (fun z : EisensteinQA => z.im) h
  have : (1 : Int) = 0 := by simpa using him
  exact one_ne_zero this

/-- The selected cube root is nontrivial. -/
theorem eisensteinOmega_ne_one : eisensteinOmega ≠ 1 := by
  intro h
  apply integralOmega_ne_one
  apply IsFractionRing.injective EisensteinQA EisensteinField
  simpa [eisensteinOmega] using h

/-- Literal short Weierstrass model `y^2 = x^3 + 1` over the Eisenstein field. -/
def eisensteinJZeroCurve : WeierstrassCurve EisensteinField :=
  ⟨0, 0, 0, 0, 1⟩

@[simp] theorem eisensteinJZeroCurve_a1 : eisensteinJZeroCurve.a₁ = 0 := rfl
@[simp] theorem eisensteinJZeroCurve_a2 : eisensteinJZeroCurve.a₂ = 0 := rfl
@[simp] theorem eisensteinJZeroCurve_a3 : eisensteinJZeroCurve.a₃ = 0 := rfl
@[simp] theorem eisensteinJZeroCurve_a4 : eisensteinJZeroCurve.a₄ = 0 := rfl
@[simp] theorem eisensteinJZeroCurve_a6 : eisensteinJZeroCurve.a₆ = 1 := rfl

private theorem eisensteinJZeroCurve_delta :
    eisensteinJZeroCurve.Δ = -(432 : EisensteinField) := by
  norm_num [eisensteinJZeroCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private theorem eisensteinJZeroCurve_delta_ne_zero : eisensteinJZeroCurve.Δ ≠ 0 := by
  rw [eisensteinJZeroCurve_delta]
  norm_num

noncomputable instance eisensteinJZeroCurve_isElliptic : eisensteinJZeroCurve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr eisensteinJZeroCurve_delta_ne_zero⟩

private theorem eisensteinJZeroCurve_c4 : eisensteinJZeroCurve.c₄ = 0 := by
  norm_num [eisensteinJZeroCurve, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]

/-- Native Mathlib j-invariant of the exact concrete curve is zero. -/
theorem eisensteinJZeroCurve_j_eq_zero : eisensteinJZeroCurve.j = 0 :=
  eisensteinJZeroCurve.j_eq_zero eisensteinJZeroCurve_c4

/-- The same-field, native-point-group CM rotation. -/
noncomputable def eisensteinCMEndomorphism :
    eisensteinJZeroCurve.Point →+ eisensteinJZeroCurve.Point :=
  Integration.jZeroRotationEndomorphism
    eisensteinJZeroCurve eisensteinOmega
    rfl rfl rfl rfl
    eisensteinOmega_cube eisensteinOmega_ne_one

/-- Three applications of the concrete endomorphism are literally the identity. -/
theorem eisensteinCMEndomorphism_orderThree
    (P : eisensteinJZeroCurve.Point) :
    eisensteinCMEndomorphism
      (eisensteinCMEndomorphism (eisensteinCMEndomorphism P)) = P := by
  exact Integration.jZeroRotationEndomorphism_orderThree
    eisensteinJZeroCurve eisensteinOmega
    rfl rfl rfl rfl
    eisensteinOmega_cube eisensteinOmega_ne_one P

/-- Same-object status after this tranche. -/
structure ConcreteCMBoundary : Prop where
  sameEisensteinIntegerCarrierFractionField : True
  nativeEllipticPointGroup : True
  nativeJInvariantZero : True
  orderThreeAdditiveEndomorphism : True
  fullEndomorphismRingIdentifiedWithEisensteinOrder : False
  heckeCharacterConstructed : False
  localEulerFactorsMatched : False
  ellipticLSeriesMatched : False

end

end Integration.EisensteinJZeroCMConcreteExact
