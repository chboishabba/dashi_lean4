import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Hodge donor: multiplicity two as a genuine algebraic cycle coefficient

Current Mathlib has a real scheme-level `AlgebraicGeometry.AlgebraicCycle`
carrier and a Weil-divisor predicate. This file uses them directly.

It records two independently proved facts:
1. the local pullback equation X^2 has root multiplicity exactly two at 0;
2. on any scheme, a codimension-one point x with coefficient 2 gives an
   actual algebraic cycle which is a Weil divisor.

The still-open SAME-OBJECT bridge is to instantiate x as the actual point
[1:0] on the projective-line scheme and prove that scheme-theoretic pullback
of its divisor along the quadratic morphism is this cycle. Rational
equivalence/CH^1 and cycle-class compatibility are later obligations.
-/

namespace Synthesis.Millennium.Hodge

open Polynomial
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicCycle

/-- Local affine equation of the pulled-back target point section. -/
def quadraticPointLocalEquation : ℚ[X] := X ^ 2

theorem quadraticPointLocalEquation_rootMultiplicity :
    rootMultiplicity (0 : ℚ) quadraticPointLocalEquation = 2 := by
  rw [← Polynomial.count_roots]
  simp [quadraticPointLocalEquation, pow_two, Polynomial.roots_mul]

section RealCycle

variable {X : Scheme} [DecidableEq X]

/-- A genuine scheme-level algebraic point cycle with integer coefficient one. -/
noncomputable def pointCycle (x : X) : AlgebraicCycle X ℤ :=
  Function.locallyFinsuppWithin.single x 1

/-- The actual multiplicity-two cycle. -/
noncomputable def doublePointCycle (x : X) : AlgebraicCycle X ℤ :=
  pointCycle x + pointCycle x

/-- A codimension-one point determines a genuine Weil divisor. -/
theorem pointCycle_isWeilDivisor
    (x : X) (hx : Order.coheight x = 1) :
    IsWeilDivisor (pointCycle x) := by
  exact isWeilDivisor_single hx 1

/-- Doubling preserves the actual Weil-divisor condition. -/
theorem doublePointCycle_isWeilDivisor
    (x : X) (hx : Order.coheight x = 1) :
    IsWeilDivisor (doublePointCycle x) := by
  exact
    (pointCycle_isWeilDivisor x hx).add
      (pointCycle_isWeilDivisor x hx)

/-- The coefficient at the selected point is literally two. -/
theorem doublePointCycle_coefficient
    (x : X) :
    doublePointCycle x x = 2 := by
  simp [doublePointCycle, pointCycle]

/-- Every other point has coefficient zero. -/
theorem doublePointCycle_off_support
    (x y : X) (hxy : y ≠ x) :
    doublePointCycle x y = 0 := by
  simp [doublePointCycle, pointCycle, hxy]

/-- Two genuine codimension-one cycle generators admit the exact
sum/difference operations needed for the P¹×P¹ ruling regression. -/
noncomputable def polarizationCycle
    {X : Scheme} [DecidableEq X] (h₁ h₂ : X) :
    AlgebraicCycle X ℤ :=
  pointCycle h₁ + pointCycle h₂

noncomputable def rulingDifferenceCycle
    {X : Scheme} [DecidableEq X] (h₁ h₂ : X) :
    AlgebraicCycle X ℤ :=
  pointCycle h₁ - pointCycle h₂

theorem polarizationCycle_isWeilDivisor
    {X : Scheme} [DecidableEq X]
    (h₁ h₂ : X)
    (hh₁ : Order.coheight h₁ = 1)
    (hh₂ : Order.coheight h₂ = 1) :
    IsWeilDivisor (polarizationCycle h₁ h₂) := by
  exact
    (pointCycle_isWeilDivisor h₁ hh₁).add
      (pointCycle_isWeilDivisor h₂ hh₂)

theorem rulingDifferenceCycle_isWeilDivisor
    {X : Scheme} [DecidableEq X]
    (h₁ h₂ : X)
    (hh₁ : Order.coheight h₁ = 1)
    (hh₂ : Order.coheight h₂ = 1) :
    IsWeilDivisor (rulingDifferenceCycle h₁ h₂) := by
  exact
    (pointCycle_isWeilDivisor h₁ hh₁).sub
      (pointCycle_isWeilDivisor h₂ hh₂)

/-- For distinct codimension-one points, the difference cycle is visibly
nonzero on the first generator. -/
theorem rulingDifferenceCycle_coefficient_left
    {X : Scheme} [DecidableEq X]
    (h₁ h₂ : X) (hne : h₁ ≠ h₂) :
    rulingDifferenceCycle h₁ h₂ h₁ = 1 := by
  simp [rulingDifferenceCycle, pointCycle, hne]

theorem rulingDifferenceCycle_coefficient_right
    {X : Scheme} [DecidableEq X]
    (h₁ h₂ : X) (hne : h₁ ≠ h₂) :
    rulingDifferenceCycle h₁ h₂ h₂ = -1 := by
  have hne' : h₂ ≠ h₁ := Ne.symm hne
  simp [rulingDifferenceCycle, pointCycle, hne, hne']

theorem rulingDifferenceCycle_ne_zero
    {X : Scheme} [DecidableEq X]
    (h₁ h₂ : X) (hne : h₁ ≠ h₂) :
    rulingDifferenceCycle h₁ h₂ ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun D : AlgebraicCycle X ℤ => D h₁) hzero
  simpa [rulingDifferenceCycle_coefficient_left h₁ h₂ hne] using hcoeff

end RealCycle

/-!
This is the first donor in the programme that lands in Mathlib's genuine
scheme-level algebraic-cycle API rather than DASHI's earlier permissive
synthetic cycle record.

Not yet proved:
* construction of P^1 as the selected Proj scheme in this module;
* the quadratic homogeneous map as a Scheme morphism;
* scheme-theoretic inverse image of [1:0];
* equality f^*[1:0] = 2[1:0] as a divisor/Chow class;
* the cycle-class map to rational singular cohomology.
-/

end Synthesis.Millennium.Hodge
