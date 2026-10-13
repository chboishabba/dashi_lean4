import Integration.EisensteinLatticeCounting
import Mathlib.Algebra.QuadraticAlgebra.Basic

namespace Dashi.EisensteinQuadraticAlgebraExact

open Dashi.EisensteinLatticeCounting

/-- Standard quadratic-algebra carrier for `ℤ[ω]`, with `ω² = -1 - ω`. -/
abbrev EisensteinQA := QuadraticAlgebra Int (-1) (-1)

/-- Coordinate embedding `(a,b) ↦ a + bω`. -/
def asQuadraticAlgebra (a b : Int) : EisensteinQA :=
  { re := a, im := b }

/-- The standard quadratic-algebra norm is literally `a² - ab + b²`. -/
theorem norm_asQuadraticAlgebra (a b : Int) :
    QuadraticAlgebra.norm (asQuadraticAlgebra a b) = eisensteinNorm a b := by
  simp [asQuadraticAlgebra, QuadraticAlgebra.norm_def, eisensteinNorm]
  ring

/-- Multiplicativity is inherited from the standard quadratic-algebra norm. -/
theorem norm_product_coordinates (a b c d : Int) :
    QuadraticAlgebra.norm (asQuadraticAlgebra a b * asQuadraticAlgebra c d)
      = eisensteinNorm a b * eisensteinNorm c d := by
  rw [map_mul, norm_asQuadraticAlgebra, norm_asQuadraticAlgebra]

/-- The quadratic-algebra generator has unit Eisenstein norm. -/
theorem omega_norm_one :
    QuadraticAlgebra.norm (QuadraticAlgebra.omega : EisensteinQA) = 1 := by
  simp [QuadraticAlgebra.norm_def]

/-- The algebra generator satisfies the Eisenstein relation `ω² = -1 - ω`. -/
theorem omega_square_relation :
    (QuadraticAlgebra.omega : EisensteinQA) ^ 2
      = -(1 : EisensteinQA) - QuadraticAlgebra.omega := by
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
  simp

/-- The representation-count theorem is now isolated beyond the standard ring
and multiplicative norm.  What remains is arithmetic classification of prime
splitting/ramification/inertia and counting associates/factorisations. -/
structure PrimeSplittingCountingSource where
  ramifiedThreeClassification : Prop
  splitPrimeClassification : Prop
  inertPrimeClassification : Prop
  associatesAreExactlySixUnits : Prop
  localFactorCountsCompileToGlobal : Prop

structure AlgebraicBoundary where
  standardQuadraticAlgebraCarrierPaid : Bool := true
  normIdentificationPaid : Bool := true
  normMultiplicativityPaid : Bool := true
  primeSplittingClassificationPaid : Bool := false
  uniqueFactorizationCountingPaid : Bool := false
  positiveRepresentationFormulaPaid : Bool := false

/-- Claim-strength boundary after the standard algebra weld. -/
def canonicalBoundary : AlgebraicBoundary := {}

end Dashi.EisensteinQuadraticAlgebraExact
