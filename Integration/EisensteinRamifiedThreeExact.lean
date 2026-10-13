import Integration.EisensteinQuadraticAlgebraExact

namespace Dashi.EisensteinRamifiedThreeExact

open Dashi.EisensteinQuadraticAlgebraExact

/-- The standard Eisenstein prime above `3`, represented as `1 - ω`. -/
def ramifiedPrime : EisensteinQA := asQuadraticAlgebra 1 (-1)

/-- The square `(1-ω)^2 = -3ω`, written on the same standard carrier. -/
def minusThreeOmega : EisensteinQA := asQuadraticAlgebra 0 (-3)

/-- The ramified prime has norm exactly `3`. -/
theorem ramifiedPrime_norm_three :
    QuadraticAlgebra.norm ramifiedPrime = 3 := by
  native_decide

/-- Exact ramification identity: `(1-ω)^2 = -3ω`.  Since `ω` is a norm-one
unit, this is the expected factorisation of the rational prime `3` up to a
unit. -/
theorem ramifiedPrime_square :
    ramifiedPrime * ramifiedPrime = minusThreeOmega := by
  native_decide

/-- The unit factor in the ramification identity has norm one. -/
theorem omega_unit_norm_one :
    QuadraticAlgebra.norm (QuadraticAlgebra.omega : EisensteinQA) = 1 :=
  omega_norm_one

structure RamifiedThreeBoundary where
  normThreePaid : Bool := true
  squareFactorisationPaid : Bool := true
  unitNormPaid : Bool := true
  idealRamificationTheoryPaid : Bool := false
  splitPrimeClassificationPaid : Bool := false
  inertResidueClassificationPaid : Bool := false
  ufdRepresentationCountingPaid : Bool := false

def canonicalBoundary : RamifiedThreeBoundary := {}

end Dashi.EisensteinRamifiedThreeExact
