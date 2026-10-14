import Integration.EisensteinLatticeCounting
import Integration.EisensteinLatticeCountingMaxCut
import Integration.EisensteinQuadraticAlgebraExact
import Integration.EisensteinInertPrimeLegendreExact
import Integration.EisensteinCharacterLocalFactorsExact
import Integration.EisensteinRamifiedThreeExact
import Integration.EisensteinChoiceRecoveryExact
import Integration.EisensteinCanonicalAssociateExact
import Integration.EisensteinAssociateClassCountExact
import Integration.EisensteinSixUnitOrbitExact
import Integration.EisensteinGeometricRepresentationFormulaExact
import Integration.EisensteinDirichletSeriesExact

namespace Dashi.EisensteinLatticeCountingRegression

open Complex LSeries
open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinLatticeCountingMaxCut
open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinCharacterLocalFactorsExact
open Dashi.EisensteinRamifiedThreeExact
open Dashi.EisensteinGeometricRepresentationFormulaExact
open Dashi.EisensteinDirichletSeriesExact

example : triangularNumber 10 = 55 := by native_decide
example : hexBallCount 3 = 37 := by native_decide
example : wedgeTriangleCount 3 = 10 := by native_decide
example : Nat.choose 4 2 = 6 := by native_decide
example : pascalRowSum 8 = 256 := by native_decide
example : hexBallCount 10 = 331 := by native_decide

example : signedEisensteinDivisorShellCount 1 = 6 := by native_decide
example : signedEisensteinDivisorShellCount 2 = 0 := by native_decide
example : signedEisensteinDivisorShellCount 3 = 6 := by native_decide
example : signedEisensteinDivisorShellCount 7 = 12 := by native_decide

example : eisensteinDivisorShellCount 1 = 6 := by native_decide
example : eisensteinDivisorShellCount 2 = 0 := by native_decide
example : eisensteinDivisorShellCount 3 = 6 := by native_decide
example : eisensteinDivisorShellCount 4 = 6 := by native_decide
example : eisensteinDivisorShellCount 5 = 0 := by native_decide
example : eisensteinDivisorShellCount 6 = 0 := by native_decide
example : eisensteinDivisorShellCount 7 = 12 := by native_decide
example : eisensteinDivisorShellCount 8 = 0 := by native_decide
example : eisensteinDivisorShellCount 9 = 6 := by native_decide
example : eisensteinDivisorShellCount 10 = 0 := by native_decide

example : geometricNormShellCount 0 = 1 := by native_decide
example : signedEisensteinDivisorShellCount 0 = 0 := by native_decide

example : localCharacterFactor 0 5 = 1 := by native_decide
example : localCharacterFactor 1 5 = 6 := by native_decide
example : localCharacterFactor (-1) 5 = 0 := by native_decide
example : localCharacterFactor (-1) 6 = 1 := by native_decide

example : eisensteinNorm 2 1 = 3 := by native_decide
example : QuadraticAlgebra.norm (asQuadraticAlgebra 2 1) = 3 := by native_decide
example : QuadraticAlgebra.norm ramifiedPrime = 3 := by native_decide
example : ramifiedPrime * ramifiedPrime = minusThreeOmega := by native_decide
example : rotate (2,1) = (1,2) := by native_decide
example : rotate (rotate (rotate (rotate (rotate (rotate (2,1)))))) = (2,1) := by native_decide

/-- Universal coefficient theorem: no finite-bound qualifier remains. -/
example (n : Nat) :
    (geometricNormShellCount (n + 1) : Int)
      = signedEisensteinDivisorShellCount (n + 1) :=
  geometricNormShell_eq_signedDivisorShell_positive n

/-- Analytic factorization on the common half-plane of absolute convergence. -/
example (s : ℂ) (hs : 1 < s.re) :
    LSeries eisensteinGeometricCoefficient s
      = 6 * riemannZeta s * chiMinus3LSeries s :=
  eisensteinGeometricLSeries_factorization s hs

end Dashi.EisensteinLatticeCountingRegression
