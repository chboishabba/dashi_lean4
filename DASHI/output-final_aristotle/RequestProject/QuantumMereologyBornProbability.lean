import RequestProject.QuantumMereologyStandardBasisProjector
import Mathlib.Analysis.Matrix.PosDef

/-!
# Finite Born-probability closure for a concrete coordinate projector family

The generic pointer-probability owner defines

  p_j = Re Tr(rho P_j)

but deliberately leaves positivity and normalisation as separate authority.
For the concrete coordinate rank-one projectors constructed in
`QuantumMereologyStandardBasisProjector`, those obligations follow from the
existing finite density-matrix laws:

* positivity of rho gives nonnegative diagonal entries;
* trace-one gives normalisation of the diagonal probabilities.

This is a finite matrix theorem.  It does not identify the coordinate basis with
the physical pointer basis of an arbitrary selected Carroll--Singh CPO.  That
same-object identification still requires the typed spectral refinement already
separated by `QuantumMereologyFiniteHermitianCPO`.
-/

namespace QuantumMereology
namespace BornProbability

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- In the concrete coordinate projector family, the trace readout is exactly
the real part of the selected diagonal density-matrix entry. -/
theorem coordinate_probability_eq_diagonalReal
    (rho : ReducedState.DensityMatrix I)
    (j : I) :
    PointerProbability.probability rho
        (StandardBasisProjector.family (I := I)) j =
      Complex.re (rho.matrix j j) := by
  classical
  simp [PointerProbability.probability,
    StandardBasisProjector.family,
    StandardBasisProjector.projector,
    StandardBasisProjector.indicator,
    Matrix.trace, Matrix.mul_apply]

/-- Positivity of the density matrix pays Born-probability nonnegativity for the
coordinate projector family. -/
theorem coordinate_probability_nonnegative
    (rho : ReducedState.DensityMatrix I)
    (j : I) :
    0 ≤ PointerProbability.probability rho
      (StandardBasisProjector.family (I := I)) j := by
  rw [coordinate_probability_eq_diagonalReal]
  exact (RCLike.nonneg_iff.mp (rho.positive.diag_nonneg (i := j))).1

/-- Trace one pays normalisation of all coordinate Born probabilities. -/
theorem coordinate_probability_normalized
    (rho : ReducedState.DensityMatrix I) :
    (∑ j : I,
      PointerProbability.probability rho
        (StandardBasisProjector.family (I := I)) j) = 1 := by
  simp_rw [coordinate_probability_eq_diagonalReal]
  simpa [Matrix.trace] using congrArg Complex.re rho.traceOne

/-- The generic probability-authority socket is inhabited for the concrete
coordinate projector family. -/
def coordinateProbabilityAuthority
    (rho : ReducedState.DensityMatrix I) :
    PointerProbability.ProbabilityAuthority rho
      (StandardBasisProjector.family (I := I)) where
  nonnegative := coordinate_probability_nonnegative rho
  normalized := coordinate_probability_normalized rho

structure Boundary where
  coordinateBornProbabilityNonnegativePaid : Bool := true
  coordinateBornProbabilityNormalizedPaid : Bool := true
  coordinateProbabilityCreatesPhysicalPointerIdentification : Bool := false
  probabilityClosureSelectsPreferredTPS : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem coordinate_born_probability_nonnegative_paid :
    canonicalBoundary.coordinateBornProbabilityNonnegativePaid = true := rfl

theorem coordinate_born_probability_normalized_paid :
    canonicalBoundary.coordinateBornProbabilityNormalizedPaid = true := rfl

theorem coordinate_probability_does_not_create_physical_pointer_identification :
    canonicalBoundary.coordinateProbabilityCreatesPhysicalPointerIdentification = false := rfl

/-- Imported theorem-source receipt: no physics source is credited with the
local matrix proof. -/
def mathlibBornProbabilitySource : AttributionReceipt where
  role := .importedFormalTheoremSource
  owner := "mathlib v4.28.0, Matrix.PosSemidef.diag_nonneg / Matrix.trace"
  claim := "Supplies nonnegativity of diagonal entries of a positive-semidefinite matrix and finite trace infrastructure used to prove coordinate Born-probability nonnegativity and normalisation."

/-- DASHI theorem receipt for the finite matrix closure. -/
def dashiBornProbabilityReceipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "For the concrete coordinate rank-one projector family, proves p_j = Re(rho_jj), p_j >= 0, and sum_j p_j = 1 for every finite PSD trace-one density matrix. It does not identify the coordinate family with a physical selected-CPO pointer basis."

end BornProbability
end QuantumMereology
