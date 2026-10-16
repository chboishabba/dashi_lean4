import RequestProject.QuantumMereologyGTPSProjectionProducer

/-!
# Unitary-family generalized-TPS metric formula

Zanardi--Dallas--Andreadakis (2026), after restricting to g-TPS families
unitarily related to a fixed reference algebra, derive

  ds_Theta^2 = kappa^2 || Q_theta(dK) ||_2^2,
  kappa = 2 / dim(A'_0),
  dK = -i dU_theta U_theta^dagger.

This module reconstructs exactly that finite formula on top of the canonical
Hilbert--Schmidt projector produced by `QuantumMereologyGTPSProjectionProducer`.
A proof-relevant tangent record carries the same-object unitary, differential,
generator equation, and fixed commutant dimension.

It deliberately does not differentiate the minimizer map
`lambda -> theta_min(lambda)`, pull this metric back to Hamiltonian parameter
space, establish singular scaling, or prove a thermodynamic m-QPT.
-/

namespace QuantumMereology
namespace GTPSUnitaryMetric2026

/-- Source-shaped infinitesimal datum for one point of a unitarily generated
g-TPS family. -/
structure UnitaryFamilyTangent (n : Nat) where
  gtps : GTPSShortTime2026.SourceGTPS n
  referenceCommutantDimension : Nat
  referenceCommutantDimensionPositive : 0 < referenceCommutantDimension
  commutantDimensionAgrees :
    Module.finrank Complex gtps.commutant = referenceCommutantDimension
  unitary : GTPSShortTime2026.MatrixSpace n
  dUnitary : GTPSShortTime2026.MatrixSpace n
  unitaryLeft : Matrix.conjTranspose unitary * unitary = 1
  unitaryRight : unitary * Matrix.conjTranspose unitary = 1
  dK : GTPSShortTime2026.MatrixSpace n
  dKEquation :
    dK = (-Complex.I) • (dUnitary * Matrix.conjTranspose unitary)
  dKHermitian : dK.IsHermitian

/-- Source normalization `kappa = 2 / dim(A'_0)`. -/
noncomputable def kappa {n : Nat} (X : UnitaryFamilyTangent n) : Real :=
  2 / X.referenceCommutantDimension

/-- Exact finite reconstruction of Eq. (8):
`ds_Theta^2 = kappa^2 ||Q_theta(dK)||_2^2`. -/
noncomputable def metricElementSq {n : Nat}
    (X : UnitaryFamilyTangent n) : Real :=
  (kappa X) ^ 2 *
    GTPSProjectionProducer.canonicalShortTimeScramblingSq X.gtps X.dK

/-- Expanded source identity using the canonical finite HS projection onto
`A_theta + A'_theta`. -/
theorem metricElementSq_eq_source_formula {n : Nat}
    (X : UnitaryFamilyTangent n) :
    metricElementSq X =
      (kappa X) ^ 2 *
        GTPSShortTime2026.hsNormSq
          (X.dK -
            (GTPSProjectionProducer.localPlusCommutantProjection X.gtps).project X.dK) :=
  rfl

/-- The normalization denominator is genuinely nonzero on the declared source
family. -/
theorem referenceCommutantDimension_ne_zero {n : Nat}
    (X : UnitaryFamilyTangent n) : X.referenceCommutantDimension ≠ 0 :=
  Nat.ne_of_gt X.referenceCommutantDimensionPositive

structure Boundary where
  unitaryFamilyMetricFormulaReconstructed : Bool := true
  usesCanonicalFiniteProjector : Bool := true
  sourceTangentGeneratorEquationExplicit : Bool := true
  fixedReferenceCommutantDimensionExplicit : Bool := true
  minimizerMapPullbackDifferentiated : Bool := false
  HamiltonianParameterMetricReconstructed : Bool := false
  algebraSusceptibilitySingularityProved : Bool := false
  thermodynamicMQPTProved : Bool := false
  empiricalPhaseTransitionClaimCreated : Bool := false
deriving Repr, DecidableEq

def canonicalBoundary : Boundary := {}

theorem unitary_family_metric_formula_reconstructed :
    canonicalBoundary.unitaryFamilyMetricFormulaReconstructed = true := rfl

theorem uses_canonical_finite_projector :
    canonicalBoundary.usesCanonicalFiniteProjector = true := rfl

theorem minimizer_pullback_not_differentiated :
    canonicalBoundary.minimizerMapPullbackDifferentiated = false := rfl

theorem thermodynamic_mqpt_not_proved :
    canonicalBoundary.thermodynamicMQPTProved = false := rfl

/-- External scientific/source authority for the unitary-family metric. -/
def zanardiDallasAndreadakisMetricSourceReceipt : AttributionReceipt where
  role := .externalSourceClaim
  owner := "Paolo Zanardi; Emanuel Dallas; Faidon Andreadakis, Mereological Quantum Phase Transitions, Phys. Rev. A 113, 042201 (2026), DOI 10.1103/r193-5s7w; arXiv:2510.06389"
  claim := "For a family A_theta = Ad(U_theta)(A_0), gives ds_Theta^2 = kappa^2 ||Q_theta(dK)||_2^2 with kappa = 2/(dim A'_0) and dK = -i dU_theta U_theta^dagger; subsequently pulls the metric through the scrambling minimizer map and interprets thermodynamic-limit singularities as m-QPTs."

/-- DASHI finite reconstruction. -/
def dashiUnitaryMetric2026Receipt : AttributionReceipt where
  role := .newDASHITheorem
  owner := "DASHI Lean"
  claim := "Reconstructs the finite unitary-family Eq. (8) metric element over an explicit same-object tangent receipt and the canonical finite Hilbert--Schmidt projector. It does not differentiate the minimizer map, construct the Hamiltonian-parameter pullback metric, prove susceptibility singularities, take a thermodynamic limit, or assert an empirical phase transition."

end GTPSUnitaryMetric2026
end QuantumMereology
