import Mathlib
import Synthesis.JacobsonClausiusNullAlgebra

namespace Synthesis.JacobsonRaychaudhuriEquilibrium

open Synthesis.JacobsonClausiusNullAlgebra

/-- Null Raychaudhuri right-hand side in 3+1 dimensions, written only at the
scalar-contraction level needed by the Jacobson horizon argument.

`shearSq` denotes sigma_ab sigma^ab and `twistSq` denotes omega_ab omega^ab.
The physical continuum congruence theorem identifying these scalars with a
specific null congruence is a separate payment. -/
def nullRaychaudhuriRHS
    (theta shearSq twistSq Rkk : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * theta^2 - shearSq + twistSq - Rkk

/-- Local-equilibrium specialization used in Jacobson's construction.
At the selected horizon point, theta = 0, shear = 0, and hypersurface
orthogonality gives twist = 0, so d theta / d lambda = -R_kk. -/
theorem nullRaychaudhuri_at_local_equilibrium (Rkk : ℝ) :
    nullRaychaudhuriRHS 0 0 0 Rkk = -Rkk := by
  simp [nullRaychaudhuriRHS]

/-- First-order expansion coefficient after factoring out the affine parameter
lambda from theta(lambda) = -lambda R_kk + higher-order terms. -/
def linearizedExpansionCoefficient (Rkk : ℝ) : ℝ := -Rkk

/-- The corresponding area-variation coefficient after also factoring out the
common horizon area element.  This is exactly the coefficient consumed by the
Clausius null-algebra module. -/
def factoredLinearizedAreaVariation (Rkk : ℝ) : ℝ :=
  linearizedExpansionCoefficient Rkk

/-- Same-object scalar weld between the local-equilibrium Raychaudhuri
linearization and the factored area-variation convention already used by the
Clausius compiler. -/
theorem factoredLinearizedAreaVariation_eq_clausius (Rkk : ℝ) :
    factoredLinearizedAreaVariation Rkk = areaVariationIntegrand Rkk := by
  rfl

/-- The scalar equilibrium/linearization algebra is paid here; this does not
prove the continuum null-congruence equation, hypersurface orthogonality,
vanishing initial shear/expansion, or control of higher-order terms on a
physical local causal horizon. -/
def equilibriumRaychaudhuriAlgebraOwned : Bool := true

def physicalNullCongruenceEquationStillRequired : Bool := true

def localEquilibriumIdentificationStillRequired : Bool := true

def hypersurfaceOrthogonalityStillRequired : Bool := true

def higherOrderControlStillRequired : Bool := true

def sameCarrierRicciIdentificationStillRequired : Bool := true

end Synthesis.JacobsonRaychaudhuriEquilibrium
