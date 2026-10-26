import Mathlib
import Synthesis.JacobsonNullConeRigidity
import Synthesis.JacobsonCouplingNormalization
import Synthesis.JacobsonClausiusNullAlgebra

namespace Synthesis.JacobsonFlat31EinsteinCompiler

open Synthesis.JacobsonNullConeRigidity
open Synthesis.JacobsonCouplingNormalization
open Synthesis.JacobsonClausiusNullAlgebra

/-- Componentwise Ricci - C·stress defect on the same symmetric 3+1 tensor
carrier used by the null-cone rigidity theorem. -/
def tensorSubScaled (ricci : SymTensor4) (C : ℝ) (stress : SymTensor4) : SymTensor4 where
  tt := ricci.tt - C * stress.tt
  tx := ricci.tx - C * stress.tx
  ty := ricci.ty - C * stress.ty
  tz := ricci.tz - C * stress.tz
  xx := ricci.xx - C * stress.xx
  xy := ricci.xy - C * stress.xy
  xz := ricci.xz - C * stress.xz
  yy := ricci.yy - C * stress.yy
  yz := ricci.yz - C * stress.yz
  zz := ricci.zz - C * stress.zz

/-- Quadratic contraction respects the componentwise Ricci-minus-scaled-stress
construction. -/
theorem contract_tensorSubScaled
    (ricci stress : SymTensor4) (C : ℝ) (v : Vec4) :
    contract (tensorSubScaled ricci C stress) v
      = contract ricci v - C * contract stress v := by
  unfold tensorSubScaled contract
  ring

/-- Flat 3+1 same-object Jacobson compiler.

If the supplied physical/QFT/geometric premises are strong enough to make the
Clausius equality hold for every Minkowski-null direction on one Ricci tensor
and one stress tensor, then the already-proved scalar normalization yields
R_kk = 8πG T_kk for every null k.  Flat null-cone rigidity then upgrades that
same-object null relation to

  Ricci - 8πG·Stress = phi·η

for one scalar metric ambiguity phi.  The later Einstein-tensor/Bianchi module
is responsible for repackaging phi as the cosmological term and proving its
constancy. -/
theorem flat31RicciStressMetricAmbiguity_of_clausius
    (ricci stress : SymTensor4) (ℏ κ G : ℝ)
    (hℏ : ℏ ≠ 0) (hκ : κ ≠ 0) (hG : G ≠ 0)
    (hC : ∀ v : Vec4, minkowskiQuad v = 0 →
      heatFluxIntegrand κ (contract stress v) =
        unruhTemperature ℏ κ *
          entropyVariationIntegrand (bekensteinHawkingAreaDensity ℏ G)
            (contract ricci v)) :
    ∃ phi : ℝ,
      tensorSubScaled ricci (8 * Real.pi * G) stress = metricMultiple phi := by
  apply nullConeRigidity (tensorSubScaled ricci (8 * Real.pi * G) stress)
  intro v hv
  rw [contract_tensorSubScaled]
  have hnull := einsteinNullRelation_of_clausius_bekensteinHawking
    ℏ κ G (contract stress v) (contract ricci v) hℏ hκ hG (hC v hv)
  linarith

/-- Status boundary. -/
def flat31JacobsonEinsteinCompilerOwned : Bool := true

def continuumSameObjectAttachmentStillRequired : Bool := true

def physicalUnruhAreaRaychaudhuriPremisesStillRequired : Bool := true

def cosmologicalConstancyStillRequiresBianchiAttachment : Bool := true

end Synthesis.JacobsonFlat31EinsteinCompiler
