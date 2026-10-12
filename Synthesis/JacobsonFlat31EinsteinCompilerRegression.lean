import Synthesis.JacobsonFlat31EinsteinCompiler

namespace Synthesis.JacobsonFlat31EinsteinCompilerRegression

open Synthesis.JacobsonNullConeRigidity
open Synthesis.JacobsonCouplingNormalization
open Synthesis.JacobsonClausiusNullAlgebra
open Synthesis.JacobsonFlat31EinsteinCompiler

example (ricci stress : SymTensor4) (ℏ κ G : ℝ)
    (hℏ : ℏ ≠ 0) (hκ : κ ≠ 0) (hG : G ≠ 0)
    (hC : ∀ v : Vec4, minkowskiQuad v = 0 →
      heatFluxIntegrand κ (contract stress v) =
        unruhTemperature ℏ κ *
          entropyVariationIntegrand (bekensteinHawkingAreaDensity ℏ G)
            (contract ricci v)) :
    ∃ phi : ℝ,
      tensorSubScaled ricci (8 * Real.pi * G) stress = metricMultiple phi :=
  flat31RicciStressMetricAmbiguity_of_clausius ricci stress ℏ κ G hℏ hκ hG hC

example : flat31JacobsonEinsteinCompilerOwned = true := rfl
example : continuumSameObjectAttachmentStillRequired = true := rfl

end Synthesis.JacobsonFlat31EinsteinCompilerRegression
