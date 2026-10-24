import Synthesis.JacobsonNullConeRigidityTransport

namespace Synthesis.JacobsonNullConeRigidityTransportRegression

open Synthesis.JacobsonNullConeRigidity
open Synthesis.JacobsonNullConeRigidityTransport

example {V Tensor : Type*}
    (F : LorentzFrameTransport V Tensor)
    (T : Tensor)
    (h : ∀ v : V, F.quad v = 0 → F.contraction T v = 0) :
    ∃ λ : ℝ, T = F.metricMultipleV λ :=
  rigidityTransportedThroughFrame F T h

example : frameTransportCompilerOwned = true := rfl
example : physicalFrameConstructionStillRequired = true := rfl

end Synthesis.JacobsonNullConeRigidityTransportRegression
