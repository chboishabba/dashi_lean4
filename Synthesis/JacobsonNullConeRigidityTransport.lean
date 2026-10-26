import Synthesis.JacobsonNullConeRigidity

namespace Synthesis.JacobsonNullConeRigidityTransport

open Synthesis.JacobsonNullConeRigidity

/-- Data needed to transport flat Minkowski null-cone rigidity to another
same-object carrier.  A physical application must supply the frame/tetrad and
prove that both the quadratic form and tensor contraction are preserved. -/
structure LorentzFrameTransport (V Tensor : Type*) where
  vectorEquiv : V ≃ Vec4
  tensorEquiv : Tensor ≃ SymTensor4
  quad : V → ℝ
  contraction : Tensor → V → ℝ
  metricMultipleV : ℝ → Tensor
  quad_compat : ∀ v : V,
    minkowskiQuad (vectorEquiv v) = quad v
  contraction_compat : ∀ (T : Tensor) (v : V),
    contract (tensorEquiv T) (vectorEquiv v) = contraction T v
  metric_compat : ∀ λ : ℝ,
    tensorEquiv (metricMultipleV λ) = metricMultiple λ

/-- Exact transport compiler.  Once a Lorentz-frame equivalence and its
same-object compatibility laws are supplied, the concrete flat 3+1 theorem
immediately yields null-cone rigidity on the transported carrier. -/
theorem rigidityTransportedThroughFrame
    {V Tensor : Type*}
    (F : LorentzFrameTransport V Tensor)
    (T : Tensor)
    (h : ∀ v : V, F.quad v = 0 → F.contraction T v = 0) :
    ∃ λ : ℝ, T = F.metricMultipleV λ := by
  have hflat : ∀ u : Vec4,
      minkowskiQuad u = 0 → contract (F.tensorEquiv T) u = 0 := by
    intro u hu
    let v : V := F.vectorEquiv.symm u
    have hvq : F.quad v = 0 := by
      calc
        F.quad v = minkowskiQuad (F.vectorEquiv v) := (F.quad_compat v).symm
        _ = minkowskiQuad u := by simp [v]
        _ = 0 := hu
    have hv := h v hvq
    have hcompat := F.contraction_compat T v
    calc
      contract (F.tensorEquiv T) u =
          contract (F.tensorEquiv T) (F.vectorEquiv v) := by simp [v]
      _ = F.contraction T v := hcompat
      _ = 0 := hv
  rcases nullConeRigidity (F.tensorEquiv T) hflat with ⟨λ, hλ⟩
  refine ⟨λ, F.tensorEquiv.injective ?_⟩
  calc
    F.tensorEquiv T = metricMultiple λ := hλ
    _ = F.tensorEquiv (F.metricMultipleV λ) := (F.metric_compat λ).symm

/-- The algebraic theorem and its frame-transport logic are now separated from
constructing the physical frame itself. -/
def frameTransportCompilerOwned : Bool := true

def physicalFrameConstructionStillRequired : Bool := true

def frameSmoothnessOrGlobalAssemblyStillRequired : Bool := true

def stressEnergySameObjectStillRequired : Bool := true

end Synthesis.JacobsonNullConeRigidityTransport
