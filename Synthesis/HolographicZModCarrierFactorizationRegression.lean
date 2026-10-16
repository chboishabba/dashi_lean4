import Synthesis.HolographicZModCarrierFactorization

namespace Synthesis.HolographicZModCarrierFactorizationRegression

open Synthesis.HolographicZModCarrierFactorization

example (k r : ℕ) : Function.Bijective (zmodBinaryFactorEquiv k r) :=
  (zmodBinaryFactorEquiv k r).bijective

example (k r : ℕ) (x : ZMod (2 ^ (k + r))) :
    (zmodBinaryFactorEquiv k r).symm (zmodBinaryFactorEquiv k r x) = x := by
  simp

example : upstreamZModCarrierFactorizationOwned = true := rfl
example : depthKSubtreeSemanticIdentificationStillRequired = true := rfl
example : minimalCutSemanticIdentificationStillRequired = true := rfl

end Synthesis.HolographicZModCarrierFactorizationRegression
