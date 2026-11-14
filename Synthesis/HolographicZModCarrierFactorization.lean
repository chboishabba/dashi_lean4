import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic

namespace Synthesis.HolographicZModCarrierFactorization

/-- Exact binary-dimension arithmetic used by a depth split `n = k+r`. -/
theorem binaryPowFactor (k r : ℕ) :
    2 ^ (k + r) = 2 ^ k * 2 ^ r := by
  exact pow_add 2 k r

/-- Pure carrier factorisation of the upstream binary boundary index type.

For nonzero binary dimensions, Mathlib supplies

* `ZMod.finEquiv n : Fin n ≃+* ZMod n`, and
* `Equiv.finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n)`.

Composing those with `2^(k+r)=2^k*2^r` yields an explicit equivalence

  ZMod (2^(k+r)) ≃ Fin (2^k) × Fin (2^r).

This closes only the finite carrier/index factorisation.  It does **not** say
that the first factor is the particular depth-k subtree, tensor factor, reduced
state, or minimal cut intended by the inspected upstream holographic source. -/
noncomputable def zmodBinaryFactorEquiv (k r : ℕ) :
    ZMod (2 ^ (k + r)) ≃ (Fin (2 ^ k) × Fin (2 ^ r)) :=
  ((ZMod.ringEquivCongr (binaryPowFactor k r)).toEquiv).trans
    (((ZMod.finEquiv (2 ^ k * 2 ^ r)).symm.toEquiv).trans
      Equiv.finProdFinEquiv.symm)

/-- First coordinate of the explicit carrier factorisation. -/
noncomputable def subsystemCarrierIndex (k r : ℕ)
    (x : ZMod (2 ^ (k + r))) : Fin (2 ^ k) :=
  (zmodBinaryFactorEquiv k r x).1

/-- Complementary coordinate of the explicit carrier factorisation. -/
noncomputable def complementCarrierIndex (k r : ℕ)
    (x : ZMod (2 ^ (k + r))) : Fin (2 ^ r) :=
  (zmodBinaryFactorEquiv k r x).2

/-- The pair of factor indices reconstructs the original upstream carrier
exactly. -/
theorem factorRoundTrip (k r : ℕ) (x : ZMod (2 ^ (k + r))) :
    (zmodBinaryFactorEquiv k r).symm
      (subsystemCarrierIndex k r x, complementCarrierIndex k r x) = x := by
  simp [subsystemCarrierIndex, complementCarrierIndex]

/-- Conversely every product index is represented by exactly one upstream
`ZMod` carrier element. -/
theorem productRoundTrip (k r : ℕ)
    (x : Fin (2 ^ k) × Fin (2 ^ r)) :
    zmodBinaryFactorEquiv k r ((zmodBinaryFactorEquiv k r).symm x) = x := by
  simp

/-- Status boundary. -/
def upstreamZModCarrierFactorizationOwned : Bool := true

def carrierCardinalityOrBijectionNoLongerRequired : Bool := true

def depthKSubtreeSemanticIdentificationStillRequired : Bool := true

def reducedDensityMatrixSemanticIdentificationStillRequired : Bool := true

def minimalCutSemanticIdentificationStillRequired : Bool := true

def tensorNetworkStateIdentificationStillRequired : Bool := true

def physicalAdSCFTStillRequired : Bool := true

end Synthesis.HolographicZModCarrierFactorization
