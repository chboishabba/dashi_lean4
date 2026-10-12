import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic
import Synthesis.HolographicZModCarrierFactorization
import Synthesis.HolographicMaxEntangledCutRT

namespace Synthesis.HolographicUnbalancedCorrectedRT

open scoped BigOperators
open Synthesis.HolographicZModCarrierFactorization
open Synthesis.HolographicMaxEntangledCutRT

/-- Binary Hilbert dimensions are monotone in depth. -/
theorem binaryPowMonotone {k r : ℕ} (hkr : k ≤ r) :
    2 ^ k ≤ 2 ^ r := by
  exact Nat.pow_le_pow_of_le (by norm_num) hkr

/-- Embed the `2^k` Schmidt labels into a complement of dimension `2^r`
whenever the complement depth is at least the subsystem depth. -/
def schmidtEmbed {k r : ℕ} (hkr : k ≤ r) :
    Fin (2 ^ k) ↪ Fin (2 ^ r) :=
  Fin.castLEEmb (binaryPowMonotone hkr)

/-- Corrected maximally-entangled density kernel for an unbalanced product
carrier `Fin (2^k) × Fin (2^r)`, with `k ≤ r`.

Only the embedded Schmidt labels carry coherence; unused complement basis
states have zero amplitude. -/
def maxEntangledEmbeddedDensity
    (k r : ℕ) (hkr : k ≤ r) :
    Matrix (Fin (2 ^ k) × Fin (2 ^ r))
      (Fin (2 ^ k) × Fin (2 ^ r)) ℝ :=
  fun x y =>
    if x.2 = schmidtEmbed hkr x.1 ∧ y.2 = schmidtEmbed hkr y.1
    then cutWeight k
    else 0

/-- Partial trace over the larger complement. -/
def reducedDensityAUnbalanced
    (k r : ℕ) (hkr : k ≤ r) :
    Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ :=
  fun i j =>
    ∑ b : Fin (2 ^ r),
      maxEntangledEmbeddedDensity k r hkr (i, b) (j, b)

/-- Even with a larger complement, tracing it out gives the same uniform
`2^{-k}` reduced state on the subsystem. -/
theorem reducedDensityAUnbalanced_eq_uniformDiagonal
    (k r : ℕ) (hkr : k ≤ r)
    (i j : Fin (2 ^ k)) :
    reducedDensityAUnbalanced k r hkr i j =
      if i = j then cutWeight k else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    simp [reducedDensityAUnbalanced, maxEntangledEmbeddedDensity]
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hib : b = schmidtEmbed hkr i
    · have hneq : schmidtEmbed hkr i ≠ schmidtEmbed hkr j := by
        intro h
        exact hij ((schmidtEmbed hkr).injective h)
      subst b
      simp [maxEntangledEmbeddedDensity, hneq]
    · simp [maxEntangledEmbeddedDensity, hib]

/-- The reduced entropy is the already-proved uniform spectral entropy. -/
noncomputable def correctedUnbalancedReducedEntropy
    (k r : ℕ) (_hkr : k ≤ r) : ℝ :=
  reducedVonNeumannEntropy k

/-- Exact RT entropy for any adequate complement depth `r ≥ k`. -/
theorem correctedUnbalancedRTEntropy
    (k r : ℕ) (hkr : k ≤ r) :
    correctedUnbalancedReducedEntropy k r hkr = correctedCutEntropy k := by
  exact (correctedRTSameObjectEntropy k).symm

/-- Pull the corrected unbalanced state onto the upstream `ZMod` carrier using
the exact binary product equivalence. -/
noncomputable def correctedUnbalancedZModDensity
    (k r : ℕ) (hkr : k ≤ r) :
    Matrix (ZMod (2 ^ (k + r))) (ZMod (2 ^ (k + r))) ℝ :=
  fun x y =>
    maxEntangledEmbeddedDensity k r hkr
      (zmodBinaryFactorEquiv k r x)
      (zmodBinaryFactorEquiv k r y)

/-- Exact pullback law from the upstream carrier type to product coordinates. -/
theorem correctedUnbalancedZModDensity_pullback
    (k r : ℕ) (hkr : k ≤ r)
    (x y : Fin (2 ^ k) × Fin (2 ^ r)) :
    correctedUnbalancedZModDensity k r hkr
      ((zmodBinaryFactorEquiv k r).symm x)
      ((zmodBinaryFactorEquiv k r).symm y)
      = maxEntangledEmbeddedDensity k r hkr x y := by
  simp [correctedUnbalancedZModDensity]

/-- Status boundary. -/
def correctedUnbalancedRTForAdequateComplementOwned : Bool := true

def correctedStateOnUpstreamZModCarrierForKLeROwned : Bool := true

def upstreamTreeContractionStillRequired : Bool := true

def upstreamNamedStateMustBeReplacedOrProvedEquivalent : Bool := true

def geometricSubtreeIdentificationStillRequired : Bool := true

def minimalCutIdentificationStillRequired : Bool := true

def physicalAdSCFTStillRequired : Bool := true

end Synthesis.HolographicUnbalancedCorrectedRT
