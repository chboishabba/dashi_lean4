import Synthesis.HolographicContractEntropy
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Same-object maximally-entangled cut model for the RT seam

The upstream holographic source defines `k * log 2` at the cut level but does
not derive it from the reduced density matrix of its named boundary state.
This module closes the finite entropy theorem on a corrected same-object model:

* the cut carrier has dimension `2^k` on each side;
* the joint density kernel has coherent support on `|i,i><j,j|`, i.e. the
  standard maximally-entangled Schmidt density kernel;
* tracing out the second factor produces the uniform diagonal state with
  eigenvalue `2^{-k}`;
* the already-proved uniform spectral entropy therefore gives `k * log 2`.

This is a theorem about the corrected finite cut model.  It deliberately does
not identify the inspected upstream `ZMod (2^n)` subtree or its named state with
this carrier; those same-object maps remain separate obligations.
-/

namespace Synthesis.HolographicMaxEntangledCutRT

open scoped BigOperators
noncomputable section

/-- Dimension of either side of a depth-`k` binary cut. -/
def cutDimension (k : ℕ) : ℕ := 2 ^ k

/-- Schmidt weight of each of the `2^k` correlated basis labels. -/
def cutWeight (k : ℕ) : ℝ := ((2 : ℝ) ^ k)⁻¹

/-- The standard maximally-entangled Schmidt density kernel.

Its nonzero entries are precisely `|i,i><j,j|`, all with coefficient `2^{-k}`.
Unlike the diagonal maximally-mixed contract audited upstream, this kernel has
coherence between distinct correlated basis labels. -/
def maxEntangledSchmidtDensity
    (k : ℕ) :
    Matrix (Fin (cutDimension k) × Fin (cutDimension k))
      (Fin (cutDimension k) × Fin (cutDimension k)) ℝ :=
  fun x y =>
    if x.1 = x.2 ∧ y.1 = y.2 then cutWeight k else 0

/-- Partial trace over the second cut factor. -/
def reducedDensityA
    (k : ℕ) : Matrix (Fin (cutDimension k)) (Fin (cutDimension k)) ℝ :=
  fun i j =>
    ∑ b : Fin (cutDimension k),
      maxEntangledSchmidtDensity k (i , b) (j , b)

/-- The reduced density matrix is exactly uniform diagonal. -/
theorem reducedDensityA_eq_uniformDiagonal
    (k : ℕ) (i j : Fin (cutDimension k)) :
    reducedDensityA k i j = if i = j then cutWeight k else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp [reducedDensityA, maxEntangledSchmidtDensity]
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hib : i = b
    · subst b
      simp [maxEntangledSchmidtDensity, hij]
    · simp [maxEntangledSchmidtDensity, hib]

/-- The reduced spectrum therefore has `2^k` copies of `2^{-k}`. -/
def reducedVonNeumannEntropy (k : ℕ) : ℝ :=
  Synthesis.HolographicContractEntropy.uniformDiagonalVonNeumannEntropy k

/-- Entropy of the reduced state of the corrected maximally-entangled cut. -/
theorem reducedEntropy_eq_kLogTwo (k : ℕ) :
    reducedVonNeumannEntropy k = (k : ℝ) * Real.log 2 := by
  exact Synthesis.HolographicContractEntropy.fullContractVonNeumannEntropyIsNLogTwo k

/-- The geometric/cut-side entropy used by the discrete RT-shaped theorem. -/
def correctedCutEntropy (k : ℕ) : ℝ := (k : ℝ) * Real.log 2

/-- Same-object RT entropy equality for the corrected finite Schmidt cut model. -/
theorem correctedRTSameObjectEntropy (k : ℕ) :
    correctedCutEntropy k = reducedVonNeumannEntropy k := by
  simpa [correctedCutEntropy] using (reducedEntropy_eq_kLogTwo k).symm

/-- Upstream's named boundary state still has to be identified with a state
    whose reduced density matrix is the one constructed here. -/
def upstreamStateIdentificationStillRequired : Bool := true

/-- The selected tensor factor still has to be identified with the geometric
    minimal-cut/subtree carrier of the upstream network. -/
def minimalCutCarrierIdentificationStillRequired : Bool := true

end

end Synthesis.HolographicMaxEntangledCutRT
