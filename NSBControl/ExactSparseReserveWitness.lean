import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt

/-!
# Exact sparse signed-reserve negative control (R815 / R823)

Independent SymPy evaluator:
`scripts/check_ns_r823_exact_sparse_reserve_witness.py`
on Agda PR #1039 evaluates a divergence-free reality-paired radius-one
Fourier snapshot. Its computed conventions are

  global R230 commutator coherent work = -142 - 59*sqrt(2)/2,
  R723 combined = 12*commutator,
  R744 critical production = 0,
  R744 critical dissipation = 108,
  nu=margin=1.

This file proves only the **exact real-number sign** and a contradiction
for a purported nonnegative *matching* instantaneous R815 physical rate.

It deliberately does NOT prove:
* the SymPy evaluator is the Agda rational-real-field physical packet;
* that R408 is inhabited by this `Real`-radical snapshot;
* a physical finite Galerkin trajectory through the snapshot;
* short-time integral negativity;
* failure of W1 or Fefferman's Navier--Stokes alternatives.

The Agda rational helical scalar carrier needs special care: true
projectors at |k|=sqrt(2) cannot be represented by a rational mode norm.
Promotion requires a genuine real/algebraic-field same-object adapter.
-/

namespace NSBControl
namespace ExactSparseReserveWitness

def commutatorWork : ℝ := -142 - (59 / 2 : ℝ) * Real.sqrt 2

def combinedResidue : ℝ := 12 * commutatorWork

def criticalProduction : ℝ := 0

def criticalDissipation : ℝ := 108

def canonicalSignedRate : ℝ :=
  6 * (combinedResidue - criticalProduction + criticalDissipation)

theorem exactSignedRate :
    canonicalSignedRate = -9576 - 2124 * Real.sqrt 2 := by
  unfold canonicalSignedRate combinedResidue commutatorWork
    criticalProduction criticalDissipation
  ring

theorem canonicalSignedRate_negative : canonicalSignedRate < 0 := by
  rw [exactSignedRate]
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  nlinarith

/-- This is an *obstruction to reifying the universal pointwise estimate*,
not an assertion that the R408/Agda same-object field reification exists. -/
theorem noNonnegativeRateOfExactMatching
    (actualRate : ℝ)
    (actualEqualsWitness : actualRate = canonicalSignedRate)
    (nonnegative : 0 ≤ actualRate) : False := by
  rw [actualEqualsWitness] at nonnegative
  exact (not_le_of_gt canonicalSignedRate_negative) nonnegative

end ExactSparseReserveWitness
end NSBControl
