import Synthesis.NavierStokesOriginalQuarterSignedTransferInverseCutExact

/-!
N2e original finite-Galerkin family: isolate the exact uniform critical
continuation payment. No arbitrary synthetic Sobolev carrier is used.
The missing mathematics is exactly the cutoff-uniform signed integral
hypothesis, not a copy of the already-paid original finite flow/FTC.

This file does NOT claim the hypothesis follows from energy, viscosity
or the quarter-energy derivative identity.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open Set MeasureTheory
noncomputable section

/-- Given actual global Galerkin trajectories on every original output
cutoff, a uniform ORIGINAL signed-transfer budget and initial
quarter-energy budget yield a cutoff-independent physical
quarter-energy ceiling, with the original nonnegative viscous
integral retained as an explicit original-field condition. -/
theorem original_all_cutoffs_quarter_ceiling_of_uniform_signed_budget
    (ν E₀ B : ℝ)
    (X : (N : ℕ) → ℝ → FiniteState N)
    (a : ℕ → ℝ)
    (ha : ∀ N, a N < 0)
    (hODE : ∀ N,
      DASHI.NavierStokes.RealContinuation.SolvesOn
        (finiteForce N ν) (X N) (Ioi (a N)))
    (hinit : ∀ N,
      fractionalEnergy N quarterWeight
        (fun k s => zeroExtend (X N s) k) 0 ^ 2 ≤ E₀)
    (hsigned : ∀ N T : ℝ, 0 ≤ T →
      (∫ t in 0..T,
        fractionalEnergy N quarterWeight
          (fun k s => zeroExtend (X N s) k) t *
        fractionalTransfer N quarterWeight
          (fun k s => zeroExtend (X N s) k) t) ≤ B)
    (hdiss : ∀ N (T : ℝ), 0 ≤ T →
      0 ≤ 4 * ν * (∫ t in 0..T,
        fractionalEnergy N quarterWeight
          (fun k s => zeroExtend (X N s) k) t *
        fractionalDissipation N quarterWeight
          (fun k s => zeroExtend (X N s) k) t)) :
    ∀ N (T : ℝ), 0 ≤ T →
      fractionalEnergy N quarterWeight
        (fun k s => zeroExtend (X N s) k) T ^ 2 ≤ E₀ + 2*B := by
  intro N T hT
  have h := actual_original_quarter_energy_ceiling_of_signed_budget
    N ν T (a N) B hT (ha N) (X N) (hODE N)
    (hsigned N T hT) (hdiss N T hT)
  exact h.trans (by linarith [hinit N])

end
end DASHI.NavierStokes.PhysicalMixed
