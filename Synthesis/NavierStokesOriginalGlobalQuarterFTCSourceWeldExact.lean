import Synthesis.NavierStokesOriginalGlobalTailSourceWeldExact
import Synthesis.NavierStokesActualFractionalSignedFTCExact

/-!
R568/N2e: one actual physical finite Galerkin trajectory owns all
three currencies: original energy/dissipation, original output-tail
weight and the signed quarter-derivative energy-square FTC.

The signed transfer has NOT been bounded above independently. The
mathematical P0 deficit is exactly a CUTOFF-UNIFORM nonlinear transfer
estimate, not a finite-flow/FTC/reality reconstruction.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open Set MeasureTheory
noncomputable section

/-- Original global finite solution with its SAME-trajectory signed
quarter fractional transfer identity for every nonnegative time.

No fresh differentiability, continuity, sign, scalar reconstruction
or arbitrary trajectory is inserted into the endpoint theorem. -/
theorem actual_global_original_quarter_signed_energy_FTC
    (N : ℕ) (ν : ℝ) (hν : 0 ≤ ν)
    (x₀ : FiniteState N)
    (hr : reflectState x₀ = x₀)
    (ht : ∀ k, outputDot k (zeroExtend x₀ k) = 0) :
    ∃ a < 0, ∃ X : ℝ → FiniteState N,
      X 0 = x₀ ∧ SolvesOn (finiteForce N ν) X (Ioi a) ∧
      (∀ t ≥ 0, reflectState (X t) = X t) ∧
      (∀ t ≥ 0, ∀ k,
        outputDot k (zeroExtend (X t) k) = 0) ∧
      (∀ T : ℝ, 0 ≤ T →
        let U := fun k t => zeroExtend (X t) k
        fractionalEnergy N quarterWeight U T^2 -
          fractionalEnergy N quarterWeight U 0^2 =
        2 * (∫ t in 0..T,
          fractionalEnergy N quarterWeight U t *
          fractionalTransfer N quarterWeight U t) -
        4 * ν * (∫ t in 0..T,
          fractionalEnergy N quarterWeight U t *
          fractionalDissipation N quarterWeight U t)) := by
  obtain ⟨a, ha, X, hzero, hode, hreal, htrans, _henergy⟩ :=
    actual_global_finite_tail_and_energy_payment N ν hν x₀ hr ht
  refine ⟨a, ha, X, hzero, hode, hreal, htrans, ?_⟩
  intro T hT
  exact actual_quarter_signed_FTC N ν T a hT ha X hode

end
end DASHI.NavierStokes.PhysicalMixed
