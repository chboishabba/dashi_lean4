import Synthesis.NavierStokesActualGlobalFiniteFlowExact

/-!
Original finite physical energy ledger exposed directly to the continuum
compactness consumers. The new conclusion is genuinely on the fixed-cutoff
global trajectory constructed in R30; the upper bound is independent of
the cutoff provided the initial energy is uniformly bounded.

This does NOT supply an H1, first-shell, or critical-norm estimate.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open Set MeasureTheory
noncomputable section

/-- The original global real/divergence-free finite Galerkin trajectory
has BOTH an energy ceiling and an integrated dissipation ceiling
throughout its actual forward time domain. -/
theorem actual_global_finite_energy_and_dissipation_payment
    (N : ℕ) (ν : ℝ) (hν : 0 ≤ ν)
    (x₀ : FiniteState N)
    (hr : reflectState x₀ = x₀)
    (ht : ∀ k, outputDot k (zeroExtend x₀ k) = 0) :
    ∃ a < 0, ∃ X : ℝ → FiniteState N,
      X 0 = x₀ ∧ SolvesOn (finiteForce N ν) X (Ioi a) ∧
      (∀ t ≥ 0, reflectState (X t) = X t) ∧
      (∀ t ≥ 0, ∀ k, outputDot k (zeroExtend (X t) k) = 0) ∧
      (∀ t ≥ 0,
        stateEnergy (X t) ≤ stateEnergy x₀ ∧
        2 * ν * (∫ s in 0..t,
          periodicDissipation N (fun k s => zeroExtend (X s) k) s)
          ≤ stateEnergy x₀) := by
  obtain ⟨a, ha, X, hX, hODE, hre, htr, hledger⟩ :=
    actual_global_forward_finite_flow N ν hν x₀ hr ht
  refine ⟨a, ha, X, hX, hODE, hre, htr, ?_⟩
  intro t ht
  have hE := hledger t ht
  have hI : 0 ≤ (∫ s in 0..t,
      periodicDissipation N (fun k s => zeroExtend (X s) k) s) :=
    intervalIntegral.integral_nonneg_of_forall ht
      (periodicDissipation_nonneg N
        (fun k s => zeroExtend (X s) k))
  have hEN := stateEnergy_nonneg (X t)
  constructor
  · nlinarith [mul_nonneg hν hI]
  · nlinarith

end
end DASHI.NavierStokes.PhysicalMixed
