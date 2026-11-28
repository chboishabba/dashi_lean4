import Synthesis.NavierStokesOriginalGlobalFullPhysicalLedgerExact
import Synthesis.NavierStokesOriginalQuarterL4TimeFromPhysicalLedgerExact

/-!
Section32: the ONE actual source Galerkin global solution carries BOTH
the original arbitrary Fourier high-shell energy/dissipation
payment and the subcritical time-integrated quarter-energy L4
bound. No independent existential trajectories, synthetic Sobolev
carrier, or assumed physical time-integrability.

This is a continuum compactness input, NOT a cutoff-uniform signed
nonlinear transfer estimate, NS regularity or Clay completion.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open Set MeasureTheory
open scoped BigOperators
noncomputable section

theorem actual_original_one_flow_tail_energy_and_quarter_L4
    (N : ℕ) (ν : ℝ) (hν : 0 < ν)
    (x₀ : FiniteState N)
    (hr : reflectState x₀ = x₀)
    (ht : ∀ k, outputDot k (zeroExtend x₀ k) = 0) :
    ∃ a < 0, ∃ X : ℝ → FiniteState N,
      X 0 = x₀ ∧
      SolvesOn (finiteForce N ν) X (Ioi a) ∧
      (∀ t ≥ 0, reflectState (X t) = X t) ∧
      (∀ t ≥ 0, ∀ k, outputDot k (zeroExtend (X t) k) = 0) ∧
      (∀ t ≥ 0,
        stateEnergy (X t) ≤ stateEnergy x₀ ∧
        2 * ν * (∫ s in 0..t,
          periodicDissipation N
            (fun k s => zeroExtend (X s) k) s) ≤ stateEnergy x₀) ∧
      (∀ t R : ℝ, 0 < R →
        R^2 * (∑ k ∈ (outputModes N).filter
          (fun k => R^2 ≤ massSq (embedMode k)),
          realHermitian (zeroExtend (X t) (embedMode k))
            (zeroExtend (X t) (embedMode k))) ≤
        periodicDissipation N
          (fun k s => zeroExtend (X s) k) t) ∧
      (∀ T : ℝ, 0 ≤ T →
        2 * ν * (∫ t in 0..T,
          (fractionalEnergy N quarterWeight
            (fun k s => zeroExtend (X s) k) t)^4)
          ≤ (stateEnergy x₀)^4) := by
  obtain ⟨a, ha, X, hzero, hode, hreal, htrans, hbudget, htail⟩ :=
    actual_global_finite_tail_and_energy_payment
      N ν hν.le x₀ hr ht
  refine ⟨a, ha, X, hzero, hode, hreal, htrans,
    hbudget, htail, ?_⟩
  intro T hT
  obtain ⟨hq, hd⟩ :=
    original_actual_finite_quarter_and_dissipation_integrable
      N ν T a hT ha X hode
  exact original_quarter_energy_L4_time_paid_by_physical_dissipation
    N ν (stateEnergy x₀) T X hT hν.le
    (stateEnergy_nonneg x₀)
    (fun t ht => (hbudget t ht).1)
    (hbudget T hT).2 hq hd

end
end DASHI.NavierStokes.PhysicalMixed
