import Synthesis.NavierStokesOriginalSameFlowTailL4CompactnessExact
import Synthesis.NavierStokesOriginalIntegratedHighShellPaymentExact

/-!
Section35: one ORIGINAL global Galerkin physical flow with BOTH
space-time compactness payments (quarter-energy fourth moment,
high Fourier shells at R^-2).

The previous original same-flow construction already pays the
nonlinear ODE, reality, transversality, initial-energy ceiling and
integrated dissipation. The existing R^-2 lemma pays exactly the
original Fourier shell after source integrability, not an independent
solution. Shell integrability is *explicitly retained* as a premise;
it may be discharged in a separate continuous finite Fourier sum
lemma but is not silently assumed here.

No cutoff-uniform signed nonlinear transport, physical continuum
regularity or all-Clay closure is claimed.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open Set MeasureTheory
open scoped BigOperators
noncomputable section

/-- The *same* original global X_N pays finite energy, dissipation,
pointwise arbitrary-shell budget, quarter L4 time and time-integrated
high-frequency tail at the optimal R^-2 energy scale.
The high-shell interval-integrability remains explicit. -/
theorem actual_original_same_flow_both_spacetime_payments
    (N : ℕ) (ν : ℝ) (hν : 0 < ν)
    (x₀ : FiniteState N)
    (hr : reflectState x₀ = x₀)
    (ht : ∀ k, outputDot k (zeroExtend x₀ k) = 0) :
    ∃ a < 0, ∃ X : ℝ → FiniteState N,
      X 0 = x₀ ∧
      SolvesOn (finiteForce N ν) X (Ioi a) ∧
      (∀ t ≥ 0, reflectState (X t) = X t) ∧
      (∀ t ≥ 0, ∀ k,
        outputDot k (zeroExtend (X t) k) = 0) ∧
      (∀ t ≥ 0,
        stateEnergy (X t) ≤ stateEnergy x₀ ∧
        2 * ν * (∫ s in 0..t,
          periodicDissipation N
            (fun k s => zeroExtend (X s) k) s) ≤
              stateEnergy x₀) ∧
      (∀ t R : ℝ, 0 < R →
        R^2 * originalPhysicalHighShell N X R t ≤
        periodicDissipation N
          (fun k s => zeroExtend (X s) k) t) ∧
      (∀ T : ℝ, 0 ≤ T →
        2 * ν * (∫ t in 0..T,
          (fractionalEnergy N quarterWeight
            (fun k s => zeroExtend (X s) k) t)^4)
          ≤ (stateEnergy x₀)^4) ∧
      (∀ T R : ℝ, 0 ≤ T → 0 < R →
        IntervalIntegrable
          (fun t => originalPhysicalHighShell N X R t)
            volume 0 T →
        (∫ t in 0..T, originalPhysicalHighShell N X R t)
          ≤ stateEnergy x₀ / (2 * ν * R^2)) := by
  obtain ⟨a,ha,X,hzero,hODE,hreal,htrans,hbudget,htail,hquarter⟩ :=
    actual_original_one_flow_tail_energy_and_quarter_L4
      N ν hν x₀ hr ht
  refine ⟨a,ha,X,hzero,hODE,hreal,htrans,hbudget,?_,hquarter,?_⟩
  · intro t R hR
    exact htail t R hR
  · intro T R hT hR hShell
    obtain ⟨_,hD⟩ :=
      original_actual_finite_quarter_and_dissipation_integrable
        N ν T a hT ha X hODE
    exact original_physical_integrated_shell_R_inverse_sq
      N ν (stateEnergy x₀) T R X hT hR hν
      hShell hD (hbudget T hT).2

end
end DASHI.NavierStokes.PhysicalMixed
