import Synthesis.NavierStokesOriginalGlobalTailSourceWeldExact
import Synthesis.NavierStokesActualFractionalSignedFTCExact

/-!
Original R30 + N2e + Fourier shell global same-source weld.

A SINGLE actual finite Galerkin flow now owns: physical reality,
transversality, total energy, integrated viscosity, arbitrary
high-frequency shell domination and the signed quarter
nonlinear-transfer FTC for every nonnegative time.
No choice of unrelated trajectories is made for separate
inequalities. The open uniform nonlinear transfer bound is not
injected into this theorem.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open Set MeasureTheory
noncomputable section

theorem actual_original_global_all_finite_energy_tail_signed_quarter
    (N : ℕ) (ν : ℝ) (hν : 0 ≤ ν)
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
            (fun k s => zeroExtend (X s) k) s)
          ≤ stateEnergy x₀) ∧
      (∀ t R : ℝ, 0 < R →
        R^2 * (∑ k ∈ (outputModes N).filter
          (fun k => R^2 ≤ massSq (embedMode k)),
          realHermitian (zeroExtend (X t) (embedMode k))
            (zeroExtend (X t) (embedMode k))) ≤
        periodicDissipation N
          (fun k s => zeroExtend (X s) k) t) ∧
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
  obtain ⟨a, ha, X, hzero, hode, hreal, htrans, henergy, htail⟩ :=
    actual_global_finite_tail_and_energy_payment N ν hν x₀ hr ht
  refine ⟨a, ha, X, hzero, hode, hreal, htrans, henergy, htail, ?_⟩
  intro T hT
  exact actual_quarter_signed_FTC N ν T a hT ha X hode

end
end DASHI.NavierStokes.PhysicalMixed
