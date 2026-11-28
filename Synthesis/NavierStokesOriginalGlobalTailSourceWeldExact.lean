import Synthesis.NavierStokesOriginalGlobalEnergyPaymentExact
import Synthesis.NavierStokesOriginalMeanAndTailExact

/-!
The same fixed-cutoff global finite trajectory now consumes the
ORIGINAL unweighted high-mode tail theorem, not an invented spectral
tail functional. This controls each instantaneous tail by its genuine
physical dissipation. It does not give cutoff-uniform critical H1 or
unrestricted 3D continuum regularity.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open Set MeasureTheory
noncomputable section

/-- On the actual global original Galerkin solution, both the
energy/dissipation budget and the high-frequency modal tail
inequality hold for ALL physical nonnegative times.

The tail is the original outputModes/realHermitian object, with
the actual zero-extension and original Fourier massSq. -/
theorem actual_global_finite_tail_and_energy_payment
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
          ≤ stateEnergy x₀) ∧
      (∀ t : ℝ, ∀ R : ℝ, 0 < R →
        R^2 * (∑ k ∈ (outputModes N).filter
          (fun k => R^2 ≤ massSq (embedMode k)),
          realHermitian (zeroExtend (X t) (embedMode k))
            (zeroExtend (X t) (embedMode k))) ≤
        periodicDissipation N (fun k s => zeroExtend (X s) k) t) := by
  obtain ⟨a,ha,X,hzero,hode,hreal,htrans,hbudget⟩ :=
    actual_global_finite_energy_and_dissipation_payment N ν hν x₀ hr ht
  refine ⟨a,ha,X,hzero,hode,hreal,htrans,hbudget,?_⟩
  intro t R hR
  exact periodic_tail_energy_le N
    (fun k s => zeroExtend (X s) k) t R hR

end
end DASHI.NavierStokes.PhysicalMixed
