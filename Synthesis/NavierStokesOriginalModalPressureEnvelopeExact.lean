import Synthesis.NavierStokesOriginalEnergyProductSummabilityExact
import Synthesis.NavierStokesOriginalJointModalWitnessExact

/-! The original joint modal witness provides the pressure input
envelope on the same selected lattice velocity at every physical time.
Pressure-cell output bounds and physical-space reconstruction remain
separate; this does not claim a Leray-Hopf or regularity endpoint. -/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open Set Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section

/-- On the selected nonlinear modal-limit carrier, the original energy
budget pays the complete fixed-output input-product convolution, all
output frequencies and times in the original closed interval. -/
theorem original_modal_pressure_envelope_from_energy
    (B T : ℝ) (V : Lattice → ℝ → CVec3)
    (hE : ∀ t ∈ Icc (0:ℝ) T, ∀ S : Finset Lattice,
      ∑ p ∈ S, phaseMass (V p t) ≤ B) :
    ∀ t ∈ Icc (0:ℝ) T, ∀ k : Lattice,
      Summable (fun p : Lattice =>
        amplitude (V p t) * amplitude (V (k-p) t)) ∧
      (∑' p : Lattice,
        amplitude (V p t) * amplitude (V (k-p) t)) ≤ B := by
  intro t ht k
  exact original_energy_product_summable k (fun p => V p t) B (hE t ht)

end
end DASHI.NavierStokes.PhysicalMixed
