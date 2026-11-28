import Synthesis.NavierStokesOriginalConvolutionSeriesExact
import Synthesis.NavierStokesPressureCellSeriesExact

namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open scoped BigOperators
noncomputable section

/-- The same energy budget controls the unprojected product envelope,
without using projected convection or dividing by output frequency. -/
theorem original_energy_product_summable (k : Lattice)
    (U : Lattice → CVec3) (B : ℝ)
    (hE : ∀ S : Finset Lattice, ∑ p ∈ S, phaseMass (U p) ≤ B) :
    Summable (fun p : Lattice => amplitude (U p) * amplitude (U (k-p))) ∧
    (∑' p : Lattice, amplitude (U p) * amplitude (U (k-p))) ≤ B := by
  classical
  have hinj : Function.Injective (fun p : Lattice => k-p) := by
    intro a b h
    exact sub_left_injective h
  have hn (p : Lattice) : 0 ≤ amplitude (U p) * amplitude (U (k-p)) :=
    mul_nonneg (amplitude_nonnegative _) (amplitude_nonnegative _)
  have hb (S : Finset Lattice) :
      (∑ p ∈ S, amplitude (U p) * amplitude (U (k-p))) ≤ B := by
    have ht : (∑ p ∈ S, phaseMass (U (k-p))) ≤ B := by
      rw [← Finset.sum_image hinj.injOn]
      exact hE _
    calc
      _ ≤ ∑ p ∈ S, (phaseMass (U p) + phaseMass (U (k-p))) / 2 := by
        apply Finset.sum_le_sum
        intro p _
        simpa using weighted_young_amplitudes (U p) (U (k-p)) 1 (by norm_num)
      _ ≤ B := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
        linarith [hE S, ht]
  exact ⟨summable_of_sum_le hn hb, Real.tsum_le_of_sum_le hn hb⟩

end
end DASHI.NavierStokes.PhysicalMixed
