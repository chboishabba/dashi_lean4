import Synthesis.NavierStokesOriginalEnergyProductSummabilityExact

/-!
Section 21i. The original raw-convection series, not just its Leray
projection, is absolutely summable at every fixed lattice output from
the original energy budget. This explicitly pays the raw term needed by
pressure_series_split, including k = 0.
-/
namespace DASHI.NavierStokes.EuclideanMidpoint
noncomputable section

/-- The exact raw cell has the same quadratic energy majorant as its
projected counterpart, without excluding the zero output mode. -/
theorem raw_cell_mass_bound (k : Vec3) (u v : CVec3) :
    phaseMass (rawConvection k u v) ≤
      massSq k * phaseMass u * phaseMass v := by
  rw [rawConvection_mass]
  exact mul_le_mul_of_nonneg_right (phaseDotSq_le k u)
    (phaseMass_nonneg v)

theorem raw_cell_amplitude_bound (k : Vec3) (u v : CVec3) :
    amplitude (rawConvection k u v) ≤
      Real.sqrt (massSq k) * amplitude u * amplitude v := by
  unfold amplitude
  have h := Real.sqrt_le_sqrt (raw_cell_mass_bound k u v)
  rw [Real.sqrt_mul
      (mul_nonneg (massSq_nonnegative k) (phaseMass_nonneg u)),
      Real.sqrt_mul (massSq_nonnegative k)] at h
  exact h

end
end DASHI.NavierStokes.EuclideanMidpoint

namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open scoped BigOperators
noncomputable section

/-- Absolute summability of every original raw nonlinear Fourier cell
from exactly the same finite-subset energy-budget hypothesis.
The pressure part is not asserted summable by this theorem. -/
theorem original_raw_convection_summable (k : Lattice)
    (U : Lattice → CVec3) (B : ℝ)
    (hE : ∀ S : Finset Lattice,
      ∑ p ∈ S, phaseMass (U p) ≤ B)
    (i : Fin 3) :
    Summable (fun p : Lattice =>
      ‖rawConvection (embedMode k) (U p) (U (k-p)) i‖) := by
  classical
  obtain ⟨hs, hB⟩ := original_energy_product_summable k U B hE
  let C : ℝ := Real.sqrt (massSq (embedMode k))
  have hc : 0 ≤ C := Real.sqrt_nonneg _
  have hb (S : Finset Lattice) :
      ∑ p ∈ S,
        ‖rawConvection (embedMode k) (U p) (U (k-p)) i‖ ≤ C * B := by
    calc
      _ ≤ ∑ p ∈ S, C * (amplitude (U p) * amplitude (U (k-p))) := by
        apply Finset.sum_le_sum
        intro p _
        calc
          ‖rawConvection (embedMode k) (U p) (U (k-p)) i‖ ≤
              amplitude (rawConvection (embedMode k) (U p) (U (k-p))) :=
            coord_norm_le_amplitude _ _
          _ ≤ C * (amplitude (U p) * amplitude (U (k-p))) := by
            simpa only [C, mul_assoc] using
              raw_cell_amplitude_bound (embedMode k) (U p) (U (k-p))
      _ = C * ∑ p ∈ S, amplitude (U p) * amplitude (U (k-p)) := by
        rw [Finset.mul_sum]
      _ ≤ C * B := by
        exact mul_le_mul_of_nonneg_left
          ((hs.sum_le_tsum S
            (fun p _ => mul_nonneg (amplitude_nonnegative _)
              (amplitude_nonnegative _))).trans hB) hc
  exact summable_of_sum_le
    (fun p => norm_nonneg (rawConvection (embedMode k)
      (U p) (U (k-p)) i)) hb

end
end DASHI.NavierStokes.PhysicalMixed
