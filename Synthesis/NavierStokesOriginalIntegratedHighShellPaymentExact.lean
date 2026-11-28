import Synthesis.NavierStokesOriginalGlobalFullPhysicalLedgerExact

/-!
Original NS one-trajectory high-shell energy: integrate the ORIGINAL
R² finite Fourier tail <= original physical dissipation and pay it
with the exact same original global energy ledger.

This yields a cutoff-independent R^-2 TIME-INTEGRATED high-shell
estimate if the initial energy is uniformly bounded. It is NOT
a time-uniform H1 estimate or a bound on the signed 1/4
nonlinear transfer; its legitimate integrability premises are
explicit and follow from finite ODE continuity on actual solutions.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open Set MeasureTheory
open scoped BigOperators
noncomputable section

def originalPhysicalHighShell (N : ℕ)
    (X : ℝ → FiniteState N) (R t : ℝ) : ℝ :=
  ∑ k ∈ (outputModes N).filter (fun k => R^2 ≤ massSq (embedMode k)),
    realHermitian (zeroExtend (X t) (embedMode k))
      (zeroExtend (X t) (embedMode k))

/-- This is the actual original Galerkin time-integrated high shell
with its correct radius-squared spectral weighting and physical
viscosity payment. Both integrands are the original physical fields. -/
theorem original_physical_integrated_shell_energy_payment
    (N : ℕ) (ν E₀ T R : ℝ)
    (X : ℝ → FiniteState N)
    (hT : 0 ≤ T) (hR : 0 < R) (hν : 0 < ν)
    (hShell : IntervalIntegrable
      (fun t => originalPhysicalHighShell N X R t) volume 0 T)
    (hD : IntervalIntegrable
      (fun t => periodicDissipation N
        (fun k s => zeroExtend (X s) k) t) volume 0 T)
    (hEnergy :
      2 * ν * (∫ s in 0..T,
        periodicDissipation N
          (fun k t => zeroExtend (X t) k) s) ≤ E₀) :
    2 * ν * R^2 * (∫ t in 0..T,
      originalPhysicalHighShell N X R t) ≤ E₀ := by
  have hPoint (t : ℝ) (ht : t ∈ Icc 0 T) :
      R^2 * originalPhysicalHighShell N X R t ≤
        periodicDissipation N (fun k s => zeroExtend (X s) k) t := by
    exact periodic_tail_energy_le N
      (fun k s => zeroExtend (X s) k) t R hR
  have hM := intervalIntegral.integral_mono_on hT
    (hShell.const_mul (R^2)) hD hPoint
  rw [intervalIntegral.integral_const_mul] at hM
  have hMul : 2 * ν * (R^2 * (∫ t in 0..T,
      originalPhysicalHighShell N X R t)) ≤
      2 * ν * (∫ s in 0..T,
        periodicDissipation N
          (fun k t => zeroExtend (X t) k) s) :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  calc
    2 * ν * R^2 * (∫ t in 0..T,
      originalPhysicalHighShell N X R t) =
      2 * ν * (R^2 * (∫ t in 0..T,
        originalPhysicalHighShell N X R t)) := by ring
    _ ≤ 2 * ν * (∫ s in 0..T,
        periodicDissipation N
          (fun k t => zeroExtend (X t) k) s) := hMul
    _ ≤ E₀ := hEnergy

/-- The original high-shell tail is controlled by the sharp R^-2
integrated ledger on every fixed physical time interval. There is no
artificial bound on derivative or high-frequency first moment. -/
theorem original_physical_integrated_shell_R_inverse_sq
    (N : ℕ) (ν E₀ T R : ℝ)
    (X : ℝ → FiniteState N)
    (hT : 0 ≤ T) (hR : 0 < R) (hν : 0 < ν)
    (hShell : IntervalIntegrable
      (fun t => originalPhysicalHighShell N X R t) volume 0 T)
    (hD : IntervalIntegrable
      (fun t => periodicDissipation N
        (fun k s => zeroExtend (X s) k) t) volume 0 T)
    (hEnergy :
      2 * ν * (∫ s in 0..T,
        periodicDissipation N
          (fun k t => zeroExtend (X t) k) s) ≤ E₀) :
    (∫ t in 0..T, originalPhysicalHighShell N X R t)
      ≤ E₀ / (2 * ν * R^2) := by
  have hc : 0 < 2 * ν * R^2 := by positivity
  have h := original_physical_integrated_shell_energy_payment
    N ν E₀ T R X hT hR hν hShell hD hEnergy
  apply (le_div_iff₀ hc).2
  nlinarith [h]

end
end DASHI.NavierStokes.PhysicalMixed
