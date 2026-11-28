import Synthesis.NavierStokesOriginalGlobalQuarterFTCSourceWeldExact

/-!
N2e original-source reverse solve.  The exact signed quarter-energy-square
FTC already exists for the original global Galerkin flow.  Consequently
the endpoint bound and the signed-transfer bound are EXACTLY equivalent,
not merely a proposed energy estimate.  This weld exposes the one
unpaid scalar functional on the SAME physical trajectory.  No
cutoff-uniform control is assumed or claimed.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open Set MeasureTheory
noncomputable section

/-- Original N2e reverse solve: on the same actual finite physical
trajectory, bounding the signed nonlinear transfer integral by B is
equivalent to paying a precise squared quarter-energy + viscous bill.

This is an iff; it is NOT an upper bound on the signed transfer.
No derivative, input pressure or energy identity is reconstructed. -/
theorem actual_original_quarter_transfer_upper_iff_paid_energy
    (N : ℕ) (ν T a B : ℝ)
    (hT : 0 ≤ T) (ha : a < 0)
    (X : ℝ → FiniteState N)
    (hODE : DASHI.NavierStokes.RealContinuation.SolvesOn
      (finiteForce N ν) X (Ioi a)) :
    let U := fun k t => zeroExtend (X t) k
    (∫ t in 0..T,
      fractionalEnergy N quarterWeight U t *
      fractionalTransfer N quarterWeight U t) ≤ B ↔
    fractionalEnergy N quarterWeight U T^2 +
      4 * ν * (∫ t in 0..T,
        fractionalEnergy N quarterWeight U t *
        fractionalDissipation N quarterWeight U t) ≤
      fractionalEnergy N quarterWeight U 0^2 + 2*B := by
  dsimp
  have hFTC := actual_quarter_signed_FTC N ν T a hT ha X hODE
  constructor <;> intro h <;> linarith

/-- Forward use after paying the actual nonlinear source.  The
viscous term has not been discarded: its nonnegativity is an
explicit original-field obligation, rather than an assumption that
the nonlinear transfer itself is nonpositive. -/
theorem actual_original_quarter_energy_ceiling_of_signed_budget
    (N : ℕ) (ν T a B : ℝ)
    (hT : 0 ≤ T) (ha : a < 0)
    (X : ℝ → FiniteState N)
    (hODE : DASHI.NavierStokes.RealContinuation.SolvesOn
      (finiteForce N ν) X (Ioi a))
    (htransfer :
      (∫ t in 0..T,
        fractionalEnergy N quarterWeight
          (fun k s => zeroExtend (X s) k) t *
        fractionalTransfer N quarterWeight
          (fun k s => zeroExtend (X s) k) t) ≤ B)
    (hdiss : 0 ≤
      4 * ν * (∫ t in 0..T,
        fractionalEnergy N quarterWeight
          (fun k s => zeroExtend (X s) k) t *
        fractionalDissipation N quarterWeight
          (fun k s => zeroExtend (X s) k) t)) :
    fractionalEnergy N quarterWeight
        (fun k s => zeroExtend (X s) k) T ^ 2 ≤
      fractionalEnergy N quarterWeight
        (fun k s => zeroExtend (X s) k) 0 ^ 2 + 2 * B := by
  have h := (actual_original_quarter_transfer_upper_iff_paid_energy
    N ν T a B hT ha X hODE).mp htransfer
  dsimp at h
  linarith

end
end DASHI.NavierStokes.PhysicalMixed
