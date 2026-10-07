import LeanDojoForceTransport
import LeanDojoMomentumTransport
import LeanDojoDivergenceTransport
import LeanDojoEnergyTransport

/-!
# Literal LeanDojo Navier--Stokes max-cut

This file names the first genuinely unpaid same-object transport after the
carrier, initial-data, smoothness, periodicity, boundary extension, momentum,
incompressibility, and whole-space energy work.

The next whole-space edge is exactly this theorem family:

  comparator ForceConditionDecay f
    -> LeanDojo SmoothRapidDecayForce (comparatorForceToLean f).

The solution-side identities needed for the contradiction are already paid:
`LeanDojoMomentumTransport` proves equation (1), `LeanDojoDivergenceTransport`
proves equation (2), `LeanDojoSolutionTransport` supplies smoothness/initial
values, and `LeanDojoEnergyTransport` transports condition (7).  Therefore the
force derivative word is the literal first unpaid representation edge; a
proposition-level C/D weld is strictly downstream packaging.
-/

noncomputable section

open ClaySpec
open NavierStokes
open NavierStokesOnR3

namespace DASHILiteralClayNS

/-- Exact first unpaid whole-space representation theorem.  The source already
proves the smoothness component in `comparatorDecayForce_smooth`; what remains
is the displayed mixed-coordinate derivative decay bound on the literal
LeanDojo spacetime carrier. -/
def ComparatorForceDecayTransportR3 : Prop :=
  ∀ {f : R3 → ℝ → R3},
    NavierStokes.Comparator.ForceConditionDecay f →
      NavierStokesOnR3.SmoothRapidDecayForce (comparatorForceToLean f)

/-- Periodic analogue.  Structural smoothness and integer periodicity are
already paid; the remaining quantitative coordinate-word decay is the only
new force-side coordinate here. -/
def ComparatorForceDecayTransportPeriodic : Prop :=
  ∀ {f : R3 → ℝ → R3},
    NavierStokes.Comparator.ForceConditionPeriodic f →
      NavierStokesPeriodic.PeriodicForceDecay (comparatorForceToLean f)

/-- Regression receipt: the whole-space max-cut really strengthens the already
proved smoothness transport rather than replacing it. -/
theorem comparatorForceDecayTransportR3_implies_smooth
    (h : ComparatorForceDecayTransportR3)
    {f : R3 → ℝ → R3}
    (hf : NavierStokes.Comparator.ForceConditionDecay f) :
    force_smooth_on_global_spacetime_domain (comparatorForceToLean f) := by
  exact (h hf).1

/- Paid solution-side coordinates kept beside the max-cut so future work does
not reopen them. -/
#check leanDojoMomentum_to_clayEquationOne
#check leanDojoIncompressible_to_clay
#check leanDojoFiniteEnergy_to_comparator
#check leanDojoSolution_structuralComparatorFields

#check ComparatorForceDecayTransportR3
#check ComparatorForceDecayTransportPeriodic

end DASHILiteralClayNS
