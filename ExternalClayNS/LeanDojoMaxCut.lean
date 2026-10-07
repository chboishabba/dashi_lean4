import LeanDojoForceTransport
import LeanDojoSolutionTransport

/-!
# Literal LeanDojo Navier--Stokes max-cut

This file names the first genuinely unpaid same-object transport after the
carrier, initial-data, smoothness, periodicity, and boundary-extension work.
It deliberately does not introduce a replacement Navier--Stokes statement.

The next whole-space edge is exactly this theorem family:

  comparator ForceConditionDecay f
    -> LeanDojo SmoothRapidDecayForce (comparatorForceToLean f).

Once this is paid, the remaining solution-side work is the equation/divergence
and finite-energy pullback already isolated in `LeanDojoSolutionTransport`.
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

#check ComparatorForceDecayTransportR3
#check ComparatorForceDecayTransportPeriodic

end DASHILiteralClayNS
