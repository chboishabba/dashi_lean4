import LeanDojoExactTerminal

/-!
# Literal LeanDojo Navier--Stokes max-cut

The representation max-cut is now paid.

The previously isolated force-decay propositions are retained as named receipts,
but `LeanDojoForceDecayQuantitative` supplies both terms and
`LeanDojoExactTerminal` composes the complete same-object transport into the
literal pinned LeanDojo Fefferman C and D propositions.

There is therefore no remaining Navier--Stokes mathematical or same-object edge
on this branch.  The only acceptance gate is external verification: elaborate
`dashiExactFeffermanC` / `dashiExactFeffermanD` against the pinned upstream
source and inspect their axiom sets.  Until that exact kernel run is recorded,
the cross-program board remains fail-closed rather than declaring GREEN.
-/

noncomputable section

open ClaySpec
open NavierStokes
open NavierStokesOnR3

namespace DASHILiteralClayNS

def ComparatorForceDecayTransportR3 : Prop :=
  ∀ {f : R3 → ℝ → R3},
    NavierStokes.Comparator.ForceConditionDecay f →
      NavierStokesOnR3.SmoothRapidDecayForce (comparatorForceToLean f)

def ComparatorForceDecayTransportPeriodic : Prop :=
  ∀ {f : R3 → ℝ → R3},
    NavierStokes.Comparator.ForceConditionPeriodic f →
      NavierStokesPeriodic.PeriodicForceDecay (comparatorForceToLean f)

/-- The former whole-space representation leaf is paid by the exact
quantitative full-jet transport. -/
theorem comparatorForceDecayTransportR3_paid :
    ComparatorForceDecayTransportR3 := by
  intro f h
  exact comparatorForceDecay_to_leanDojo h

/-- The periodic force-decay leaf is paid by the same full-jet transport. -/
theorem comparatorForceDecayTransportPeriodic_paid :
    ComparatorForceDecayTransportPeriodic := by
  intro f h
  exact comparatorPeriodicForceDecay_to_leanDojo h

/-- Regression receipt: the paid whole-space transport still exposes the
previously proved smoothness coordinate. -/
theorem comparatorForceDecayTransportR3_implies_smooth
    (h : ComparatorForceDecayTransportR3)
    {f : R3 → ℝ → R3}
    (hf : NavierStokes.Comparator.ForceConditionDecay f) :
    force_smooth_on_global_spacetime_domain (comparatorForceToLean f) := by
  exact (h hf).1

/- Exact terminal terms on the pinned LeanDojo propositions. -/
#check dashiExactFeffermanC
#check dashiExactFeffermanD
#print axioms dashiExactFeffermanC
#print axioms dashiExactFeffermanD

end DASHILiteralClayNS
