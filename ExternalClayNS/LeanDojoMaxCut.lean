import LeanDojoExactTerminal

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

theorem comparatorForceDecayTransportR3_paid : ComparatorForceDecayTransportR3 := by
  intro f h
  exact comparatorForceDecay_to_leanDojo h

theorem comparatorForceDecayTransportPeriodic_paid : ComparatorForceDecayTransportPeriodic := by
  intro f h
  exact comparatorPeriodicForceDecay_to_leanDojo h

theorem comparatorForceDecayTransportR3_implies_smooth
    (h : ComparatorForceDecayTransportR3)
    {f : R3 → ℝ → R3}
    (hf : NavierStokes.Comparator.ForceConditionDecay f) :
    force_smooth_on_global_spacetime_domain (comparatorForceToLean f) := by
  exact (h hf).1

#check dashiExactFeffermanC
#check dashiExactFeffermanD
#print axioms dashiExactFeffermanC
#print axioms dashiExactFeffermanD

end DASHILiteralClayNS
