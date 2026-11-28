import Mathlib
import YangMills.CMP119PeriodicPolymerReflectionGeometry
import YangMills.LiteralSU2ReflectedLinks

/-!
# Exact + / - / crossing / empty split of finite CMP119 polymer sectors

A selected finite source sector is a finite family of periodic link-support
polymers together with its actual evaluator on the same literal link field.
This file partitions that source sum by the time-plane placement proved in
`CMP119PeriodicPolymerReflectionGeometry`.

The decomposition is purely finite and exact.  Reflection compatibility of the
one-sided sums and PSD of the crossing contribution remain separately named
physical obligations; neither is inferred from the partition itself.
-/

namespace RequestProject.YangMills

structure CMP119PeriodicPolymerSectorSource
    (n : ℕ) [NeZero n] where
  polymers : Finset (CMP119PeriodicLinkPolymer n)
  evaluate :
    CMP119PeriodicLinkPolymer n → SU2TorusLinks (2 * n) → ℝ

namespace CMP119PeriodicPolymerSectorSource

/-- Complete selected source-sector action on one literal periodic link field. -/
def action
    {n : ℕ} [NeZero n]
    (source : CMP119PeriodicPolymerSectorSource n)
    (links : SU2TorusLinks (2 * n)) : ℝ :=
  ∑ X in source.polymers, source.evaluate X links

/-- Contribution from one of the four literal reflection placements. -/
def placementAction
    {n : ℕ} [NeZero n]
    (source : CMP119PeriodicPolymerSectorSource n)
    (placement : CMP119PolymerPlacement)
    (links : SU2TorusLinks (2 * n)) : ℝ :=
  ∑ X in source.polymers,
    if cmp119PeriodicPolymerPlacement n X = placement then
      source.evaluate X links
    else 0

/-- Every polymer contributes to exactly one of the four placement sums. -/
theorem action_eq_sum_placements
    {n : ℕ} [NeZero n]
    (source : CMP119PeriodicPolymerSectorSource n)
    (links : SU2TorusLinks (2 * n)) :
    source.action links =
      source.placementAction CMP119PolymerPlacement.positive links +
      source.placementAction CMP119PolymerPlacement.negative links +
      source.placementAction CMP119PolymerPlacement.crossing links +
      source.placementAction CMP119PolymerPlacement.empty links := by
  classical
  unfold action placementAction
  calc
    (∑ X in source.polymers, source.evaluate X links) =
      ∑ X in source.polymers,
        ((if cmp119PeriodicPolymerPlacement n X =
              CMP119PolymerPlacement.positive then
            source.evaluate X links else 0) +
         (if cmp119PeriodicPolymerPlacement n X =
              CMP119PolymerPlacement.negative then
            source.evaluate X links else 0) +
         (if cmp119PeriodicPolymerPlacement n X =
              CMP119PolymerPlacement.crossing then
            source.evaluate X links else 0) +
         (if cmp119PeriodicPolymerPlacement n X =
              CMP119PolymerPlacement.empty then
            source.evaluate X links else 0)) := by
        apply Finset.sum_congr rfl
        intro X hX
        cases hPlacement : cmp119PeriodicPolymerPlacement n X <;>
          simp [hPlacement]
    _ =
      (∑ X in source.polymers,
        if cmp119PeriodicPolymerPlacement n X =
            CMP119PolymerPlacement.positive then
          source.evaluate X links else 0) +
      (∑ X in source.polymers,
        if cmp119PeriodicPolymerPlacement n X =
            CMP119PolymerPlacement.negative then
          source.evaluate X links else 0) +
      (∑ X in source.polymers,
        if cmp119PeriodicPolymerPlacement n X =
            CMP119PolymerPlacement.crossing then
          source.evaluate X links else 0) +
      (∑ X in source.polymers,
        if cmp119PeriodicPolymerPlacement n X =
            CMP119PolymerPlacement.empty then
          source.evaluate X links else 0) := by
        simp_rw [Finset.sum_add_distrib]

/--
The exact one-sided source reflection obligation.  A physical sector closes its
noncrossing RP part by constructing this proposition on the SAME evaluator.
-/
def ReflectedOneSided
    {n : ℕ} [NeZero n]
    (source : CMP119PeriodicPolymerSectorSource n) : Prop :=
  ∀ links : SU2TorusLinks (2 * n),
    source.placementAction CMP119PolymerPlacement.negative links =
      source.placementAction CMP119PolymerPlacement.positive
        (su2EvenTimeReflectLinks links)

/-- Exact crossing contribution singled out for the PSD/falsification audit. -/
def crossingAction
    {n : ℕ} [NeZero n]
    (source : CMP119PeriodicPolymerSectorSource n) :
    SU2TorusLinks (2 * n) → ℝ :=
  source.placementAction CMP119PolymerPlacement.crossing

end CMP119PeriodicPolymerSectorSource

end RequestProject.YangMills
