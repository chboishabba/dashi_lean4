import Mathlib.Tactic
import NSBControl.Rational345R831PhysicalWeld
import NSBControl.Rational345R823RealProductionIncidence

/-!
# Literal real R853 scalar carrier on the physical radius-four state space

Round853 reduces the selected complete rate to three same-object scalars:
coherent commutator work, critical production, and critical dissipation.
This file ports those three scalar carriers to the real Lean radius-four model
without introducing reserve/demand data.

The coherent and dissipation carriers are written as their literal finite sums.
The production carrier is deliberately independent: it is twice the physical
R744 weighted ordered-incidence fold, and the existing incidence theorem proves
that this equals the public critical production on zero-mean states.

Thus the R853 normal form itself is no longer a semantic leaf.  The remaining
R831 obligation is only the R823 reserve/demand same-packet carrier identity.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345R853PhysicalScalarCarrier

open Rational345RealRadius4
open Rational345R831ReserveDecision
open Rational345R823RealProductionIncidence

/-- Literal fixed-output coherent scalar used by the R692/R741/R853 chain. -/
def r853CoherentCarrier (u : State) : ℝ :=
  ∑ k : Mode, if isZeroMode k then 0 else
    coherentWork
      (fixedOutputMixed u k)
      (fixedOutputCommutator u (projectedNonlinearity u) k)

/-- Literal R744 physical incidence carrier, with the factor two required by
public `criticalProduction`. -/
def r853ProductionCarrier (u : State) : ℝ :=
  2 * physicalWeightedProductionIncidenceTotal u

/-- Literal critical dissipation finite sum used by R741/R853. -/
def r853DissipationCarrier (u : State) : ℝ :=
  ∑ k : Mode, if isZeroMode k then 0 else
    criticalWeight k * normSq k *
      (hermitianDot (u k) (u k)).re

/-- Decision-normalized Round853 complete physical rate (nu = delta = 1). -/
def r853CompletePhysicalRate (u : State) : ℝ :=
  6 *
    (12 * r853CoherentCarrier u
      - r853ProductionCarrier u
      + r853DissipationCarrier u)

/-- Coherent carrier identification is literal finite-sum equality. -/
theorem r853_coherent_sameObject
    (u : State) (_hu : IsR823PhysicalState u) :
    r853CoherentCarrier u = globalCoherentWork u := by
  rfl

/-- R744 incidence summation identifies the physical production carrier with
public critical production.  Only zero mean is needed from physicality. -/
theorem r853_production_sameObject
    (u : State) (hu : IsR823PhysicalState u) :
    r853ProductionCarrier u = criticalProduction u := by
  have hzero : u Rational345Round71ZeroMode.zeroMode = 0 := hu.2.2
  unfold r853ProductionCarrier
  rw [criticalProduction_eq_twice_weightedIncidence u]
  rw [weightedIncidence_eq_physicalWeightedIncidence u hzero]

/-- Dissipation carrier identification is literal finite-sum equality. -/
theorem r853_dissipation_sameObject
    (u : State) (_hu : IsR823PhysicalState u) :
    r853DissipationCarrier u = criticalDissipation u := by
  rfl

/-- The concrete three-scalar carrier reproduces the public selected rate on
physical states.  No reserve/demand semantics enter this theorem. -/
theorem selectedRate_eq_r853CompletePhysicalRate
    (u : State) (hu : IsR823PhysicalState u) :
    selectedRate u = r853CompletePhysicalRate u := by
  rw [selectedRate_public_definition]
  unfold r853CompletePhysicalRate
  rw [r853_coherent_sameObject u hu,
      r853_production_sameObject u hu,
      r853_dissipation_sameObject u hu]

/-- The three scalar identifications requested by the physical R853 max-cut
are now explicit on the real trajectory carrier. -/
def r853PhysicalThreeScalarCarrierClosed : Bool := true

/-- R823 reserve/demand same-packet semantics are intentionally not asserted by
this scalar carrier owner. -/
def r853ScalarCarrierIntroducesReserveSemantics : Bool := false

end Rational345R853PhysicalScalarCarrier
end NSBControl
