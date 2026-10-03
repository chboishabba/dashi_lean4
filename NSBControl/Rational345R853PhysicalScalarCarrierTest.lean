import NSBControl.Rational345R853PhysicalScalarCarrier

namespace NSBControl
namespace Rational345R853PhysicalScalarCarrierTest

open Rational345RealRadius4
open Rational345R831ReserveDecision
open Rational345R853PhysicalScalarCarrier

example (u : State) (hu : IsR823PhysicalState u) :
    r853CoherentCarrier u = globalCoherentWork u := by
  exact r853_coherent_sameObject u hu

example (u : State) (hu : IsR823PhysicalState u) :
    r853ProductionCarrier u = criticalProduction u := by
  exact r853_production_sameObject u hu

example (u : State) (hu : IsR823PhysicalState u) :
    r853DissipationCarrier u = criticalDissipation u := by
  exact r853_dissipation_sameObject u hu

example (u : State) (hu : IsR823PhysicalState u) :
    selectedRate u = r853CompletePhysicalRate u := by
  exact selectedRate_eq_r853CompletePhysicalRate u hu

example : r853PhysicalThreeScalarCarrierClosed = true := by
  rfl

end Rational345R853PhysicalScalarCarrierTest
end NSBControl
