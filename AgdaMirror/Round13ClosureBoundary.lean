/-! Secondary mirror of DASHI.Physics.Closure.Round13ClosureBoundaryExact.
A status transcription is not a proof of the R193 analytic payment. -/
namespace AgdaMirror.Round13ClosureBoundary

structure ClosureBoundary where
  productionEnergyLedgerClosed : Bool
  externalSignedCellExpansionClosed : Bool
  selfOwnerPaymentClosed : Bool
  externalTrajectoryPaymentClosed : Bool
  packageAClosed : Bool
  clayPromoted : Bool

def round13Boundary : ClosureBoundary :=
  ⟨true, true, false, false, false, false⟩

theorem energyLedgerStatus :
    round13Boundary.productionEnergyLedgerClosed = true := rfl

theorem externalCellsStatus :
    round13Boundary.externalSignedCellExpansionClosed = true := rfl

theorem selfOwnerPaymentStillOpen :
    round13Boundary.selfOwnerPaymentClosed = false := rfl

theorem externalTrajectoryPaymentStillOpen :
    round13Boundary.externalTrajectoryPaymentClosed = false := rfl

theorem packageAStillOpen :
    round13Boundary.packageAClosed = false := rfl

theorem noClayPromotion :
    round13Boundary.clayPromoted = false := rfl

end AgdaMirror.Round13ClosureBoundary
