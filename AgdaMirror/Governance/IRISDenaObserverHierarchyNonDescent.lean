namespace AgdaMirror.Governance.IRISDenaObserverHierarchyNonDescent

inductive RefinedOperationalState
  | electricalMaintenanceCandidate
  | mechanicalMaintenanceCandidate
  deriving DecidableEq, Repr

inductive DutyClassSurface
  | platformMaintenanceClass
  deriving DecidableEq, Repr

inductive ProtocolSurface
  | lawfulProtocolGovernedMaintenance
  deriving DecidableEq, Repr

inductive ExactTask
  | electricalTask
  | mechanicalTask
  deriving DecidableEq, Repr

def dutyClassObserver : RefinedOperationalState -> DutyClassSurface
  | .electricalMaintenanceCandidate => .platformMaintenanceClass
  | .mechanicalMaintenanceCandidate => .platformMaintenanceClass

def protocolObserver : RefinedOperationalState -> ProtocolSurface
  | .electricalMaintenanceCandidate => .lawfulProtocolGovernedMaintenance
  | .mechanicalMaintenanceCandidate => .lawfulProtocolGovernedMaintenance

def exactTaskConsumer : RefinedOperationalState -> ExactTask
  | .electricalMaintenanceCandidate => .electricalTask
  | .mechanicalMaintenanceCandidate => .mechanicalTask

theorem duty_class_collision :
    dutyClassObserver .electricalMaintenanceCandidate =
    dutyClassObserver .mechanicalMaintenanceCandidate := by
  rfl

theorem protocol_collision :
    protocolObserver .electricalMaintenanceCandidate =
    protocolObserver .mechanicalMaintenanceCandidate := by
  rfl

theorem exact_tasks_differ :
    exactTaskConsumer .electricalMaintenanceCandidate !=
    exactTaskConsumer .mechanicalMaintenanceCandidate := by
  decide

structure ObserverHierarchyBoundary where
  verifiedDutyClassDeterminesExactTask : Bool := false
  completeProtocolDeterminesExactTask : Bool := false
  hansardPaymentDeletesOperationalResidual : Bool := false
  protocolPaymentDeletesOperationalResidual : Bool := false


def canonicalBoundary : ObserverHierarchyBoundary := {}

theorem acquisition_cells_are_non_substitutable :
    canonicalBoundary.verifiedDutyClassDeterminesExactTask = false ∧
    canonicalBoundary.completeProtocolDeterminesExactTask = false ∧
    canonicalBoundary.hansardPaymentDeletesOperationalResidual = false ∧
    canonicalBoundary.protocolPaymentDeletesOperationalResidual = false := by
  decide

end AgdaMirror.Governance.IRISDenaObserverHierarchyNonDescent
