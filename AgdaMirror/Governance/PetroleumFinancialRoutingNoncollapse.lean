namespace AgdaMirror.Governance.PetroleumFinancialRoutingNoncollapse

inductive PetroleumRoutingClass
  | ordinaryOilSettlement
  | sovereignReserveInvestment
  | proposedBilateralOilCredit
  | sanctionsEvasionRouting
  | covertArmsFundsDiversion
  deriving DecidableEq, Repr

structure RoutingMechanismReceipt where
  class : PetroleumRoutingClass
  sourceRef : String
  carrier : String
  intermediary : String
  settlementOrFlow : String
  downstreamUse : String
  sourceRole : String
  covertIntentPaid : Bool
  sanctionsEvasionPaid : Bool
  illegalDiversionPaid : Bool

def currentIranBarterReceipt : RoutingMechanismReceipt :=
  ⟨.sanctionsEvasionRouting,
   "Reuters 2026-09-10 + U.S. Treasury",
   "Iranian oil revenue",
   "China-linked SPV / trading entities as reported",
   "oil-for-goods / nonstandard financial routing",
   "Chinese goods / Iranian projects and procurement as reported",
   "investigative reporting plus sanctions-authority allegations",
   false,true,false⟩

def iranContraReceipt : RoutingMechanismReceipt :=
  ⟨.covertArmsFundsDiversion,
   "Walsh/NARA Iran-Contra record",
   "arms-sale proceeds",
   "North/Secord/Hakim Enterprise",
   "off-the-books corporate / Swiss-account flow",
   "Contra support",
   "historical Independent Counsel / archival record",
   true,false,true⟩

theorem current_routing_not_iran_contra :
    currentIranBarterReceipt.class != iranContraReceipt.class := by
  decide

end AgdaMirror.Governance.PetroleumFinancialRoutingNoncollapse
