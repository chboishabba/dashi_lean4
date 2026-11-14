import Integration.DASHITOE.ConcreteInhabitants

namespace DASHITOE

/-- Agda PR #1164 actual R3 Hodge/wedge/cross theorem value. -/
def agda1164HodgeCrossInhabitant : FormalInhabitantReceipt :=
  { prover := "Agda"
    repository := "chboishabba/dashi_agda"
    pullRequest := 1164
    headCommit := "043a55e66b67a71d52612382d7d665e8ec8f8122"
    moduleName := "DASHI.Physics.Foundations.R3HodgeCrossExact"
    declaration := "hodgeWedgeEqualsCross"
    propositionScope := "On the concrete R3/SU2 Lie-algebra carrier, Hodge star of the explicit bivector wedge equals the right-hand cross product; the same owner proves [u,v]=2(u cross v)."
    authority := .importedFormalInhabitant }

/-- Agda PR #1164 actual group-level U1 inclusion in concrete quaternionic SU2. -/
def agda1164U1SU2TorusInhabitant : FormalInhabitantReceipt :=
  { prover := "Agda"
    repository := "chboishabba/dashi_agda"
    pullRequest := 1164
    headCommit := "043a55e66b67a71d52612382d7d665e8ec8f8122"
    moduleName := "DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact"
    declaration := "includePreservesMultiply"
    propositionScope := "A literal unit-circle U1 group is constructed inside unit-quaternion SU2; its inclusion preserves multiplication, inverse and identity."
    authority := .importedFormalInhabitant }

/-- Agda PR #1165 actual Brown-Maclay electromagnetic stress witness. -/
def agda1165BrownMaclayStressInhabitant : FormalInhabitantReceipt :=
  { prover := "Agda"
    repository := "chboishabba/dashi_agda"
    pullRequest := 1165
    headCommit := "64c8d33320a8e313064a565068ae399566b4de23"
    moduleName := "DASHI.Physics.QuantumVacuum.CasimirBrownMaclayEnergyConditionExact"
    declaration := "canonicalBrownMaclayNormalizedStressWitness"
    propositionScope := "Source-bounded ideal parallel-plate electromagnetic stress witness with normalized rho=-1, tangential pressures +1,+1 and normal pressure -3; same owner derives null contraction -4w."
    authority := .importedFormalInhabitant }

structure GaugeFormalInhabitantBundle where
  hodgeCross : FormalInhabitantReceipt
  u1InsideSU2 : FormalInhabitantReceipt
  brownMaclayStress : FormalInhabitantReceipt


def canonicalGaugeFormalInhabitantBundle : GaugeFormalInhabitantBundle :=
  { hodgeCross := agda1164HodgeCrossInhabitant
    u1InsideSU2 := agda1164U1SU2TorusInhabitant
    brownMaclayStress := agda1165BrownMaclayStressInhabitant }

end DASHITOE
