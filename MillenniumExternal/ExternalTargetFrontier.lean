import MillenniumExternal.TerminalCensus

namespace MillenniumExternal

inductive AdapterState where
  | greenExact
  | redType
  | redMath
  | upstreamIncomplete
  deriving DecidableEq, BEq, Repr

structure ExternalTargetReceipt where
  problem : Problem
  upstreamDeclaration : String
  state : AdapterState
  note : String
  deriving DecidableEq, Repr

/--
Fail-closed current receipts.  `greenExact` is intentionally absent until a
theorem term is kernel-checked against the exact upstream proposition.  This
prevents source-written terminal constructors or registry strings from being
misreported as solved external targets.
-/
def externalTargetReceipts : List ExternalTargetReceipt :=
  [ { problem := .pVersusNP
      upstreamDeclaration := "Millennium.ClayPVersusNP.Formulations.NegativeBranch"
      state := .redType
      note := "Agda Clay-core producer exists; exact LeanDojo carrier adapter not kernel-checked." }
  , { problem := .riemann
      upstreamDeclaration := "Millennium.ClayRiemannHypothesis"
      state := .redType
      note := "DASHI terminal-positive/globalization constructors exist; exact pinned upstream package adapter awaits same-toolchain compatibility build." }
  , { problem := .navierStokes
      upstreamDeclaration := "MillenniumNavierStokes.FeffermanA|B|C|D"
      state := .redType
      note := "Merged DASHI critical-barrier/endgame constructors exist; exact Fefferman carrier adapter is the compatibility seam." }
  , { problem := .hodge
      upstreamDeclaration := "MillenniumHodge.ClayHodge"
      state := .upstreamIncomplete
      note := "LeanDojo registry marks this statement incomplete and not a valid prize target at the pinned commit." }
  , { problem := .birchSwinnertonDyer
      upstreamDeclaration := "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer"
      state := .redType
      note := "Universal same-curve rank theorem constructor exists; exact pinned upstream elliptic/L-series carrier adapter remains to kernel-check." }
  , { problem := .yangMills
      upstreamDeclaration := "MillenniumYangMills.ClayYangMills"
      state := .upstreamIncomplete
      note := "LeanDojo registry marks this interface incomplete; DASHI's stronger OS/QFT/mass-gap programme must target a faithful repaired statement." }
  , { problem := .poincare
      upstreamDeclaration := "MillenniumPoincare.ClayPoincareConjecture"
      state := .redType
      note := "Solved mathematics retained only as upstream regression; no DASHI proof programme is introduced." }
  ]

theorem externalTargetReceipts_length : externalTargetReceipts.length = 7 := by decide

def hasGreenExact (p : Problem) : Bool :=
  externalTargetReceipts.any fun r => r.problem == p && r.state == .greenExact

/-- Incomplete upstream statements are structurally incapable of becoming
GREEN merely because DASHI proves a stronger internal terminal theorem. -/
theorem hodge_not_green_exact : hasGreenExact .hodge = false := by decide

theorem yangMills_not_green_exact : hasGreenExact .yangMills = false := by decide

end MillenniumExternal
