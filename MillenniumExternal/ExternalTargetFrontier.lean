import MillenniumExternal.TerminalCensus

namespace MillenniumExternal

inductive AdapterState where
  | greenExact
  | redType
  | redMath
  | upstreamIncomplete
  | upstreamSolvedUnformalized
  deriving DecidableEq, BEq, Repr

/-- Machine-facing classification of the *first unpaid edge* in the shortest
external-target dependency cone.  This is intentionally independent of
`AdapterState`: for example RH has already paid the exact statement/type weld,
but remains `analytic` because the Mathlib RH producer is still open. -/
inductive FrontierClass where
  | proved
  | typeWeld
  | analytic
  | upstreamDefect
  | solvedUnformalized
  deriving DecidableEq, BEq, Repr

structure ExternalTargetReceipt where
  problem : Problem
  upstreamDeclaration : String
  state : AdapterState
  frontier : FrontierClass
  firstUnpaid : String
  note : String
  deriving DecidableEq, Repr

/--
Fail-closed current receipts. `greenExact` is intentionally absent until a
theorem term is kernel-checked against the exact upstream proposition. The notes
separate statement/carrier transport from the genuine mathematical producer so
that same-object archaeology cannot be confused with a new conjectural lemma.

`frontier` and `firstUnpaid` encode the max-cut requested by the acceptance
programme: one literal external target, one shortest dependency cone, one first
unpaid theorem.  In particular a paid target-statement weld does not imply a
solution theorem is GREEN.

`upstreamSolvedUnformalized` is distinct from `redType`: it means the underlying
mathematics is historically solved, but this pinned external repository does not
contain the corresponding proof term. It therefore cannot be used as a DASHI
kernel acceptance receipt.
-/
def externalTargetReceipts : List ExternalTargetReceipt :=
  [ { problem := .pVersusNP
      upstreamDeclaration := "Millennium.ClayPVersusNP.Formulations.NegativeBranch"
      state := .redMath
      frontier := .analytic
      firstUnpaid := "Agda UniversalAnchoredPolynomialSATDecisionCollision on the literal PolynomialCostModel/SAT carrier"
      note := "Agda already proves the literal compiler UniversalAnchoredPolynomialSATDecisionCollision -> SATNotInP -> SATLowerBoundProducer -> PNotEqualsNP, including the anchor-or-already-fails reduction. The surviving mathematical wall is therefore exactly the universal anchored collision theorem; Agda-to-LeanDojo machine-model transport remains a later certification seam, not the first unpaid mathematical edge." }
  , { problem := .riemann
      upstreamDeclaration := "Millennium.ClayRiemannHypothesis"
      state := .redMath
      frontier := .analytic
      firstUnpaid := "produce Mathlib RiemannHypothesis from the surviving A2/A1/B analytic leaf"
      note := "Exact LeanDojo <-> Mathlib RiemannHypothesis statement weld is source-written bidirectionally. DASHI's current RH route still reports the global/high-zero theorem open; kernel acceptance therefore waits on the standard Mathlib RH producer, not another Clay statement reconstruction." }
  , { problem := .navierStokes
      upstreamDeclaration := "MillenniumNavierStokes.FeffermanA|B|C|D"
      state := .redType
      frontier := .typeWeld
      firstUnpaid := "kernel-check ClaySpec.ClayOptionC/D <-> LeanDojo FeffermanC/D in one environment"
      note := "ExternalClayNS already proves literal independent Clay C and D from the released comparator proof through a detailed physical/semantic bridge. LeanDojoTargetBridge reduces external acceptance exactly to ClaySpec.ClayOptionC/D <-> LeanDojo FeffermanC/D; no new fluid estimate belongs in this seam." }
  , { problem := .hodge
      upstreamDeclaration := "MillenniumHodge.ClayHodge"
      state := .upstreamIncomplete
      frontier := .upstreamDefect
      firstUnpaid := "faithful official Clay Hodge statement; internal general algebraic-cycle theorem remains separate"
      note := "LeanDojo registry marks this statement incomplete and not a valid prize target. DASHI retains the stronger rational-Hodge/algebraic-cycle same-object programme; the general algebraic reopening remains the research wall." }
  , { problem := .birchSwinnertonDyer
      upstreamDeclaration := "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer"
      state := .redMath
      frontier := .analytic
      firstUnpaid := "universal same-curve algebraic-rank = analytic-rank producer plus LeanDojo rank-carrier transport"
      note := "LeanDojo itself reduces the exact Taylor target to Rank.Existence plus finite Mordell-Weil rank. DASHI already has the literal same-curve analytic/algebraic rank carriers; ExactTargetSurface compiles the external Clay theorem from BSDLeanDojoSameObjectWeld plus the existing BSD core. The universal rank equality remains open in the current DASHI source, while continuation/rank-carrier transport is the certification seam." }
  , { problem := .yangMills
      upstreamDeclaration := "MillenniumYangMills.ClayYangMills"
      state := .upstreamIncomplete
      frontier := .upstreamDefect
      firstUnpaid := "faithful official Jaffe-Witten target; internal continuum construction and positive mass gap remain separate"
      note := "LeanDojo registry marks this interface incomplete. DASHI's stronger OS/reflection-positivity, continuum-QFT, Hamiltonian and mass-gap physical-object programme therefore remains the authoritative target until a faithful external statement exists." }
  , { problem := .poincare
      upstreamDeclaration := "MillenniumPoincare.ClayPoincareConjecture"
      state := .upstreamSolvedUnformalized
      frontier := .solvedUnformalized
      firstUnpaid := "upstream does not include Perelman's proof term"
      note := "The pinned upstream registry correctly marks Poincare historically solved, but its README explicitly says Perelman's Lean proof is not included. The statement is co-elaborated as a regression target only; absence of a local proof term is not a DASHI type-adapter failure and cannot be marked GREEN." }
  ]

theorem externalTargetReceipts_length : externalTargetReceipts.length = 7 := by decide

def hasGreenExact (p : Problem) : Bool :=
  externalTargetReceipts.any fun r => r.problem == p && r.state == .greenExact

/-- RH's target/type statement seam is no longer the max-cut: the exact
LeanDojo↔Mathlib equivalence lives in `ExactTargetSurface`.  The unpaid class is
therefore mathematical/analytic rather than representational. -/
theorem riemann_frontier_is_analytic :
    (externalTargetReceipts.find? (fun r => r.problem == .riemann)).map
        (fun r => r.frontier) = some .analytic := by
  decide

/-- Incomplete upstream statements are structurally incapable of becoming
GREEN merely because DASHI proves a stronger internal terminal theorem. -/
theorem hodge_not_green_exact : hasGreenExact .hodge = false := by decide

theorem yangMills_not_green_exact : hasGreenExact .yangMills = false := by decide

/-- A historically solved statement without a proof term in the pinned upstream
package is likewise not an exact-kernel DASHI receipt. -/
theorem poincare_not_green_exact : hasGreenExact .poincare = false := by decide

end MillenniumExternal
