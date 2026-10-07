import MillenniumExternal.TerminalCensus

namespace MillenniumExternal

inductive AdapterState where
  | greenExact
  | redType
  | redMath
  | upstreamIncomplete
  | upstreamSolvedUnformalized
  deriving DecidableEq, BEq, Repr

structure ExternalTargetReceipt where
  problem : Problem
  upstreamDeclaration : String
  state : AdapterState
  note : String
  deriving DecidableEq, Repr

/--
Fail-closed current receipts. `greenExact` is intentionally absent until a
theorem term is kernel-checked against the exact upstream proposition. The notes
separate statement/carrier transport from the genuine mathematical producer so
that same-object archaeology cannot be confused with a new conjectural lemma.

`upstreamSolvedUnformalized` is distinct from `redType`: it means the underlying
mathematics is historically solved, but this pinned external repository does not
contain the corresponding proof term. It therefore cannot be used as a DASHI
kernel acceptance receipt.
-/
def externalTargetReceipts : List ExternalTargetReceipt :=
  [ { problem := .pVersusNP
      upstreamDeclaration := "Millennium.ClayPVersusNP.Formulations.NegativeBranch"
      state := .redMath
      note := "ExactTargetSurface now proves that one concrete finite-alphabet LeanDojo language L with L∈NP and L∉P yields the exact NegativeBranch. Thus the external adapter does not require a second class hierarchy or NP-completeness wrapper. DASHI already reduces its Clay core to an actual SAT lower-bound producer; the surviving mathematical wall is that universal polynomial SAT lower bound, followed by same-object transport of the SAT language/machine model into the LeanDojo witness." }
  , { problem := .riemann
      upstreamDeclaration := "Millennium.ClayRiemannHypothesis"
      state := .redMath
      note := "Exact LeanDojo <-> Mathlib RiemannHypothesis statement weld is source-written bidirectionally. DASHI's current RH route still reports the global/high-zero theorem open; kernel acceptance therefore waits on the standard Mathlib RH producer, not another Clay statement reconstruction." }
  , { problem := .navierStokes
      upstreamDeclaration := "MillenniumNavierStokes.FeffermanA|B|C|D"
      state := .redType
      note := "Fefferman C is the shortest external route. The released comparator theorem, comparator-data -> ClaySpec weld, ClaySpec-solution -> comparator weld, literal spatial carrier, pair-spacetime packing round-trip, domain membership and initial divergence are already paid. The direct exact-target compiler has only three representation transports left: condition-(4) derivative packaging, condition-(5) pair-spacetime -> LeanDojo time-first Fin4 packaging, and LeanDojo GlobalSmoothSolution+FiniteEnergy -> ClaySpec.ClaySolutionR3. No new fluid estimate belongs in this seam." }
  , { problem := .hodge
      upstreamDeclaration := "MillenniumHodge.ClayHodge"
      state := .upstreamIncomplete
      note := "LeanDojo registry marks this statement incomplete and not a valid prize target. DASHI retains the stronger rational-Hodge/algebraic-cycle same-object programme; the general algebraic reopening remains the research wall." }
  , { problem := .birchSwinnertonDyer
      upstreamDeclaration := "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer"
      state := .redMath
      note := "LeanDojo itself reduces the exact Taylor target to Rank.Existence plus finite Mordell-Weil rank. DASHI already has the literal same-curve analytic/algebraic rank carriers; ExactTargetSurface compiles the external Clay theorem from BSDLeanDojoSameObjectWeld plus the existing BSD core. The universal rank equality remains open in the current DASHI source, while continuation/rank-carrier transport is the certification seam." }
  , { problem := .yangMills
      upstreamDeclaration := "MillenniumYangMills.ClayYangMills"
      state := .upstreamIncomplete
      note := "LeanDojo registry marks this interface incomplete. DASHI's stronger OS/reflection-positivity, continuum-QFT, Hamiltonian and mass-gap physical-object programme therefore remains the authoritative target until a faithful external statement exists." }
  , { problem := .poincare
      upstreamDeclaration := "MillenniumPoincare.ClayPoincareConjecture"
      state := .upstreamSolvedUnformalized
      note := "The pinned upstream registry correctly marks Poincare historically solved, but its README explicitly says Perelman's Lean proof is not included. The statement is co-elaborated as a regression target only; absence of a local proof term is not a DASHI type-adapter failure and cannot be marked GREEN." }
  ]

theorem externalTargetReceipts_length : externalTargetReceipts.length = 7 := by decide

def hasGreenExact (p : Problem) : Bool :=
  externalTargetReceipts.any fun r => r.problem == p && r.state == .greenExact

/-- Incomplete upstream statements are structurally incapable of becoming
GREEN merely because DASHI proves a stronger internal terminal theorem. -/
theorem hodge_not_green_exact : hasGreenExact .hodge = false := by decide

theorem yangMills_not_green_exact : hasGreenExact .yangMills = false := by decide

/-- A historically solved statement without a proof term in the pinned upstream
package is likewise not an exact-kernel DASHI receipt. -/
theorem poincare_not_green_exact : hasGreenExact .poincare = false := by decide

end MillenniumExternal
