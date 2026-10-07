import MillenniumExternal.TerminalCensus
import MillenniumExternal.ExternalTargetFrontier

/-!
# Same-object / physical-object max-cut for external Millennium adapters

This file records the integration rule used by the external target layer:
existing literal/same-object/physical-object welds are consumed before any new
mathematical hypothesis is introduced. A remaining seam is classified as
`transportOnly` exactly when the current repository already owns the mathematical
producer and only carrier/proposition/toolchain identification remains.
-/

namespace MillenniumExternal

inductive RemainingSeam where
  | none
  | transportOnly
  | mathematics
  | upstreamSpecification
  | historicalProofAbsent
  deriving DecidableEq, BEq, Repr

structure SameObjectCut where
  problem : Problem
  existingProducer : String
  existingWeld : String
  remaining : RemainingSeam
  note : String
  deriving DecidableEq, Repr

def pVersusNPSameObjectCut : SameObjectCut :=
  { problem := .pVersusNP
    existingProducer :=
      "Agda PNotEqualsNPClayCoreExact / PNotEqualsNPDirectSATLowerBoundExact"
    existingWeld :=
      "SATNotInP -> PNotEqualsNP Clay-core compiler; machine-model transport retained separately"
    remaining := .mathematics
    note :=
      "The external adapter must reuse the existing SAT/P machine-model chain. The only mathematical producer still represented as an input is the universal SAT lower-bound/failure theorem; no second P-vs-NP formalism is permitted." }

def riemannSameObjectCut : SameObjectCut :=
  { problem := .riemann
    existingProducer :=
      "Mathlib RiemannHypothesis endpoint fed by DASHI RH terminal route"
    existingWeld :=
      "LeanDojo ClayRiemannHypothesis <-> Mathlib RiemannHypothesis"
    remaining := .mathematics
    note :=
      "The external statement weld is already exact. Any remaining work belongs upstream of Mathlib.RiemannHypothesis in the existing RH route, not in a new Clay adapter." }

def navierStokesSameObjectCut : SameObjectCut :=
  { problem := .navierStokes
    existingProducer :=
      "ExternalClayNS literalClayC / literalClayD"
    existingWeld :=
      "released comparator -> independent ClaySpec C/D physical-semantic adapter"
    remaining := .transportOnly
    note :=
      "No new fluid estimate is admissible here. The remaining cut is exact proposition/carrier identification ClaySpec.ClayOptionC/D <-> LeanDojo FeffermanC/D in one compatible kernel." }

def hodgeSameObjectCut : SameObjectCut :=
  { problem := .hodge
    existingProducer :=
      "DASHI rational-Hodge / algebraic-cycle same-object programme"
    existingWeld :=
      "Mathlib algebraic-cycle carrier plus Agda Hodge algebraic reopening stack"
    remaining := .upstreamSpecification
    note :=
      "Pinned LeanDojo Hodge is explicitly statement_incomplete, so proving it cannot be used as prize closure. DASHI's stronger faithful target remains authoritative." }

def bsdSameObjectCut : SameObjectCut :=
  { problem := .birchSwinnertonDyer
    existingProducer :=
      "Synthesis.Millennium.BSD universal same-curve analytic/algebraic rank weld"
    existingWeld :=
      "literal Mathlib L-series continuation + literal rational point group/free rank"
    remaining := .mathematics
    note :=
      "ExactTargetSurface already compiles the LeanDojo target once the existing BSD core and the integral-model/projective-rank same-object transport are supplied. Taylor-series mathematics is not reopened." }

def yangMillsSameObjectCut : SameObjectCut :=
  { problem := .yangMills
    existingProducer :=
      "DASHI OS/RP continuum-QFT Hamiltonian mass-gap physical-object stack"
    existingWeld :=
      "finite Wilson -> continuum observable -> OS Hilbert/Hamiltonian same-physical-object chain"
    remaining := .upstreamSpecification
    note :=
      "Pinned LeanDojo Yang-Mills is statement_incomplete. The stronger DASHI physical-object construction remains the acceptance surface until an external faithful target exists." }

def poincareSameObjectCut : SameObjectCut :=
  { problem := .poincare
    existingProducer := "Perelman (historically solved mathematics)"
    existingWeld := "LeanDojo statement only"
    remaining := .historicalProofAbsent
    note :=
      "Regression target only: the pinned external repository does not contain Perelman's Lean proof." }

/-- Canonical post-archaeology max-cut. These rows deliberately reuse existing
same-object and physical-object owners rather than opening replacement carriers. -/
def sameObjectCuts : List SameObjectCut :=
  [ pVersusNPSameObjectCut
  , riemannSameObjectCut
  , navierStokesSameObjectCut
  , hodgeSameObjectCut
  , bsdSameObjectCut
  , yangMillsSameObjectCut
  , poincareSameObjectCut
  ]

theorem sameObjectCuts_length : sameObjectCuts.length = 7 := by decide

/-- The two lanes whose pinned upstream statements are known incomplete are
classified as specification seams, never mathematical failures of DASHI. -/
theorem hodge_is_upstream_specification :
    hodgeSameObjectCut.remaining = .upstreamSpecification := by decide

theorem yangMills_is_upstream_specification :
    yangMillsSameObjectCut.remaining = .upstreamSpecification := by decide

/-- Navier-Stokes is the canonical transport-only lane after consuming the
existing released-proof -> independent-Clay physical/semantic weld. -/
theorem navierStokes_is_transport_only :
    navierStokesSameObjectCut.remaining = .transportOnly := by decide

/-- External-target integration must never infer that every non-GREEN seam is
new mathematics. -/
def requiresNewMathematics (c : SameObjectCut) : Bool :=
  c.remaining == .mathematics

theorem navierStokes_requires_no_new_mathematics :
    requiresNewMathematics navierStokesSameObjectCut = false := by decide

theorem hodge_requires_no_new_mathematics_at_external_adapter :
    requiresNewMathematics hodgeSameObjectCut = false := by decide

theorem yangMills_requires_no_new_mathematics_at_external_adapter :
    requiresNewMathematics yangMillsSameObjectCut = false := by decide

end MillenniumExternal
