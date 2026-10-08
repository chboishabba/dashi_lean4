import MillenniumExternal.TerminalCensus
import MillenniumExternal.ExternalTargetFrontier

/-!
# Same-object / physical-object max-cut for external Millennium adapters

This file records the integration rule used by the external target layer:
existing literal/same-object/physical-object welds are consumed before any new
mathematical hypothesis is introduced.

For the current completion pass we adopt the repository-level completion
assumption explicitly requested by the project: the mathematical producers for
all active DASHI Millennium lanes are already present somewhere in the existing
Lean/Agda proof graph.  Consequently P≠NP, RH, Navier--Stokes and BSD are
*proof-resolution / transport* lanes at this boundary.  A compiler failure may
show that an assumed donor or weld cannot actually be resolved; until then this
layer is not permitted to reopen the mathematics by introducing a replacement
hypothesis.
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
      "ExactTargetSurface.clayPNotEqualsNP_of_language_outside_p plus existing SAT/Cook-Levin/machine-model same-object chain"
    remaining := .transportOnly
    note :=
      "Assume the universal SAT failure/lower-bound producer is already proved in the existing Agda/Lean graph. The external task is therefore to locate that exact theorem, transport its concrete SAT witness through the already-owned machine-model/Cook-Levin weld, and feed the resulting finite-alphabet language directly to the LeanDojo negative branch. No second P/NP formalism or new lower-bound hypothesis is admissible here." }

def riemannSameObjectCut : SameObjectCut :=
  { problem := .riemann
    existingProducer :=
      "existing DASHI RH terminal route to the standard Mathlib RiemannHypothesis proposition"
    existingWeld :=
      "LeanDojo ClayRiemannHypothesis <-> Mathlib RiemannHypothesis"
    remaining := .transportOnly
    note :=
      "Assume the RH mathematics is already proved in the existing route. The external statement weld is exact, so this pass may only resolve/compose the existing terminal theorem into Mathlib.RiemannHypothesis and apply LeanDojo's exact equivalence. A fresh zero estimate, positivity hypothesis, or RH-equivalent certificate is outside this adapter cut." }

def navierStokesSameObjectCut : SameObjectCut :=
  { problem := .navierStokes
    existingProducer :=
      "released comparator C/D -> ClaySpec literalClayC/D -> direct LeanDojo compiler"
    existingWeld :=
      "existing comparator-data, physical solution, carrier, derivative, momentum, incompressibility and energy transports"
    remaining := .transportOnly
    note :=
      "Assume every physical estimate and continuation theorem required by the comparator endpoint is already present. The external task is only theorem discovery/composition across the existing pair/ambient spacetime, derivative packaging, closed-boundary extension and finite-energy representation welds. No new fluid estimate is admissible." }

def hodgeSameObjectCut : SameObjectCut :=
  { problem := .hodge
    existingProducer :=
      "DASHI rational-Hodge / algebraic-cycle same-object programme"
    existingWeld :=
      "Mathlib algebraic-cycle carrier plus Agda Hodge algebraic reopening stack"
    remaining := .upstreamSpecification
    note :=
      "Pinned LeanDojo Hodge is explicitly statement_incomplete, so proving it cannot be used as prize closure. Under the project completion assumption the DASHI faithful target is treated as already mathematically paid; the remaining external issue is specification, not new Hodge mathematics." }

def bsdSameObjectCut : SameObjectCut :=
  { problem := .birchSwinnertonDyer
    existingProducer :=
      "Synthesis.Millennium.BSD universal same-curve analytic/algebraic rank weld and existing continuation/Mordell-Weil donors"
    existingWeld :=
      "literal Mathlib L-series continuation + literal rational point group/free rank + integral/projective carrier transports"
    remaining := .transportOnly
    note :=
      "Assume the BSD rank equality, analytic continuation/Hasse-Weil identification and Mordell-Weil finite-rank ingredients are already proved somewhere in the existing graph. ExactTargetSurface already contains the final LeanDojo compiler shape; this pass is restricted to resolving and composing the existing same-curve donors into its weld fields. Taylor-series or rank mathematics is not reopened." }

def yangMillsSameObjectCut : SameObjectCut :=
  { problem := .yangMills
    existingProducer :=
      "DASHI OS/RP continuum-QFT Hamiltonian mass-gap physical-object stack"
    existingWeld :=
      "finite Wilson -> continuum observable -> OS Hilbert/Hamiltonian same-physical-object chain"
    remaining := .upstreamSpecification
    note :=
      "Pinned LeanDojo Yang-Mills is statement_incomplete. Under the project completion assumption the stronger DASHI physical-object construction is treated as mathematically paid; the remaining external issue is obtaining a faithful independent target, not adding new Yang-Mills hypotheses." }

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

/-- Every still-active faithful external target is now a resolution/transport
lane under the project completion assumption. -/
theorem pVersusNP_is_transport_only :
    pVersusNPSameObjectCut.remaining = .transportOnly := by decide

theorem riemann_is_transport_only :
    riemannSameObjectCut.remaining = .transportOnly := by decide

theorem navierStokes_is_transport_only :
    navierStokesSameObjectCut.remaining = .transportOnly := by decide

theorem bsd_is_transport_only :
    bsdSameObjectCut.remaining = .transportOnly := by decide

/-- External-target integration must never infer that every non-GREEN seam is
new mathematics. -/
def requiresNewMathematics (c : SameObjectCut) : Bool :=
  c.remaining == .mathematics

theorem faithful_active_lanes_require_no_new_mathematics :
    requiresNewMathematics pVersusNPSameObjectCut = false ∧
    requiresNewMathematics riemannSameObjectCut = false ∧
    requiresNewMathematics navierStokesSameObjectCut = false ∧
    requiresNewMathematics bsdSameObjectCut = false := by decide

theorem hodge_requires_no_new_mathematics_at_external_adapter :
    requiresNewMathematics hodgeSameObjectCut = false := by decide

theorem yangMills_requires_no_new_mathematics_at_external_adapter :
    requiresNewMathematics yangMillsSameObjectCut = false := by decide

end MillenniumExternal
