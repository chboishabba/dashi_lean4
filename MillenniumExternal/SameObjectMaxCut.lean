import MillenniumExternal.TerminalCensus
import MillenniumExternal.ExternalTargetFrontier

/-!
# Same-object / physical-object max-cut for external Millennium adapters

Existing literal/same-object/physical-object welds are consumed before any new
mathematical hypothesis is introduced.  Under the current completion pass,
P≠NP, RH, Navier--Stokes and BSD are proof-resolution / transport lanes only.
A compiler failure may show that an assumed donor cannot actually be resolved;
until then this layer is not permitted to reopen the mathematics by inventing a
replacement premise.
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
      "Locate the existing universal SAT failure/lower-bound donor, transport its concrete SAT witness through the existing machine-model/Cook-Levin chain, and feed the resulting finite-alphabet language to LeanDojo. No second P/NP formalism or new lower-bound hypothesis is admissible." }

def riemannSameObjectCut : SameObjectCut :=
  { problem := .riemann
    existingProducer :=
      "existing DASHI RH terminal route to the standard Mathlib RiemannHypothesis proposition"
    existingWeld :=
      "LeanDojo ClayRiemannHypothesis <-> Mathlib RiemannHypothesis"
    remaining := .transportOnly
    note :=
      "Resolve/compose the existing terminal theorem into Mathlib.RiemannHypothesis and apply LeanDojo's exact equivalence. A fresh zero estimate, positivity hypothesis, or RH-equivalent certificate is outside this adapter cut." }

def navierStokesSameObjectCut : SameObjectCut :=
  { problem := .navierStokes
    existingProducer :=
      "DASHILiteralClayNS.dashiExactFeffermanC / dashiExactFeffermanD"
    existingWeld :=
      "paid comparator-data, carrier, derivative, momentum, incompressibility, energy and force-decay transports"
    remaining := .transportOnly
    note :=
      "The representation dependency cone is source-written all the way to the literal pinned Fefferman C/D propositions. No fluid estimate or additional proposition weld remains; only exact-kernel compilation and axiom audit are outstanding." }

def hodgeSameObjectCut : SameObjectCut :=
  { problem := .hodge
    existingProducer :=
      "DASHI rational-Hodge / algebraic-cycle same-object programme"
    existingWeld :=
      "Mathlib algebraic-cycle carrier plus Agda Hodge algebraic reopening stack"
    remaining := .upstreamSpecification
    note :=
      "Pinned LeanDojo Hodge is statement_incomplete. The remaining external issue is obtaining a faithful target, not weakening or reopening DASHI's Hodge mathematics." }

def bsdSameObjectCut : SameObjectCut :=
  { problem := .birchSwinnertonDyer
    existingProducer :=
      "Synthesis.Millennium.BSD universal same-curve analytic/algebraic rank weld and continuation/Mordell-Weil donors"
    existingWeld :=
      "literal Mathlib L-series continuation + rational point/free rank + paid affine/projective point-group transport"
    remaining := .transportOnly
    note :=
      "Resolve and compose the existing same-curve continuation, finite-rank and universal-rank donors into ExactTargetSurface's LeanDojo compiler. MillenniumBSDProjectiveRankWeld already pays the affine/projective group-model seam. Taylor-series or rank mathematics is not reopened here." }

def yangMillsSameObjectCut : SameObjectCut :=
  { problem := .yangMills
    existingProducer :=
      "DASHI OS/RP continuum-QFT Hamiltonian mass-gap physical-object stack"
    existingWeld :=
      "finite Wilson -> continuum observable -> OS Hilbert/Hamiltonian same-physical-object chain"
    remaining := .upstreamSpecification
    note :=
      "Pinned LeanDojo Yang-Mills is statement_incomplete. The remaining external issue is a faithful independent Jaffe-Witten target, not a new Yang-Mills premise." }

def poincareSameObjectCut : SameObjectCut :=
  { problem := .poincare
    existingProducer := "Perelman (historically solved mathematics)"
    existingWeld := "LeanDojo statement only"
    remaining := .historicalProofAbsent
    note :=
      "Regression target only: the pinned external repository does not contain Perelman's Lean proof." }

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

theorem hodge_is_upstream_specification :
    hodgeSameObjectCut.remaining = .upstreamSpecification := by decide

theorem yangMills_is_upstream_specification :
    yangMillsSameObjectCut.remaining = .upstreamSpecification := by decide

theorem pVersusNP_is_transport_only :
    pVersusNPSameObjectCut.remaining = .transportOnly := by decide

theorem riemann_is_transport_only :
    riemannSameObjectCut.remaining = .transportOnly := by decide

theorem navierStokes_is_transport_only :
    navierStokesSameObjectCut.remaining = .transportOnly := by decide

theorem bsd_is_transport_only :
    bsdSameObjectCut.remaining = .transportOnly := by decide

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
