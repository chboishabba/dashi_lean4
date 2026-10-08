import MillenniumExternal.SameObjectMaxCut

/-!
# Proof-resolution-only completion board

This is the operational interpretation of the project completion assumption for
the external Millennium pass.

For P≠NP, RH, Navier--Stokes and BSD we assume that every mathematical theorem
needed by the final external target has already been proved somewhere in the
existing Lean/Agda graph.  Therefore the permitted operations are deliberately
restricted to discovery, import, definitional reduction, `simpa`/`change`,
existing equivalences, same-object transport, and theorem composition.

A missing symbol or failed composition is evidence to search the proof graph;
it is not permission to add a new mathematical premise.  Only after exhaustive
resolution may a lane be reclassified, and that reclassification must be backed
by a concrete compiler/type error rather than roadmap prose.
-/

namespace MillenniumExternal

inductive ResolutionOperation where
  | locateExistingTheorem
  | importExistingTheorem
  | definitionalEquality
  | simplifyExistingEquality
  | applyExistingEquivalence
  | sameObjectTransport
  | composeExistingTheorems
  | kernelCheck
  deriving DecidableEq, BEq, Repr

structure ProofResolutionLane where
  problem : Problem
  producerSearch : List String
  preferredOperations : List ResolutionOperation
  externalCompiler : String
  newMathematicsPermitted : Bool
  deriving DecidableEq, Repr

private def standardResolutionOps : List ResolutionOperation :=
  [ .locateExistingTheorem
  , .importExistingTheorem
  , .definitionalEquality
  , .simplifyExistingEquality
  , .applyExistingEquivalence
  , .sameObjectTransport
  , .composeExistingTheorems
  , .kernelCheck
  ]

def pVersusNPResolution : ProofResolutionLane :=
  { problem := .pVersusNP
    producerSearch :=
      [ "PNotEqualsNPClayCoreExact"
      , "PNotEqualsNPDirectSATLowerBoundExact"
      , "SATNotInP"
      , "CookLevin"
      , "machine-model transport" ]
    preferredOperations := standardResolutionOps
    externalCompiler := "clayPNotEqualsNP_of_language_outside_p"
    newMathematicsPermitted := false }

def rhResolution : ProofResolutionLane :=
  { problem := .riemann
    producerSearch :=
      [ "RiemannHypothesis"
      , "CanonicalTerminalPositive"
      , "RH terminal constructor"
      , "selected-zero/globalization same-object weld" ]
    preferredOperations := standardResolutionOps
    externalCompiler := "clayRiemannHypothesis_of_mathlib"
    newMathematicsPermitted := false }

def navierStokesResolution : ProofResolutionLane :=
  { problem := .navierStokes
    producerSearch :=
      [ "literalClayC"
      , "literalClayD"
      , "current_three_coordinate_endgame"
      , "physical/comparator solution weld"
      , "momentum/divergence/energy transport" ]
    preferredOperations := standardResolutionOps
    externalCompiler := "LeanDojo exact Fefferman C/D terminal compiler"
    newMathematicsPermitted := false }

def bsdResolution : ProofResolutionLane :=
  { problem := .birchSwinnertonDyer
    producerSearch :=
      [ "universalBSDRankTheorem_of_background"
      , "universalBSDRankTheorem_of_producers"
      , "BSDClayCoreObligation"
      , "Hasse-Weil/LSeries same-object weld"
      , "Mordell-Weil affine/projective rank transport" ]
    preferredOperations := standardResolutionOps
    externalCompiler := "clayBirchSwinnertonDyer_of_dashi"
    newMathematicsPermitted := false }

def faithfulResolutionLanes : List ProofResolutionLane :=
  [pVersusNPResolution, rhResolution, navierStokesResolution, bsdResolution]

theorem faithfulResolutionLanes_length : faithfulResolutionLanes.length = 4 := by
  decide

theorem no_faithful_resolution_lane_permits_new_mathematics :
    faithfulResolutionLanes.all (fun lane => !lane.newMathematicsPermitted) = true := by
  decide

theorem resolution_board_agrees_with_same_object_cut :
    pVersusNPSameObjectCut.remaining = .transportOnly ∧
    riemannSameObjectCut.remaining = .transportOnly ∧
    navierStokesSameObjectCut.remaining = .transportOnly ∧
    bsdSameObjectCut.remaining = .transportOnly := by
  decide

end MillenniumExternal
