import Mathlib

/-!
# Lean mirror of `DASHI/Core/IntersectionalNonFactorability.agda`

Conceptual/source attribution:
Kimberlé Crenshaw, "Mapping the Margins: Intersectionality, Identity Politics,
and Violence against Women of Color", Stanford Law Review 43(6), 1241–1299
(1991), DOI 10.2307/1229039, motivates the warning that a coarse/single-axis
representation can erase situated distinctions.

The factorisation criterion, witness type, obstruction theorem, and recharting
theorems below are **DASHI mathematical translations**.  They are not theorems
attributed to Crenshaw.

This mirror is intentionally generic so domain lanes such as AdK consume the
same factorisation spine rather than defining local variants.
-/

namespace AgdaMirror.IntersectionalNonFactorability

/-- A phenomenon factors through a coarse observer when some interpretation of
that coarse surface reproduces the phenomenon on every situated state. -/
structure FactorsThrough
    {Situated Flat Outcome : Type*}
    (flatten : Situated → Flat)
    (phenomenon : Situated → Outcome) where
  interpretFlat : Flat → Outcome
  factorisation :
    (state : Situated) →
      phenomenon state = interpretFlat (flatten state)

/-- Concrete obstruction: two situated states collide under the coarse observer
while the phenomenon still distinguishes them. -/
structure NonFactorabilityWitness
    {Situated Flat Outcome : Type*}
    (flatten : Situated → Flat)
    (phenomenon : Situated → Outcome) where
  left : Situated
  right : Situated
  sameFlatProjection : flatten left = flatten right
  situatedOutcomesDiffer : phenomenon left ≠ phenomenon right

/-- A witnessed collision rules out every factorisation of that exact
phenomenon through that exact coarse observer. -/
theorem witnessRulesOutEveryFlatFactorisation
    {Situated Flat Outcome : Type*}
    {flatten : Situated → Flat}
    {phenomenon : Situated → Outcome}
    (witness : NonFactorabilityWitness flatten phenomenon)
    (factor : FactorsThrough flatten phenomenon) : False := by
  apply witness.situatedOutcomesDiffer
  calc
    phenomenon witness.left =
        factor.interpretFlat (flatten witness.left) :=
      factor.factorisation witness.left
    _ = factor.interpretFlat (flatten witness.right) :=
      congrArg factor.interpretFlat witness.sameFlatProjection
    _ = phenomenon witness.right :=
      (factor.factorisation witness.right).symm

/-- Post-composing a coarse observer cannot recover information already erased
by that observer. -/
def postcomposeNonFactorability
    {Situated Flat Recharted Outcome : Type*}
    {flatten : Situated → Flat}
    {phenomenon : Situated → Outcome}
    (rechart : Flat → Recharted)
    (witness : NonFactorabilityWitness flatten phenomenon) :
    NonFactorabilityWitness (fun state => rechart (flatten state)) phenomenon :=
  { left := witness.left
    right := witness.right
    sameFlatProjection := congrArg rechart witness.sameFlatProjection
    situatedOutcomesDiffer := witness.situatedOutcomesDiffer }

/-- Recharting/relabeling the old quotient is therefore insufficient to recover
a phenomenon separated by the original collision witness. -/
theorem rechartingCannotRecoverErasedPhenomenon
    {Situated Flat Recharted Outcome : Type*}
    {flatten : Situated → Flat}
    {phenomenon : Situated → Outcome}
    (rechart : Flat → Recharted)
    (witness : NonFactorabilityWitness flatten phenomenon) :
    ¬ FactorsThrough (fun state => rechart (flatten state)) phenomenon := by
  intro factor
  exact witnessRulesOutEveryFlatFactorisation
    (postcomposeNonFactorability rechart witness) factor

/-- The conceptual citation does not manufacture the DASHI factorisation
criterion or its theorems. -/
def conceptualSourceCreatesFactorisationTheorem : Bool := false

example : conceptualSourceCreatesFactorisationTheorem = false := rfl

end AgdaMirror.IntersectionalNonFactorability


namespace DashiTradeGoldenParity

open AgdaMirror.IntersectionalNonFactorability

/-!
Parity-only dashiTRADE instance.

Agda owns the trading semantics in
`DASHI/Trading/DashiTradeDreamOptionConeExact.agda`.

This Lean section only instantiates the existing generic non-factorability
mirror. It does not create an independent trading ontology or runtime
conformance claim.
-/

inductive Direction
  | shortDirection
  | flatDirection
  | longDirection
  deriving DecidableEq, Repr

inductive InventoryRegime
  | neutralInventory
  | crowdedLongInventory
  deriving DecidableEq, Repr

structure TradingState where
  proposal : Direction
  inventory : InventoryRegime
  deriving DecidableEq, Repr

inductive TradeAction
  | sellAction
  | holdAction
  | buyAction
  deriving DecidableEq, Repr

def candidateObserver (state : TradingState) : Direction :=
  state.proposal

def actionAvailable : TradingState → TradeAction → Bool
  | _, .holdAction => true
  | _, .sellAction => true
  | ⟨.longDirection, .neutralInventory⟩, .buyAction => true
  | _, .buyAction => false

def cleanLongState : TradingState :=
  ⟨.longDirection, .neutralInventory⟩

def crowdedLongState : TradingState :=
  ⟨.longDirection, .crowdedLongInventory⟩

theorem sameLongProposal :
    candidateObserver cleanLongState = candidateObserver crowdedLongState := rfl

theorem buyAvailabilityDiffers :
    actionAvailable cleanLongState .buyAction ≠
      actionAvailable crowdedLongState .buyAction := by
  decide

def buyViabilityDoesNotFactorThroughDirection :
    NonFactorabilityWitness
      candidateObserver
      (fun state => actionAvailable state .buyAction) where
  left := cleanLongState
  right := crowdedLongState
  sameFlatProjection := sameLongProposal
  situatedOutcomesDiffer := buyAvailabilityDiffers

theorem noDirectionOnlyBuyClassifier :
    ¬ FactorsThrough
      candidateObserver
      (fun state => actionAvailable state .buyAction) := by
  intro factor
  exact witnessRulesOutEveryFlatFactorisation
    buyViabilityDoesNotFactorThroughDirection
    factor

theorem postprocessedDirectionStillCannotRecoverBuyViability
    {Chart : Type*}
    (rechart : Direction → Chart) :
    ¬ FactorsThrough
      (fun state => rechart (candidateObserver state))
      (fun state => actionAvailable state .buyAction) :=
  rechartingCannotRecoverErasedPhenomenon
    rechart
    buyViabilityDoesNotFactorThroughDirection

def agdaIsGoldenOwner : Bool := true

def leanDefinesIndependentTradingSemantics : Bool := false

def leanClaimsRuntimeConformance : Bool := false

example : agdaIsGoldenOwner = true := rfl

example : leanDefinesIndependentTradingSemantics = false := rfl

example : leanClaimsRuntimeConformance = false := rfl

end DashiTradeGoldenParity
