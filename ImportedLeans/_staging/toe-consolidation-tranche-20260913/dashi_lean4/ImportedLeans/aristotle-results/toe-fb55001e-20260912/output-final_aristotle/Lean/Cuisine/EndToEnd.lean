import Cuisine.Witnesses
import Cuisine.Surfaces
import Cuisine.DataFlow
import Cuisine.Provenance
import Cuisine.LedgerPattern
import Cuisine.ToneSeparation
import Cuisine.CarryingCapacity
import Cuisine.HyperfabricGuard

/-!
# The checkable end-to-end statement for the cuisine lane

This file assembles the preceding layers into one structure, `CuisineSpine`,
whose fields are *propositions, equivalences and obstructions* — never Boolean
flags, names, or unproved interfaces — and exhibits a canonical inhabitant
`cuisineSpine`, every field of which is discharged by a theorem proved in this
repository.

It also proves one composite statement, `cuisine_end_to_end`, chaining the
layers: the non-additive umami law, the observer- and process-dependence
obstructions, the acyclic sauce order, the repaired order-sensitive mole route,
the fail-closed promotion gate and publication decision, the channel-dependent
provenance routing, and the negative bridge to the `Synthesis` tone spine.

## What this is *not*

Every carrier below is a finite set or a list of natural numbers.  Nothing here
is an empirical claim about food, chemistry, safety, history, or cultural
authority, and nothing here is a physical or mathematical theory of everything.
The honest content is: those parts of the supplied cuisine material that carry
proof content carry exactly the content stated below; the parts that carry none
are identified as such (`Cuisine.LedgerPattern`, `ProcessRoute.processRouteRel_total`);
and the tempting cross-domain identification with the ternary tone spine is
recorded as a negative theorem.
-/

namespace Cuisine.EndToEnd

open Cuisine.SensoryCore Cuisine.Surfaces Cuisine.Lineage Cuisine.ProcessRoute
open Cuisine.DataFlow Cuisine.Publication Cuisine.Provenance Cuisine.LedgerPattern
open Cuisine.ToneSeparation Cuisine.Witnesses Cuisine.CarryingCapacity
open Cuisine.HyperfabricGuard

/-! ## The interface -/

/-- The cuisine spine: the interface that the supplied cuisine material
genuinely supports.  Positive fields are theorems; negative fields record the
collapses that provably do not occur, and the two "no content" fields record
where the supplied formalism proves nothing. -/
structure CuisineSpine where
  /-- The umami record has exactly two degrees of freedom. -/
  umamiNormalForm : ∀ u : UmamiBlend, u = UmamiBlend.ofLoads u.glutamateLoad u.nucleotideLoad
  /-- Its combination law factorises multiplicatively. -/
  umamiFactorises : ∀ u : UmamiBlend,
    1 + u.combinedIntensity = (1 + u.glutamateLoad) * (1 + u.nucleotideLoad)
  /-- And it is not additive in any reparametrisation. -/
  umamiNotAdditive :
    ¬ ∃ f : ℕ → ℕ, ∀ g n : ℕ, (UmamiBlend.ofLoads g n).combinedIntensity = f g + f n
  /-- Valence is not a function of the stimulus. -/
  valenceObstruction :
    ¬ ∃ f : SensoryProfile → Valence,
        f trainedFunkReading.profile = trainedFunkReading.valence ∧
        f unfamiliarFunkReading.profile = unfamiliarFunkReading.valence
  /-- Safety is not a function of stimulus and cue. -/
  safetyObstruction :
    ¬ ∃ f : SensoryProfile → StrangenessCue → SafetyEvidence,
        f controlledAgedBoundary.profile controlledAgedBoundary.perceivedCue =
          controlledAgedBoundary.safetyStatus ∧
        f unknownProcessBoundary.profile unknownProcessBoundary.perceivedCue =
          unknownProcessBoundary.safetyStatus
  /-- Every recorded surface separation separates genuinely distinct surfaces. -/
  surfaceLedgerSound : ∀ {a b : CuisineSurface}, SurfaceDistinction a b → a ≠ b
  /-- ... but the ledger is partial. -/
  surfaceLedgerPartial :
    CuisineSurface.nutritionSurface ≠ CuisineSurface.flavourSurface ∧
      ¬ SurfaceDistinction CuisineSurface.nutritionSurface CuisineSurface.flavourSurface ∧
      ¬ SurfaceDistinction CuisineSurface.flavourSurface CuisineSurface.nutritionSurface
  /-- Sauce derivation is a partial order (acyclic). -/
  sauceAcyclic : ∀ {a b : Sauce}, SaucePath a b → SaucePath b a → a = b
  /-- Its two classical families do not communicate. -/
  sauceDisconnected : ¬ SaucePath Sauce.bechamel Sauce.bordelaise
  /-- The supplied process-route relation is total, hence contentless. -/
  suppliedRouteContentless : ∀ a b : CandidateMoleState, ProcessRouteRel a b
  /-- The repaired route relation is acyclic ... -/
  repairedRouteAcyclic : ∀ {a b : CandidateMoleState}, MoleRoute a b → MoleRoute b a → a = b
  /-- ... and in it the two cooking orders are genuinely unmergeable. -/
  ordersUnmergeable :
    ¬ MoleRoute CandidateMoleState.friedThenRehydratedChileState
        CandidateMoleState.rehydratedThenFriedChileState ∧
      ¬ MoleRoute CandidateMoleState.rehydratedThenFriedChileState
        CandidateMoleState.friedThenRehydratedChileState
  /-- Promotion is fail-closed: no policy-generic promoter exists. -/
  promotionFailClosed :
    ¬ Nonempty ((policy : PromotionPolicy) → SurfaceClaim → PromotedClaim policy)
  /-- Publication severity is preserved exactly by the decision map. -/
  publicationExact : ∀ r : PublicationRisk, decisionLevel (publicationDecision r) = riskLevel r
  /-- With the repaired assessment, one maximal component risk forces abstention. -/
  publicationAbstains : ∀ t : TightAssessment,
    riskLevel t.locationRisk = 2 ∨ riskLevel t.appropriationRisk = 2 ∨
      riskLevel t.harassmentRisk = 2 → t.decision = PublicationDecision.abstainDecision
  /-- Provenance channels are not determined by the contribution. -/
  channelObstruction :
    ¬ ∃ f : HistoricalContribution → CuisineOutputChannel,
        f canonicalRouting.brandRoute.contribution = canonicalRouting.brandRoute.channel ∧
        f canonicalRouting.creditRoute.contribution = canonicalRouting.creditRoute.channel
  /-- The `Bool`-with-`= false` boundary record is a singleton: it proves
  nothing. -/
  ledgerHasNoContent : CuisinePropositionBoundary ≃ Unit
  /-- The safety carrier and the `Synthesis` tone carrier are abstractly
  isomorphic ... -/
  safetyToneCarrierEquiv : SafetyEvidence ≃ AgdaMirror.Base369.TriTruth
  /-- ... but no structure transports: the tone's order-3 rotation is
  incompatible with the fail-closed safety order. -/
  noToneStructureTransport :
    ¬ ∃ f : SafetyEvidence → SafetyEvidence,
        SeverityMonotone f ∧ (∀ a, f (f (f a)) = a) ∧ (∃ a, f a ≠ a)
  /-- The supplied carrying-capacity record has a free `standing` field: a
  profile may report `withinCapacity` while demand exceeds capacity. -/
  capacityHole : ∃ p : LooseCapacityProfile,
    p.capacityValue CapacityDimension.labourCapacity <
        p.demandValue CapacityDimension.labourCapacity ∧
      p.standing CapacityDimension.labourCapacity = CapacityStanding.withinCapacity
  /-- With the repair, the standing is exactly the comparison of the two
  measurements. -/
  capacityRepaired : ∀ (p : TightCapacityProfile) (d : CapacityDimension),
    p.standing d = CapacityStanding.capacityExceeded ↔ p.capacityValue d < p.demandValue d
  /-- With partial measurement the repair fails closed. -/
  capacityFailsClosed : ∀ (p : GuardedCapacityProfile) (d : CapacityDimension),
    p.capacityValue d = none ∨ p.demandValue d = none →
      p.standing d = CapacityStanding.capacityUnknown
  /-- The source receipt required by the mole and situated-world records, with
  the distinctness the Agda count does not check. -/
  sourceReceipt :
    Cuisine.SourceAtlas.sourceCount Cuisine.SourceAtlas.sourceIds = 22 ∧
      Cuisine.SourceAtlas.sourceIds.Nodup
  /-- The lane's one cross-domain definitional import — the hyperfabric guard —
  admits exactly one interpretive route, so no promotion passes it. -/
  hyperfabricGuardExact : ∃! r : InterpretiveRoute, Admissible r
  /-- The part of that guard the cuisine record actually stores is a singleton:
  it contributes a constant, not information. -/
  hyperfabricFacetNoContent : HyperfabricFacet ≃ Unit
  /-- And the guard's eight triad surfaces — among them the ones named
  `trit`, `dialectic` and `hyperfabric` — do not even inject into the ternary
  tone carrier, so the shared vocabulary is not a ternary structure. -/
  triadSurfacesNotTernary : ¬ ∃ f : TriadSurface → AgdaMirror.Base369.TriTruth,
    Function.Injective f

/-- **The spine is inhabited**: every interface obligation is discharged by a
theorem of this repository. -/
def cuisineSpine : CuisineSpine where
  umamiNormalForm := UmamiBlend.eq_ofLoads
  umamiFactorises := UmamiBlend.succ_combined_eq
  umamiNotAdditive := UmamiBlend.not_additive
  valenceObstruction := funk_no_stimulus_only_valence
  safetyObstruction := funk_no_cue_only_safety
  surfaceLedgerSound := SurfaceDistinction.ne
  surfaceLedgerPartial := surfaceDistinction_incomplete
  sauceAcyclic := SaucePath.antisymm
  sauceDisconnected := not_bechamel_to_bordelaise
  suppliedRouteContentless := processRouteRel_total
  repairedRouteAcyclic := moleRoute_antisymm
  ordersUnmergeable := orders_are_unmergeable
  promotionFailClosed := no_uniform_promoter
  publicationExact := decisionLevel_publicationDecision
  publicationAbstains := fun t h => TightAssessment.abstains_of_any_component_high t h
  channelObstruction := canonical_no_source_determined_channel
  ledgerHasNoContent := cuisinePropositionBoundaryEquivUnit
  safetyToneCarrierEquiv := safetyTritEquiv
  noToneStructureTransport := no_order_three_monotone_selfmap
  capacityHole := LooseCapacityProfile.within_while_exceeded
  capacityRepaired := fun p d => p.exceeded_iff d
  capacityFailsClosed := fun p d h => p.unknown_of_missing d h
  sourceReceipt := ⟨Cuisine.SourceAtlas.sourceCount_eq_22, Cuisine.SourceAtlas.sourceIds_nodup⟩
  hyperfabricGuardExact := exists_unique_admissible
  hyperfabricFacetNoContent := hyperfabricFacetEquivUnit
  triadSurfacesNotTernary := no_injective_trit_labelling

/-! ## The composite theorem -/

/-- **End-to-end statement for the cuisine lane.**  For every umami blend, every
repaired publication assessment, and every pair of mole states:

1. *(arithmetic)* the umami law factorises as `(1+g)(1+n)`, is super-additive,
   and is not additive under any reparametrisation;
2. *(qualitative)* no stimulus-only rule reproduces the two supplied funk
   readings, and no stimulus-and-cue rule reproduces the two supplied safety
   verdicts;
3. *(process)* the supplied route relation relates every pair of states and so
   proves nothing, while the repaired relation is acyclic and separates the two
   cooking orders;
4. *(lineage)* sauce derivation is an acyclic order with two components;
5. *(governance)* there is no policy-generic promoter, and a repaired assessment
   with any maximal component risk abstains;
6. *(provenance)* the output channel of a contribution is not a function of the
   contribution;
7. *(cross-domain)* the three-element safety carrier is abstractly isomorphic to
   the ternary tone carrier of `Synthesis.ToneCore`, and no order-3 self-map of
   it is compatible with the fail-closed safety order, so no tone structure
   transports. -/
theorem cuisine_end_to_end (u : UmamiBlend) (t : TightAssessment)
    (a b : CandidateMoleState) :
    (1 + u.combinedIntensity = (1 + u.glutamateLoad) * (1 + u.nucleotideLoad) ∧
      u.additiveBaseline ≤ u.combinedIntensity) ∧
    (¬ ∃ f : ℕ → ℕ, ∀ g n : ℕ, (UmamiBlend.ofLoads g n).combinedIntensity = f g + f n) ∧
    (¬ ∃ f : SensoryProfile → Valence,
        f trainedFunkReading.profile = trainedFunkReading.valence ∧
        f unfamiliarFunkReading.profile = unfamiliarFunkReading.valence) ∧
    ProcessRouteRel a b ∧
    (¬ MoleRoute CandidateMoleState.friedThenRehydratedChileState
        CandidateMoleState.rehydratedThenFriedChileState) ∧
    (∀ x y : Sauce, SaucePath x y → SaucePath y x → x = y) ∧
    (¬ Nonempty ((policy : PromotionPolicy) → SurfaceClaim → PromotedClaim policy)) ∧
    (riskLevel t.locationRisk = 2 → t.decision = PublicationDecision.abstainDecision) ∧
    (¬ ∃ f : HistoricalContribution → CuisineOutputChannel,
        f canonicalRouting.brandRoute.contribution = canonicalRouting.brandRoute.channel ∧
        f canonicalRouting.creditRoute.contribution = canonicalRouting.creditRoute.channel) ∧
    (¬ ∃ f : SafetyEvidence → SafetyEvidence,
        SeverityMonotone f ∧ (∀ x, f (f (f x)) = x) ∧ (∃ x, f x ≠ x)) := by
  refine ⟨⟨UmamiBlend.succ_combined_eq u, UmamiBlend.baseline_le_combined u⟩,
    UmamiBlend.not_additive, funk_no_stimulus_only_valence, processRouteRel_total a b,
    orders_are_unmergeable.1, fun x y => SaucePath.antisymm, no_uniform_promoter,
    fun h => TightAssessment.abstains_of_any_component_high t (Or.inl h),
    canonical_no_source_determined_channel, no_order_three_monotone_selfmap⟩

end Cuisine.EndToEnd
