import Mathlib

/-!
# Cuisine layer 6: channel-dependent provenance routing

Lean mirror of `DASHI.Culture.Cuisine.ProvenanceRoutingBridge` together with the
`HistoricalFoodRelation` / `HistoricalMemoryLane` / `HistoricalContribution`
vocabulary it reuses from `DASHI.Culture.Cuisine.SituatedMoleWorld`.

The Agda module records the intended reading in comments — "the same provenance
contribution may be routed differently by channel", so "national canonisation
does not imply origin, and visible authenticity does not imply
credit/rights/value return" — and in a four-flag `Bool` ledger, which by
`Cuisine.LedgerPattern` carries no proof content.

New content proved here:

* `no_source_determined_channel` — a routing whose three routes share a source
  but carry different channels is exactly an obstruction to any function that
  computes the channel from the contribution.  That is the formal content of
  "channel-dependent";
* `channels_pairwise_distinct` for the canonical routing, so the obstruction is
  non-vacuous;
* `IsEmpty (HistoricalRelationProvesExclusiveOwnership _)` — transcribing the
  Agda empty family.  This holds *by construction*: it records the absence of an
  inference rule from historical relation to exclusive ownership, and is not a
  derivation of that absence from anything else.  It is listed here so the
  distinction is on the record.
-/

namespace Cuisine.Provenance

/-! ## Historical contribution vocabulary -/

inductive HistoricalFoodRelation
  | introducedIngredientRelation | coercedProductionRelation
  | appropriatedTechniqueRelation | marketAdoptionRelation
  | eliteCodificationRelation | householdAdaptationRelation
  | religiousReframingRelation | nationalCanonisationRelation
  | tourismRebrandingRelation | communityReclamationRelation
  deriving DecidableEq, Fintype, Repr

inductive HistoricalMemoryLane
  | indigenousFoodMemoryLane | afroMexicanFoodMemoryLane | colonialInstitutionLane
  | pacificTradeLane | regionalEcologyLane | householdMarketLane
  | nationalHeritageLane | diasporaFoodMemoryLane
  deriving DecidableEq, Fintype, Repr

structure HistoricalContribution where
  contributorOrCommunity : String
  memoryLane : HistoricalMemoryLane
  relation : HistoricalFoodRelation
  contributionReading : String
  sourceReading : String
  deriving DecidableEq

/-! ## Output channels and routing -/

inductive CuisineOutputChannel
  | publicBrand | authenticity | historicalCredit | economicBenefit
  | representationRights | ownershipClaim | communityMemory
  deriving DecidableEq, Fintype, Repr

structure RoutedCulinaryProvenance where
  contribution : HistoricalContribution
  channel : CuisineOutputChannel
  routedReading : String

/-- The Agda `ChannelDependentCuisineRouting`: three routes off one source. -/
structure ChannelDependentCuisineRouting where
  source : HistoricalContribution
  brandRoute : RoutedCulinaryProvenance
  creditRoute : RoutedCulinaryProvenance
  rightsRoute : RoutedCulinaryProvenance
  brandUsesSameSource : brandRoute.contribution = source
  creditUsesSameSource : creditRoute.contribution = source
  rightsUsesSameSource : rightsRoute.contribution = source

namespace ChannelDependentCuisineRouting

/-- **Channel-dependence, proved.**  If two of the routes off a single source
carry different channels, then no function of the contribution alone can produce
the channel: brand visibility, historical credit and representation rights are
independent outputs of the same provenance fact. -/
theorem no_source_determined_channel (r : ChannelDependentCuisineRouting)
    (h : r.brandRoute.channel ≠ r.creditRoute.channel) :
    ¬ ∃ f : HistoricalContribution → CuisineOutputChannel,
        f r.brandRoute.contribution = r.brandRoute.channel ∧
        f r.creditRoute.contribution = r.creditRoute.channel := by
  rintro ⟨f, h₁, h₂⟩
  exact h (by rw [← h₁, ← h₂, r.brandUsesSameSource, r.creditUsesSameSource])

end ChannelDependentCuisineRouting

/-- The Afro-Mexican memory boundary of `SituatedMoleWorld`, transcribed as the
shared source of the canonical routing. -/
def afroMexicanMemoryBoundary : HistoricalContribution where
  contributorOrCommunity :=
    "Afro-Mexican women and communities; no homogeneous spokesperson asserted"
  memoryLane := .afroMexicanFoodMemoryLane
  relation := .communityReclamationRelation
  contributionReading :=
    "Afro-Mexican culinary memory, labour, identity, and resistance remain explicit."
  sourceReading := "bounded by attributed review and future community-led evidence"

/-- A canonical routing of that contribution to three different channels. -/
def canonicalRouting : ChannelDependentCuisineRouting where
  source := afroMexicanMemoryBoundary
  brandRoute := ⟨afroMexicanMemoryBoundary, .publicBrand, "visible in national branding"⟩
  creditRoute := ⟨afroMexicanMemoryBoundary, .historicalCredit, "credited in historical accounts"⟩
  rightsRoute :=
    ⟨afroMexicanMemoryBoundary, .representationRights, "who may speak, and on what occasion"⟩
  brandUsesSameSource := rfl
  creditUsesSameSource := rfl
  rightsUsesSameSource := rfl

theorem channels_pairwise_distinct :
    canonicalRouting.brandRoute.channel ≠ canonicalRouting.creditRoute.channel ∧
    canonicalRouting.creditRoute.channel ≠ canonicalRouting.rightsRoute.channel ∧
    canonicalRouting.brandRoute.channel ≠ canonicalRouting.rightsRoute.channel := by
  refine ⟨by decide, by decide, by decide⟩

/-- The obstruction is realised: for the canonical routing there is genuinely no
contribution-only channel rule. -/
theorem canonical_no_source_determined_channel :
    ¬ ∃ f : HistoricalContribution → CuisineOutputChannel,
        f canonicalRouting.brandRoute.contribution = canonicalRouting.brandRoute.channel ∧
        f canonicalRouting.creditRoute.contribution = canonicalRouting.creditRoute.channel :=
  canonicalRouting.no_source_determined_channel channels_pairwise_distinct.1

/-- Stronger: no rule can even reproduce all three channels at once, and this is
independent of which function one tries. -/
theorem no_three_channel_rule :
    ¬ ∃ f : HistoricalContribution → CuisineOutputChannel,
        f canonicalRouting.brandRoute.contribution = canonicalRouting.brandRoute.channel ∧
        f canonicalRouting.creditRoute.contribution = canonicalRouting.creditRoute.channel ∧
        f canonicalRouting.rightsRoute.contribution = canonicalRouting.rightsRoute.channel := by
  rintro ⟨f, h₁, h₂, -⟩
  exact canonical_no_source_determined_channel ⟨f, h₁, h₂⟩

/-! ## The ownership non-promotion rule -/

inductive CuisineOwnershipPromotion
  | historicalRelationObserved
  deriving DecidableEq, Fintype, Repr

/-- The Agda empty family.  There is no constructor: no rule promotes an
observed historical relation to a claim of exclusive ownership. -/
inductive HistoricalRelationProvesExclusiveOwnership : CuisineOwnershipPromotion → Prop

/-- Uninhabited by construction.  This records the *absence of an inference
rule*; it is not derived from any prior principle. -/
theorem historicalRelationDoesNotProveExclusiveOwnership
    (p : CuisineOwnershipPromotion) : ¬ HistoricalRelationProvesExclusiveOwnership p := by
  rintro ⟨⟩

end Cuisine.Provenance
