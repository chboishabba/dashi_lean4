import Dashi.Biology.IBSMonashAdaptiveSequencingExact

namespace Dashi.Biology.IBSMonashLongHorizonAdaptiveExact

inductive LongHorizonEvidenceRole where
  | longTermPersonalisationBurden | negativeGeneticStratification | digitalBrainGutDelivery
  deriving Repr, DecidableEq

structure LongHorizonEvidence where
  sourceReference : String
  role : LongHorizonEvidenceRole
  paidObservation : String
  promotionBlocked : String
  deriving Repr, DecidableEq

def canonicalMonashLongHorizonAtlas : List LongHorizonEvidence := [
  { sourceReference := "Silva et al. 2025 DOI 10.1111/nmo.70116",
    role := .longTermPersonalisationBurden,
    paidObservation := "long-term symptom control can coexist with personalized/minimally restrictive diets; persistent strict restriction carried lower food-related QoL",
    promotionBlocked := "retrospective follow-up does not prove personalization caused long-term control" },
  { sourceReference := "Silva et al. 2026 DOI 10.1002/ueg2.70173",
    role := .negativeGeneticStratification,
    paidObservation := "single SI hypomorphic-variant carriage did not distinguish short- or long-term FODMAP outcome in the studied cohort",
    promotionBlocked := "null association does not establish universal genetic irrelevance" },
  { sourceReference := "Anderson et al. 2025 DOI 10.14309/ajg.0000000000002921",
    role := .digitalBrainGutDelivery,
    paidObservation := "digital gut-directed hypnotherapy has randomized controlled outcome evidence against active control",
    promotionBlocked := "digital delivery is not definitionally equivalent to therapist delivery or a CNS-only mechanism" }
]

inductive SingleSIHypomorphPredictsFODMAPOutcomePermission : Prop
inductive MoreRestrictionAlwaysBetterPermission : Prop
inductive DigitalGDHEqualsTherapistGDHPermission : Prop

theorem singleSIHypomorphDoesNotPredictFODMAPOutcome : SingleSIHypomorphPredictsFODMAPOutcomePermission → False := by intro h; cases h
theorem moreRestrictionIsNotAlwaysBetter : MoreRestrictionAlwaysBetterPermission → False := by intro h; cases h
theorem digitalGDHDoesNotDefinitionallyEqualTherapistGDH : DigitalGDHEqualsTherapistGDHPermission → False := by intro h; cases h

structure BurdenSensitiveAdaptiveObjective where
  symptomBenefitRetained : Bool
  foodRelatedQoLRetained : Bool
  restrictionBurdenRetained : Bool
  accessDeliveryBurdenRetained : Bool
  informationValueRetained : Bool
  numericUtilityInvented : Bool
  deriving Repr, DecidableEq

def canonicalBurdenSensitiveAdaptiveObjective : BurdenSensitiveAdaptiveObjective :=
  { symptomBenefitRetained := true, foodRelatedQoLRetained := true,
    restrictionBurdenRetained := true, accessDeliveryBurdenRetained := true,
    informationValueRetained := true, numericUtilityInvented := false }

structure LongHorizonParetoNode where
  label : String
  route : String
  paidReference : String
  residual : String
  nextAcquisition : String
  authorityBoundary : String
  deriving Repr, DecidableEq

def canonicalMonashLongHorizonPareto : List LongHorizonParetoNode := [
  { label := "minimal-effective dietary restriction", route := "externalKnowledgeComparison",
    paidReference := "Silva 2025 DOI 10.1111/nmo.70116",
    residual := "retrospective long-term follow-up cannot identify optimal reintroduction policy",
    nextAcquisition := "prospective randomized personalization/reintroduction strategy with symptom, nutrition and food-related QoL outcomes",
    authorityBoundary := "less restriction is not automatically better if symptom control deteriorates; optimize jointly" },
  { label := "SI genotype negative-stratification replication", route := "externalKnowledgeComparison",
    paidReference := "Silva 2026 DOI 10.1002/ueg2.70173",
    residual := "double-carriers were too few and cohort was retrospective",
    nextAcquisition := "larger prospective genotype-by-diet interaction study with enzyme activity/phenotype where feasible",
    authorityBoundary := "single-variant null result is not universal absence of SI effects" },
  { label := "digital versus therapist brain-gut delivery", route := "experimentalDesign",
    paidReference := "Anderson 2025 DOI 10.14309/ajg.0000000000002921 plus Peters 2016 DOI 10.1111/apt.13706",
    residual := "delivery mode, therapist contact, adherence, expectancy and cost are partially entangled",
    nextAcquisition := "head-to-head pragmatic effectiveness/cost/access trial with common outcome and mechanism panel",
    authorityBoundary := "delivery convenience and mechanistic efficacy are distinct coordinates" }
]

structure MonashLongHorizonBoundary where
  nullSIResultRetained : Bool
  longTermBurdenRetained : Bool
  digitalDeliverySeparatedFromMechanism : Bool
  strictRestrictionIsUniversalGoal : Bool
  parentOwnerReference : String
  deriving Repr, DecidableEq

def canonicalMonashLongHorizonBoundary : MonashLongHorizonBoundary :=
  { nullSIResultRetained := true, longTermBurdenRetained := true,
    digitalDeliverySeparatedFromMechanism := true, strictRestrictionIsUniversalGoal := false,
    parentOwnerReference := "IBSMonashAdaptiveSequencingExact" }

end Dashi.Biology.IBSMonashLongHorizonAdaptiveExact
