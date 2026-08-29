import Cuisine.SensoryCore
import Cuisine.Lineage
import Cuisine.ProcessRoute
import Cuisine.Publication
import Cuisine.SourceAtlas

/-!
# Cuisine finite witnesses and the regression suite

Lean mirror of the finite witnesses of
`DASHI.Culture.Cuisine.QualitativeSensoryCore` (the dashi and fermented-funk
profiles, the two observers and their readings, the same-cue/different-safety
pair) and of the regression module
`DASHI.Culture.Cuisine.CuisineFormalismTests`.

Every Agda regression that has a Lean counterpart is restated here and checked;
where the Lean version is *stronger* than the Agda one the docstring says so.
The point of the file is that the divergence and separation theorems of
`Cuisine.SensoryCore` are not vacuous: concrete witnesses inhabit them.
-/

namespace Cuisine.Witnesses

open Cuisine.SensoryCore

/-! ## The dashi profile -/

def dashiTaste : TasteDimension → ℕ
  | .sweet => 0 | .salty => 2 | .sour => 0 | .bitter => 1 | .umami => 11

def dashiAroma : AromaFamily → ℕ
  | .green => 1 | .smoky => 2 | .earthy => 1 | .marine => 3 | _ => 0

def dashiMouthfeel : MouthfeelDimension → ℕ
  | .silky => 1 | _ => 0

def dashiChemesthetic : ChemestheticDimension → ℕ
  | .warming => 1 | _ => 0

def dashiTemporal : TemporalPhase → ℕ
  | .aromaBeforeBite => 2 | .attack => 2 | .midPalate => 5
  | .finish => 3 | .aftertaste => 2 | .retronasalReturn => 2

def dashiSensoryProfile : SensoryProfile :=
  ⟨dashiTaste, dashiAroma, dashiMouthfeel, dashiChemesthetic, dashiTemporal⟩

/-- Agda regression `dashiProfileUmamiRegression`. -/
theorem dashi_umami : dashiSensoryProfile.tasteIntensity .umami = 11 := rfl

/-- The dashi profile is quiet everywhere except umami: its umami intensity
strictly dominates every other taste dimension.  (Stronger than the Agda point
check.) -/
theorem dashi_umami_dominates (d : TasteDimension) (h : d ≠ .umami) :
    dashiSensoryProfile.tasteIntensity d < dashiSensoryProfile.tasteIntensity .umami := by
  cases d <;> simp_all [dashiSensoryProfile, dashiTaste]

/-! ## The fermented-funk profile and its two readings -/

def funkTaste : TasteDimension → ℕ
  | .sweet => 1 | .salty => 4 | .sour => 2 | .bitter => 2 | .umami => 6

def funkAroma : AromaFamily → ℕ
  | .fruity => 1 | .nutty => 2 | .earthy => 3 | .fungal => 5 | .sulfurous => 2
  | .animalic => 4 | .fermented => 5 | .ammoniaLike => 3 | .oxidative => 1 | _ => 0

def funkMouthfeel : MouthfeelDimension → ℕ
  | .tender => 1 | .creamy => 5 | .fatty => 5 | .silky => 3 | .grainy => 1
  | .astringent => 1 | _ => 0

def funkChemesthetic : ChemestheticDimension → ℕ
  | .nasalSharpness => 3 | _ => 0

def funkTemporal : TemporalPhase → ℕ
  | .aromaBeforeBite => 5 | .attack => 4 | .midPalate => 6
  | .finish => 5 | .aftertaste => 5 | .retronasalReturn => 6

def fermentedFunkProfile : SensoryProfile :=
  ⟨funkTaste, funkAroma, funkMouthfeel, funkChemesthetic, funkTemporal⟩

def trainedFunkObserver : ObserverContext where
  community := "aged-fermentation dining context"
  exposureCount := 40
  setting := "shared table"
  expectation := "controlled fungal and animalic complexity"
  familiarity := .learned

def unfamiliarFunkObserver : ObserverContext where
  community := "unfamiliar tasting context"
  exposureCount := 0
  setting := "first encounter"
  expectation := "mild fresh dairy aroma"
  familiarity := .unfamiliar

def trainedFunkReading : QualitativeReading where
  profile := fermentedFunkProfile
  observer := trainedFunkObserver
  valence := .attractive
  frame := .prestigeFrame
  description := "controlled funk, earthy depth, and long savoury return"

def unfamiliarFunkReading : QualitativeReading where
  profile := fermentedFunkProfile
  observer := unfamiliarFunkObserver
  valence := .aversive
  frame := .spoilageFrame
  description := "ammoniacal and animalic cues interpreted as spoilage-like"

/-- The Agda `fermentedFunkDivergentReading`, now carrying its divergence
proof. -/
def fermentedFunkDivergentReading : DivergentReadingWitness where
  profile := fermentedFunkProfile
  firstReading := trainedFunkReading
  secondReading := unfamiliarFunkReading
  firstOnProfile := rfl
  secondOnProfile := rfl
  valenceDiffers := by decide

/-- Agda regression `funkReadingContextRegression`. -/
theorem funk_first_reading :
    fermentedFunkDivergentReading.firstReading = trainedFunkReading := rfl

/-- **The obstruction is realised.**  No stimulus-only valence rule reproduces
both funk readings. -/
theorem funk_no_stimulus_only_valence :
    ¬ ∃ f : SensoryProfile → Valence,
        f trainedFunkReading.profile = trainedFunkReading.valence ∧
        f unfamiliarFunkReading.profile = unfamiliarFunkReading.valence :=
  no_stimulus_only_valence fermentedFunkDivergentReading

/-! ## Same cue, different safety -/

def controlledAgedBoundary : StinkSafetyBoundary where
  profile := fermentedFunkProfile
  perceivedCue := .ammoniaCue
  processStatus := .controlledAging
  safetyStatus := .safetyVerified

def unknownProcessBoundary : StinkSafetyBoundary where
  profile := fermentedFunkProfile
  perceivedCue := .ammoniaCue
  processStatus := .unknownProcess
  safetyStatus := .safetyUnknown

def sameFunkCueDifferentSafety : SameCueDifferentSafety where
  first := controlledAgedBoundary
  second := unknownProcessBoundary
  sameProfile := rfl
  sameCue := rfl
  safetyDiffers := by decide

/-- Agda regression `funkSafetySeparationRegression`. -/
theorem funk_first_safety :
    sameFunkCueDifferentSafety.first.safetyStatus = .safetyVerified := rfl

/-- **The obstruction is realised.**  No rule reading only stimulus and cue can
produce both verdicts, so process assurance is load-bearing. -/
theorem funk_no_cue_only_safety :
    ¬ ∃ f : SensoryProfile → StrangenessCue → SafetyEvidence,
        f controlledAgedBoundary.profile controlledAgedBoundary.perceivedCue =
          controlledAgedBoundary.safetyStatus ∧
        f unknownProcessBoundary.profile unknownProcessBoundary.perceivedCue =
          unknownProcessBoundary.safetyStatus :=
  no_cue_only_safety sameFunkCueDifferentSafety

/-! ## Remaining Agda regressions -/

open Cuisine.Lineage in
/-- Agda regressions `umamiInteractionRegression`, `umamiCombinedRegression`,
`carbonaraCreamClassificationRegression`, `mornayPathRegression`,
`bordelaisePathRegression`, `sourceCountRegression`,
`highPublicationRiskFailsClosedRegression`,
`unknownPublicationRiskFailsClosedRegression` and
`controlledPublicationRiskIsLimitedRegression`, in one block. -/
theorem agda_regressions :
    UmamiBlend.kombuKatsuobushi.interactionTerm = 6 ∧
    UmamiBlend.kombuKatsuobushi.combinedIntensity = 11 ∧
    carbonaraIngredientStatus .cream = .canonicallyExcluded ∧
    SaucePath .bechamel .mornay ∧
    SaucePath .espagnole .bordelaise ∧
    Cuisine.SourceAtlas.sourceCount Cuisine.SourceAtlas.sourceIds = 22 ∧
    Cuisine.Publication.publicationDecision .highPublicationRisk = .abstainDecision ∧
    Cuisine.Publication.publicationDecision .unknownPublicationRisk = .abstainDecision ∧
    Cuisine.Publication.publicationDecision .controlledPublicationRisk =
      .limitedProjectionDecision :=
  ⟨rfl, rfl, rfl, mornayDerivesFromBechamel, bordelaiseDerivesFromEspagnole,
    rfl, rfl, rfl, rfl⟩

open Cuisine.ProcessRoute in
/-- Agda regressions `fryThenRehydrateRouteRegression`,
`rehydrateThenFryRouteRegression`, `candidateMoleRouteRegression` and
`moleRouteEndpointsDistinct`, restated for the *repaired* route relation of
`Cuisine.ProcessRoute` (for the supplied relation they are vacuous, by
`processRouteRel_total`). -/
theorem agda_route_regressions :
    MoleRoute .rawChileState .friedThenRehydratedChileState ∧
    MoleRoute .rawChileState .rehydratedThenFriedChileState ∧
    MoleRoute .rawComponentAssemblyState .serviceStableMoleState ∧
    (CandidateMoleState.friedThenRehydratedChileState ≠
      CandidateMoleState.rehydratedThenFriedChileState) :=
  ⟨fryThenRehydrateRoute, rehydrateThenFryRoute, canonicalCandidateMoleRoute, by decide⟩

end Cuisine.Witnesses
