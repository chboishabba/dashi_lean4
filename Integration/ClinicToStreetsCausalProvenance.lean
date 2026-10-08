import Integration.Teleodynamics

/-!
# From the Clinic to the Streets: causal provenance and psychic intrusion

This is a DASHI structural mirror of the supplied reel transcript about Lara
Sheehi's 2026 book.  Source statements are represented as attributed claims;
they are not promoted automatically to historical, clinical, political, or
causal theorem authority.

The reusable primitive is `CausalProvenanceErasure`: an interpretation can
retain intimate/intrapsychic coordinates while deleting an evidenced upstream
structural coordinate.  Psychic-intrusion and counterinsurgent-effect surfaces
are effect-typed; deliberate intent remains an independent coordinate.
-/

namespace Integration.ClinicToStreetsCausalProvenance

inductive CausalLevel
  | structural
  | institutional
  | communal
  | familial
  | interpersonal
  | intrapsychic
  deriving DecidableEq, Repr

inductive Mechanism
  | extraction
  | occupation
  | violence
  | alienation
  | normalisation
  | individualisation
  | pathologisation
  | activation
  | internalisation
  | psychicIntrusion
  | affectModulation
  | depoliticisation
  deriving DecidableEq, Repr

inductive Affect
  | fear
  | confusion
  | despair
  | exhaustion
  | anger
  | grief
  | agency
  deriving DecidableEq, Repr

inductive Direction
  | decreases
  | unchanged
  | increases
  deriving DecidableEq, Repr

inductive IntentStatus
  | unknown
  | attributed
  | established
  deriving DecidableEq, Repr

inductive ClaimKind
  | observation
  | interpretation
  | causalClaim
  | historicalClaim
  | attribution
  | normativeClaim
  | autobiographicalReport
  | recommendation
  deriving DecidableEq, Repr

inductive EpistemicStatus
  | attributed
  | reported
  | sourceChecked
  | independentlyEstablished
  deriving DecidableEq, Repr

structure SourceClaim where
  startSecond : Nat
  endSecond : Nat
  propositionLabel : String
  speakerLabel : String
  attributedSourceLabel : String
  kind : ClaimKind
  status : EpistemicStatus
  deriving Repr

def familyActivationClaim : SourceClaim where
  startSecond := 135
  endSecond := 145
  propositionLabel :=
    "family as intimate site where structural inequalities are activated, internalised, and made to seem normal"
  speakerLabel := "reel narrator"
  attributedSourceLabel := "attributed to Lara Sheehi"
  kind := .causalClaim
  status := .attributed

def therapyCounterinsurgencyClaim : SourceClaim where
  startSecond := 29
  endSecond := 38
  propositionLabel := "therapy can function as counterinsurgency"
  speakerLabel := "reel narrator"
  attributedSourceLabel := "attributed to Lara Sheehi / Fanon lineage"
  kind := .interpretation
  status := .attributed

structure CausalTrace where
  upstream : CausalLevel
  intimateSite : CausalLevel
  downstream : CausalLevel
  upstreamToSite : Mechanism
  siteToDownstream : Mechanism
  deriving Repr

def canonicalStructuralFamilyPsychicTrace : CausalTrace where
  upstream := .structural
  intimateSite := .familial
  downstream := .intrapsychic
  upstreamToSite := .activation
  siteToDownstream := .internalisation

structure ProvenanceVisibility where
  structuralVisible : Bool
  intimateVisible : Bool
  intrapsychicVisible : Bool
  deriving DecidableEq, Repr

def fullContext : ProvenanceVisibility := ⟨true, true, true⟩
def atomisedContext : ProvenanceVisibility := ⟨false, true, true⟩

structure CausalProvenanceErasure
    (before after : ProvenanceVisibility) : Prop where
  beforeStructuralVisible : before.structuralVisible = true
  afterStructuralHidden : after.structuralVisible = false
  intimateRetained : after.intimateVisible = true
  intrapsychicRetained : after.intrapsychicVisible = true

theorem canonicalAtomisingErasure :
    CausalProvenanceErasure fullContext atomisedContext := by
  constructor <;> rfl

structure ContextPreservingInterpretation where
  structuralCauseAdmissible : Bool
  intimateCauseAdmissible : Bool
  intrapsychicCauseAdmissible : Bool
  downstreamCauseErasedByUpstream : Bool
  deriving DecidableEq, Repr

def canonicalContextPreservingInterpretation : ContextPreservingInterpretation :=
  ⟨true, true, true, false⟩

structure PsychicState where
  fearPresent : Bool
  confusionPresent : Bool
  despairPresent : Bool
  causalAttributionDistorted : Bool
  actionSpaceContracted : Bool
  deriving DecidableEq, Repr

structure PsychicIntrusionTransform where
  before : PsychicState
  after : PsychicState
  attributionChanged : Bool
  actionSpaceChanged : Bool
  intent : IntentStatus
  deriving Repr

def canonicalPsychicIntrusionEffect : PsychicIntrusionTransform where
  before := ⟨false, false, false, false, false⟩
  after := ⟨true, true, true, true, true⟩
  attributionChanged := true
  actionSpaceChanged := true
  intent := .unknown

/-- Effect evidence alone does not entail deliberate intent. -/
inductive PsychicEffectImpliesEstablishedIntent : Prop

theorem psychicEffectDoesNotEstablishIntent :
    ¬ PsychicEffectImpliesEstablishedIntent := by
  intro h
  cases h

structure CounterinsurgentEffect where
  structuralSalience : Direction
  individualBlame : Direction
  collectiveAgency : Direction
  effectObserved : Bool
  deliberateIntent : IntentStatus
  deriving Repr

def canonicalCounterinsurgentEffectSignature : CounterinsurgentEffect where
  structuralSalience := .decreases
  individualBlame := .increases
  collectiveAgency := .decreases
  effectObserved := true
  deliberateIntent := .unknown

/-- An effect signature does not establish the essence of therapy as a whole. -/
inductive EffectSignatureImpliesTherapyEssence : Prop

theorem effectSignatureDoesNotEstablishTherapyEssence :
    ¬ EffectSignatureImpliesTherapyEssence := by
  intro h
  cases h

structure ReskillingTransform where
  structuralProvenanceRestored : Bool
  levelDifferentiationPreserved : Bool
  causalResolution : Direction
  confusion : Direction
  actionSpace : Direction
  deriving Repr

def canonicalReskillingTransform : ReskillingTransform :=
  ⟨true, true, .increases, .decreases, .increases⟩

/--
A generic three-axis observer matching the Agda cognitive-warfare / Plato /
trauma weld: narrative content, effective action-cone state, and provenance are
kept as separate coordinates.
-/
structure DetectorState where
  contentLabel : String
  coneContracted : Bool
  provenanceLabel : String
  deriving Repr

inductive ConeDeformationImpliesInfluence : Prop
inductive ProvenanceImpliesTruth : Prop

theorem coneDeformationDoesNotEstablishInfluence :
    ¬ ConeDeformationImpliesInfluence := by
  intro h
  cases h

theorem provenanceDoesNotEstablishTruth :
    ¬ ProvenanceImpliesTruth := by
  intro h
  cases h

structure Boundary where
  reelClaimsAreAttributed : Bool
  structuralContextCanCoexistWithIntrapsychicCause : Bool
  atomisationCanEraseUpstreamProvenance : Bool
  psychicEffectImpliesIntent : Bool
  counterinsurgentEffectImpliesTherapyEssence : Bool
  provenanceImpliesTruth : Bool
  coneDeformationImpliesHostileInfluence : Bool
  reskillingRestoresProvenanceCoordinate : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  reelClaimsAreAttributed := true
  structuralContextCanCoexistWithIntrapsychicCause := true
  atomisationCanEraseUpstreamProvenance := true
  psychicEffectImpliesIntent := false
  counterinsurgentEffectImpliesTherapyEssence := false
  provenanceImpliesTruth := false
  coneDeformationImpliesHostileInfluence := false
  reskillingRestoresProvenanceCoordinate := true

end Integration.ClinicToStreetsCausalProvenance
