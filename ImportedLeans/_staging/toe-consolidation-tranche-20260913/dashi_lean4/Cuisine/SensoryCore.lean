import Mathlib

/-!
# Cuisine layer 0: the qualitative sensory carrier

Faithful Lean mirror of the proof-relevant part of the Agda module
`DASHI.Culture.Cuisine.QualitativeSensoryCore`, together with the theorems that
the Agda file states only as *finite numerical witnesses* (`refl` on one
instance) or not at all.

Provenance of the mirrored definitions (all from the Agda source, none invented
here):

* `TasteDimension`, `AromaFamily`, `MouthfeelDimension`, `ChemestheticDimension`,
  `TemporalPhase`, `SensoryProfile` — the stimulus carrier;
* `Valence`, `Familiarity`, `InterpretationFrame`, `ObserverContext`,
  `QualitativeReading`, `DivergentReadingWitness` — the reading carrier;
* `UmamiBlend` with its three equational fields `baselineLaw`,
  `interactionLaw`, `combinedLaw`;
* `StrangenessCue`, `ProcessAssurance`, `SafetyEvidence`,
  `StinkSafetyBoundary`, `SameCueDifferentSafety`.

New content proved here:

* the closed form and the factorisation `1 + combined = (1 + g) * (1 + n)` of the
  Agda umami law, its super-additivity, and the exact condition under which the
  interaction term vanishes;
* the *non-additivity* theorem: the umami combination is not `f g + f n` for any
  single-variable `f` — the Agda file asserts non-additivity only in a comment;
* the observer-dependence theorem: a `DivergentReadingWitness` is exactly an
  obstruction to any valence assignment that depends on the stimulus alone;
* the corresponding obstruction for safety: a `SameCueDifferentSafety` witness
  rules out any safety verdict computed from stimulus and cue.

Nothing here is an empirical claim about food: the carriers are finite sets and
the umami law is the arithmetic law written in the Agda record.
-/

namespace Cuisine.SensoryCore

/-! ## Stimulus carriers -/

inductive TasteDimension
  | sweet | salty | sour | bitter | umami
  deriving DecidableEq, Fintype, Repr

inductive AromaFamily
  | floral | fruity | citrus | herbal | green | roasted | nutty | caramel
  | smoky | earthy | fungal | sulfurous | marine | animalic | fermented
  | ammoniaLike | oxidative
  deriving DecidableEq, Fintype, Repr

inductive MouthfeelDimension
  | crisp | tender | chewy | creamy | fatty | silky | grainy | slimy
  | gelatinous | dry | astringent
  deriving DecidableEq, Fintype, Repr

inductive ChemestheticDimension
  | warming | burning | cooling | tingling | numbing | nasalSharpness
  | carbonation
  deriving DecidableEq, Fintype, Repr

inductive TemporalPhase
  | aromaBeforeBite | attack | midPalate | finish | aftertaste | retronasalReturn
  deriving DecidableEq, Fintype, Repr

/-- The stimulus carrier: five independent intensity families.  Exactly the
Agda record `SensoryProfile`; in particular it is *not* a scalar score. -/
structure SensoryProfile where
  tasteIntensity : TasteDimension → ℕ
  aromaIntensity : AromaFamily → ℕ
  mouthfeelIntensity : MouthfeelDimension → ℕ
  chemestheticIntensity : ChemestheticDimension → ℕ
  temporalIntensity : TemporalPhase → ℕ

/-! ## Reading carriers -/

inductive Valence
  | attractive | neutral | aversive | ambivalent
  deriving DecidableEq, Fintype, Repr

inductive Familiarity
  | familiar | learned | unfamiliar | estranged
  deriving DecidableEq, Fintype, Repr

inductive InterpretationFrame
  | comfortFrame | celebrationFrame | prestigeFrame | medicinalFrame
  | spoilageFrame | challengeFrame | homeFrame | noveltyFrame
  deriving DecidableEq, Fintype, Repr

structure ObserverContext where
  community : String
  exposureCount : ℕ
  setting : String
  expectation : String
  familiarity : Familiarity

/-- A reading of a fixed stimulus by a fixed observer.  In the Agda source the
profile and observer are record *indices*; here they are fields, which is the
same data. -/
structure QualitativeReading where
  profile : SensoryProfile
  observer : ObserverContext
  valence : Valence
  frame : InterpretationFrame
  description : String

/-- Two readings of the *same* stimulus that disagree.  The Agda record
`DivergentReadingWitness` packages the same data; the disagreement field
`valenceDiffers` is the part the Agda version leaves implicit in its example. -/
structure DivergentReadingWitness where
  profile : SensoryProfile
  firstReading : QualitativeReading
  secondReading : QualitativeReading
  firstOnProfile : firstReading.profile = profile
  secondOnProfile : secondReading.profile = profile
  valenceDiffers : firstReading.valence ≠ secondReading.valence

/-- **Observer-dependence.**  A divergent-reading witness is exactly an
obstruction to any valence rule that reads the stimulus alone: no function of
the sensory profile can reproduce both readings.

This is the theorem behind the Agda comment "a qualitative culinary carrier is
not a scalar pleasantness score"; the Agda file supplies the witness but never
states the consequence. -/
theorem no_stimulus_only_valence (w : DivergentReadingWitness) :
    ¬ ∃ f : SensoryProfile → Valence,
        f w.firstReading.profile = w.firstReading.valence ∧
        f w.secondReading.profile = w.secondReading.valence := by
  rintro ⟨f, h₁, h₂⟩
  refine w.valenceDiffers ?_
  rw [← h₁, ← h₂, w.firstOnProfile, w.secondOnProfile]

/-- The same obstruction stated for the observer: a rule that also reads the
observer context is obstructed as soon as the two observer contexts agree. -/
theorem observers_differ_of_divergent (w : DivergentReadingWitness)
    (h : w.firstReading.observer = w.secondReading.observer) :
    ¬ ∃ f : SensoryProfile → ObserverContext → Valence,
        f w.firstReading.profile w.firstReading.observer = w.firstReading.valence ∧
        f w.secondReading.profile w.secondReading.observer = w.secondReading.valence := by
  rintro ⟨f, h₁, h₂⟩
  refine w.valenceDiffers ?_
  rw [← h₁, ← h₂, w.firstOnProfile, w.secondOnProfile, h]

/-! ## The umami law -/

/-- The Agda record `UmamiBlend`: two independent loads, an additive baseline,
a multiplicative interaction term, and their sum. -/
structure UmamiBlend where
  glutamateLoad : ℕ
  nucleotideLoad : ℕ
  additiveBaseline : ℕ
  interactionTerm : ℕ
  combinedIntensity : ℕ
  baselineLaw : additiveBaseline = glutamateLoad + nucleotideLoad
  interactionLaw : interactionTerm = glutamateLoad * nucleotideLoad
  combinedLaw : combinedIntensity = additiveBaseline + interactionTerm

namespace UmamiBlend

/-- The blend determined by its two loads.  Every `UmamiBlend` is of this
form (`eq_ofLoads`), so the record has exactly two degrees of freedom. -/
def ofLoads (g n : ℕ) : UmamiBlend where
  glutamateLoad := g
  nucleotideLoad := n
  additiveBaseline := g + n
  interactionTerm := g * n
  combinedIntensity := g + n + g * n
  baselineLaw := rfl
  interactionLaw := rfl
  combinedLaw := rfl

theorem eq_ofLoads (u : UmamiBlend) : u = ofLoads u.glutamateLoad u.nucleotideLoad := by
  obtain ⟨g, n, b, i, c, hb, hi, hc⟩ := u
  subst hb; subst hi; subst hc; rfl

/-- Closed form of the Agda laws. -/
theorem combined_eq (u : UmamiBlend) :
    u.combinedIntensity = u.glutamateLoad + u.nucleotideLoad +
      u.glutamateLoad * u.nucleotideLoad := by
  rw [u.combinedLaw, u.baselineLaw, u.interactionLaw]

/-- The multiplicative factorisation: the umami law is `(1+g)(1+n) - 1`. -/
theorem succ_combined_eq (u : UmamiBlend) :
    1 + u.combinedIntensity = (1 + u.glutamateLoad) * (1 + u.nucleotideLoad) := by
  rw [combined_eq]; ring

/-- Super-additivity: the combined intensity never falls below the additive
baseline. -/
theorem baseline_le_combined (u : UmamiBlend) :
    u.additiveBaseline ≤ u.combinedIntensity := by
  rw [u.combinedLaw]; exact Nat.le_add_right _ _

/-- The interaction is *strictly* positive exactly when both loads are: this is
the precise sense in which the record is non-additive. -/
theorem baseline_lt_combined_iff (u : UmamiBlend) :
    u.additiveBaseline < u.combinedIntensity ↔
      0 < u.glutamateLoad ∧ 0 < u.nucleotideLoad := by
  rw [u.combinedLaw, u.interactionLaw]
  constructor
  · intro h
    have hpos : 0 < u.glutamateLoad * u.nucleotideLoad := by omega
    exact ⟨Nat.pos_of_ne_zero (by rintro h0; rw [h0] at hpos; simp at hpos),
      Nat.pos_of_ne_zero (by rintro h0; rw [h0] at hpos; simp at hpos)⟩
  · rintro ⟨hg, hn⟩
    have : 0 < u.glutamateLoad * u.nucleotideLoad := Nat.mul_pos hg hn
    omega

/-- Monotonicity in the glutamate load. -/
theorem combined_mono {g g' n : ℕ} (h : g ≤ g') :
    (ofLoads g n).combinedIntensity ≤ (ofLoads g' n).combinedIntensity := by
  simp only [ofLoads]
  have : g * n ≤ g' * n := Nat.mul_le_mul_right _ h
  omega

/-- **Non-additivity.**  The umami combination law is not of the form
`f g + f n` for any single-variable function `f`.  The Agda module asserts
"an explicit non-additive interaction term" in a comment; this is the
statement, and it rules out every candidate `f`, not just the additive
baseline. -/
theorem not_additive :
    ¬ ∃ f : ℕ → ℕ, ∀ g n : ℕ, (ofLoads g n).combinedIntensity = f g + f n := by
  rintro ⟨f, hf⟩
  have h00 := hf 0 0
  have h10 := hf 1 0
  have h11 := hf 1 1
  simp only [ofLoads] at h00 h10 h11
  omega

/-- The supplied kombu/katsuobushi witness, mirroring `kombuKatsuobushiUmami`. -/
def kombuKatsuobushi : UmamiBlend := ofLoads 2 3

theorem kombuKatsuobushi_interaction : kombuKatsuobushi.interactionTerm = 6 := rfl

theorem kombuKatsuobushi_combined : kombuKatsuobushi.combinedIntensity = 11 := rfl

/-- ... and it is genuinely super-additive, not merely equal to its baseline. -/
theorem kombuKatsuobushi_superadditive :
    kombuKatsuobushi.additiveBaseline < kombuKatsuobushi.combinedIntensity := by decide

end UmamiBlend

/-! ## Strangeness, process assurance, and safety -/

inductive StrangenessCue
  | sulfurCue | animalicCue | ammoniaCue | fungalCue | marineCue
  | fermentationCue | slimeCue | bitterCue | oxidativeCue | medicinalCue
  deriving DecidableEq, Fintype, Repr

inductive ProcessAssurance
  | validatedFermentation | controlledAging | controlledCuring
  | verifiedFreshPreparation | unknownProcess
  deriving DecidableEq, Fintype, Repr

/-- The three-element safety carrier of the Agda source. -/
inductive SafetyEvidence
  | safetyVerified | safetyUnknown | safetyRejected
  deriving DecidableEq, Fintype, Repr

structure StinkSafetyBoundary where
  profile : SensoryProfile
  perceivedCue : StrangenessCue
  processStatus : ProcessAssurance
  safetyStatus : SafetyEvidence

/-- Two boundaries with the same stimulus and the same perceived cue but
different safety verdicts — the Agda `SameCueDifferentSafety`, with the
disagreement made a field. -/
structure SameCueDifferentSafety where
  first : StinkSafetyBoundary
  second : StinkSafetyBoundary
  sameProfile : first.profile = second.profile
  sameCue : first.perceivedCue = second.perceivedCue
  safetyDiffers : first.safetyStatus ≠ second.safetyStatus

/-- **Sensory cues do not determine safety.**  No verdict computed from the
stimulus and the perceived strangeness cue can agree with both boundaries; the
process assurance is a genuinely independent input. -/
theorem no_cue_only_safety (w : SameCueDifferentSafety) :
    ¬ ∃ f : SensoryProfile → StrangenessCue → SafetyEvidence,
        f w.first.profile w.first.perceivedCue = w.first.safetyStatus ∧
        f w.second.profile w.second.perceivedCue = w.second.safetyStatus := by
  rintro ⟨f, h₁, h₂⟩
  refine w.safetyDiffers ?_
  rw [← h₁, ← h₂, w.sameProfile, w.sameCue]

end Cuisine.SensoryCore
