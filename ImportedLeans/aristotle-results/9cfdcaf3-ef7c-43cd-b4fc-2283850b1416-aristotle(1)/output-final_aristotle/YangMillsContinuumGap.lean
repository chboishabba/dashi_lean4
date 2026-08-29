/-!
# Yang–Mills Sprint-93 continuum-gap route (Lean transcription)

This file is a faithful Lean 4 transcription of the completed Agda module
`YMSprint93ContinuumGapAttempt.agda` (supplied in the attached source dump).

It separates, exactly as the Agda original does:

  1. **elementary / structural lemmas** we can assemble now
     (the `*From*` assembly functions below);
  2. **scoped external authorities** from Balaban / Osterwalder–Schrader / QFT,
     carried as opaque placeholder *types* (`Type`-valued fields), since they are
     references to external mathematics rather than proved content here;
  3. the **remaining genuinely new continuum-gap theorem**, which is the real
     Clay wall and is *not* discharged here.

Honesty boundary (preserved verbatim from the Agda source): the promotion
boundary `clayYangMillsPromoted` is **intentionally `false`**.  This module
supplies the *route* (the dependency skeleton showing exactly where the hard
theorem begins), **not** external Clay acceptance and **not** a completed
constructive proof.  The remaining genuinely-open obligations are recorded in
`Sprint93OpenObligations`.

Nothing in this file claims to prove the Yang–Mills mass gap.  The
placeholder fields stand for as-yet-unsupplied mathematics; assembling the
records does not establish their informal meaning.
-/

namespace YangMillsContinuumGap

/-! ## Marker propositions (unit-like records)

In the Agda source these are empty records with constructors `pos`, `lt1`, `nz`.
They are positivity / strictness markers carried structurally. -/

/-- Marker that a quantity is positive (no computational content). -/
structure Positive where
  pos ::

/-- Marker that a quantity is strictly less than one. -/
structure StrictLessThanOne where
  lt1 ::

/-- Marker that a quantity is nonzero. -/
structure NonZero where
  nz ::

/-! ## The Sprint-93 dependency skeleton

`Type`-valued fields are opaque placeholders for external/unsupplied content,
mirroring the Agda `Set`-valued fields. -/

/-- Master WC3 (Dobrushin) condition for SU(3) at `K = 11`. -/
structure MasterWC3ConditionSU3AtK11 where
  cAvgLeOne : Type
  conservativeSU3AdjointPenalty9over4 : Type
  rowSumSU3K11BelowExpMinus4 : Type
  deltaPositive : Positive

/-- Gauge-covariant Dobrushin comparison, built from the master WC3 condition. -/
structure GaugeCovariantDobrushinComparison where
  masterWC3 : MasterWC3ConditionSU3AtK11
  rowSumLTOne : StrictLessThanOne
  contractionDelta : Positive

/-- Uniform polymer activity bound obtained from the Dobrushin comparison. -/
structure UniformPolymerActivityFromDobrushin where
  dobrushin : GaugeCovariantDobrushinComparison
  uniformC : Type
  uniformM : Type
  uniformInLatticeSpacing : Type

/-- WC3 uniform cluster summability over the physical diameter. -/
structure WC3UniformClusterSummability where
  uniformActivity : UniformPolymerActivityFromDobrushin
  summableOverPhysicalDiameter : Type
  wc3UniformInA : Type

/-- Uniform connected Schwinger-function exponential decay. -/
structure UniformConnectedSchwingerDecay where
  wc3 : WC3UniformClusterSummability
  connectedClusterExpansion : Type
  exponentialDecayRatePositive : Positive

/-- Tight gauge-field continuum limit (tightness + gauge-invariant limit). -/
structure TightGaugeFieldContinuumLimit where
  tightness : Type
  subsequentialLimit : Type
  gaugeInvariantLimit : Type

/-- Osterwalder–Schrader → Wightman reconstruction data. -/
structure OSWightmanReconstruction where
  os0 : Type
  os1ReflectionPositivity : Type
  os2EuclideanCovariance : Type
  os3Regularity : Type
  wightmanFields : Type

/-- **The real Clay wall.**  Stronger than WC3: the mass-gap lower bound must
survive the continuum limit as a physical Hilbert-space gap. -/
structure ContinuumLimitMassGap where
  decay : UniformConnectedSchwingerDecay
  continuumLimit : TightGaugeFieldContinuumLimit
  osWightman : OSWightmanReconstruction
  spectralGapContinuityInActivityBound : Type
  noSpectralPollutionUnderContinuumLimit : Type
  positiveContinuumMassGap : Positive

/-- Nontriviality of the 4D SU(3) Yang–Mills measure. -/
structure Nontrivial4DSU3YangMillsMeasure where
  interacting : Type
  notGaussianFreeField : Type
  su3GaugeGroup : Type
  fourDimensionalR4 : Type

/-- The full Clay Yang–Mills candidate datum. -/
structure ClayYangMillsCandidate where
  continuumGap : ContinuumLimitMassGap
  nontrivialMeasure : Nontrivial4DSU3YangMillsMeasure
  compactSimpleGScope : Type

/-! ## Elementary assembly lemmas

These are not the hard Clay theorem; they show exactly where the hard theorem
begins by assembling the cheap structural steps. -/

/-- Build the gauge-covariant Dobrushin comparison from the master WC3 condition. -/
def gaugeCovariantDobrushinFromMaster
    (m : MasterWC3ConditionSU3AtK11) : GaugeCovariantDobrushinComparison :=
  { masterWC3 := m
    rowSumLTOne := StrictLessThanOne.lt1
    contractionDelta := m.deltaPositive }

/-- Carry the uniform polymer activity from a Dobrushin comparison together with
the (opaque) uniform constants. -/
def uniformActivityFromDobrushin
    (d : GaugeCovariantDobrushinComparison)
    (uniformC uniformM uniformInA : Type) :
    UniformPolymerActivityFromDobrushin :=
  { dobrushin := d
    uniformC := uniformC
    uniformM := uniformM
    uniformInLatticeSpacing := uniformInA }

/-- Assemble WC3 uniform cluster summability from the uniform activity bound. -/
def wc3FromUniformActivity
    (a : UniformPolymerActivityFromDobrushin)
    (summable wc3Uniform : Type) :
    WC3UniformClusterSummability :=
  { uniformActivity := a
    summableOverPhysicalDiameter := summable
    wc3UniformInA := wc3Uniform }

/-- Pass from WC3 summability to uniform connected Schwinger decay. -/
def uniformDecayFromWC3
    (wc3 : WC3UniformClusterSummability)
    (connectedClusterExpansion : Type) :
    UniformConnectedSchwingerDecay :=
  { wc3 := wc3
    connectedClusterExpansion := connectedClusterExpansion
    exponentialDecayRatePositive := Positive.pos }

/-- Assemble the continuum-limit mass-gap datum from its (mostly opaque) inputs. -/
def continuumGapFromUniformDecay
    (decay : UniformConnectedSchwingerDecay)
    (lim : TightGaugeFieldContinuumLimit)
    (os : OSWightmanReconstruction)
    (spectralContinuity noPollution : Type) :
    ContinuumLimitMassGap :=
  { decay := decay
    continuumLimit := lim
    osWightman := os
    spectralGapContinuityInActivityBound := spectralContinuity
    noSpectralPollutionUnderContinuumLimit := noPollution
    positiveContinuumMassGap := Positive.pos }

/-! ## Promotion boundary

Intentionally `false`: this file supplies the route, not external Clay
acceptance or a completed constructive proof. -/

/-- The Clay Yang–Mills promotion flag.  **Intentionally `false`.** -/
def clayYangMillsPromoted : Bool := false

/-- The promotion flag is, and is meant to be, `false`. -/
theorem clayYangMillsPromoted_false : clayYangMillsPromoted = false := rfl

/-! ## Remaining proof obligations

To be replaced by real modules / external authorities.  The presence of these
opaque fields is the honest statement that the hard mathematics is not supplied
here. -/

/-- The open obligations remaining for Sprint 93 toward the continuum mass gap. -/
structure Sprint93OpenObligations where
  balabanCMP98AveragingKernelIsProbability : Type
  balabanCMP116PolymerMassBound : Type
  masterWC3ConditionSU3AtK11 : MasterWC3ConditionSU3AtK11
  uniformCAndMFromDobrushin : Type
  wc3UniformInA : Type
  connectedSchwingerDecayFromWC3 : Type
  tightContinuumLimit : TightGaugeFieldContinuumLimit
  osWightmanReconstruction : OSWightmanReconstruction
  spectralGapContinuity : Type
  noSpectralPollution : Type
  nontrivialSU3Measure : Nontrivial4DSU3YangMillsMeasure

end YangMillsContinuumGap
