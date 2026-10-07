import Mathlib
import YangMills.CMP119SelectedExactComponentReflection
import YangMills.ProjectiveCylinderPhysicalReflectionRepresentation
import YangMills.WilsonCylinderDeterminingSource
import YangMills.OSGramRawDenseSameFamilyWeld
import YangMills.OSStronglyContinuousSemigroup
import YangMills.HalfRatePhysicalTimeNormalization

/-!
# Yang--Mills max-cut frontier — 2026-10-07, post-cylinder cut

This owner is the current shortest honest route.

* A remains off the active board modulo exact-head kernel verification.
* BC certificates are tied component-by-component to designated actual E/R/B
  kernels, with finite negative samples as decisive falsifiers.
* E1 is representation-first: physical reflection and multiplication are chosen
  once, and the transported bounded cylinder reflected product is definitionally
  their selected observable representation.  The old duplicate-function
  equality receipt is removed.
* DF2's generalized cylinder carrier/measure-determining machinery remains
  constructive.  No stronger gauge-field topology is inferred.
* E2's null quotient, positive-definite pre-Hilbert norm, Hilbert completion and
  discrete contraction semigroup are constructive.  The continuous-time input
  is now an ACTUAL strongly-continuous symmetric positive contraction semigroup
  on nonnegative real time, agreeing with the constructed discrete family.
* F1/F2 use the modern source-first Wilson carrier: R556 makes SAME-family
  continuum covariance convergence compiler-owned once the finite covariance is
  the exact CMP119/T5 covariance; R574/R576 reduce the genuine Wilson source
  bill to W1 mixed-log connected-cluster expansion and W3 connecting-tail
  control, with bounded-test/time/order semantics downstream.  On the preferred
  OS route this observable carrier IS the raw pre-Hilbert carrier, so its OS
  vector image is dense by quotient surjectivity plus completion and no separate
  F2 density axiom survives.
* The elementary half-rate -> `log 2 / a` energy conversion is proved once a
  positive physical Euclidean step is source-identified.
* The remaining generator and spectrum statements are external standard
  functional-analytic authority relations; they are caller-fixed and cannot be
  manufactured by defining local predicates to be `True`.
* G remains downstream.
-/

namespace RequestProject.YangMills

/-! ## BC: exact actual-component source cut -/

/-- Strict BC compiler: every selected actual E/R/B component kernel is certified. -/
theorem ym20261007BCExactCompiler
    {n : ℕ} [NeZero n] {X : Type*}
    (cut : CMP119SelectedSourceExactFunctionalReflectionCut n X) :
    ReflectionPositiveKernel cut.sourceKernel :=
  cut.source_kernel_rp

/-- Exact remaining BC producer. One finite negative component sample falsifies that route. -/
def YM20261007BCProducerExists
    (n : ℕ) [NeZero n] (X : Type*) : Prop :=
  Nonempty (CMP119SelectedSourceExactFunctionalReflectionCut n X)

/-! ## E1: representation-first physical cylinder OS positivity -/

/--
The physical reflected product is computed from one selected representation of
physical reflection and multiplication; there is no second arbitrary cylinder
product and hence no artificial same-function equality field.
-/
theorem ym20261007PhysicalCylinderOSPositiveFromRepresentation
    {Ω Obs : Type*} [MeasurableSpace Ω]
    (rep : PhysicalCylinderObservableRepresentation Ω Obs) :
    RealCountableObservableNormMomentSource.ProjectiveCylinderOSPositive
      rep.source rep.reflectedProduct :=
  rep.projectiveOSPositive

/-- Exact remaining E1 producer: the intended physical observable representation itself. -/
def YM20261007E1PhysicalRepresentationProducerExists
    (Ω Obs : Type*) [MeasurableSpace Ω] : Prop :=
  Nonempty (PhysicalCylinderObservableRepresentation Ω Obs)

/-! ## DF2: cylinder-first continuum carrier -/

/--
The preferred generalized continuum carrier is the compact closure of the
bounded Wilson coordinate image.  Each cutoff law is put on that carrier and
the bounded determining source is produced directly there.
-/
noncomputable def ym20261007CylinderContinuumSource
    {Ω : Type*} [MeasurableSpace Ω]
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i))
    (cutoffLaw : ℕ → ProbabilityMeasure Ω) :
    RealCountableObservableDeterminingSource (WilsonCylinderState raw) :=
  wilsonCylinderDeterminingSource raw hMeas cutoffLaw

/-! ## F1/F2: choose the preferred source-first Wilson family as the OS raw carrier -/

/--
Preferred same-family producer.  The modern source-first Wilson observable
carrier is literally the OS raw test space `V`, its transfer is the completed OS
transfer, and its continuum covariance is the corresponding matrix coefficient.
R556 already owns same-family covariance convergence on the exact CMP119/T5
carrier; R574/R576 isolate W1/W3 upstream source analysis.  Density follows
from the OS construction and is not an additional hypothesis here.
-/
def YM20261007PreferredSameFamilyProducerExists
    (State V : Type*)
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V] : Prop :=
  Nonempty (SameHOSRawMixedHalfRateWeld State V)

/-- Preferred same-family data automatically supplies the older dense-weld interface. -/
noncomputable theorem ym20261007PreferredSameFamilyDenseWeld
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSRawMixedHalfRateWeld State V) :
    SameHDenseWilsonMixedHalfRateWeld State V weld.data.Hilbert :=
  weld.toDenseSameFamilyWeld

/-- Every nonzero vector is detected by that same automatically dense source-first Wilson/OS carrier. -/
theorem ym20261007PreferredSameFamilyDetectsNonzero
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSRawMixedHalfRateWeld State V)
    (v : weld.data.Hilbert) (hv : v ≠ 0) :
    ∃ w ∈ Submodule.span ℝ (Set.range weld.data.rawVector), ⟪w, v⟫_ℝ ≠ 0 :=
  weld.toDenseSameFamilyWeld.detects_nonzero v hv

/-! ## E2: concrete C0-type OS semigroup, external generator authority only -/

/--
Concrete E2 receipt.  The continuous semigroup is no longer hidden behind an
opaque relation: it is an actual symmetric positive strongly-continuous
contraction semigroup on `ℝ≥0` whose integer times are exactly the discrete OS
transfer.  Only the unbounded-generator theorem is supplied by an externally
fixed authority relation.
-/
structure YM20261007E2ContinuousTimeGeneratorReceipt
    (H Hamiltonian : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (HamiltonianSelfAdjoint : Hamiltonian → Prop)
    (HamiltonianNonnegative : Hamiltonian → Prop)
    (GeneratedByOSSemigroup :
      OSSymmetricPositiveStronglyContinuousSemigroup H → Hamiltonian → Prop) where
  discreteTransfer : ℕ → H →L[ℝ] H
  continuousExtension :
    OSSymmetricPositiveStronglyContinuousSemigroupExtension discreteTransfer
  hamiltonian : Hamiltonian
  selfAdjoint : HamiltonianSelfAdjoint hamiltonian
  nonnegative : HamiltonianNonnegative hamiltonian
  generatedBySameOSSemigroup :
    GeneratedByOSSemigroup
      continuousExtension.toOSSymmetricPositiveStronglyContinuousSemigroup
      hamiltonian

/-- Exact remaining E2 producer relative to fixed generator semantics. -/
def YM20261007E2ProducerExists
    (H Hamiltonian : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (HamiltonianSelfAdjoint : Hamiltonian → Prop)
    (HamiltonianNonnegative : Hamiltonian → Prop)
    (GeneratedByOSSemigroup :
      OSSymmetricPositiveStronglyContinuousSemigroup H → Hamiltonian → Prop) : Prop :=
  Nonempty (YM20261007E2ContinuousTimeGeneratorReceipt
    H Hamiltonian HamiltonianSelfAdjoint HamiltonianNonnegative
    GeneratedByOSSemigroup)

/-! ## Physical time normalization -/

/-- Elementary spectral normalization: half-rate over step `a` means energy at least `log 2 / a`. -/
theorem ym20261007HalfRatePhysicalEnergyFloor
    (a E : ℝ) (ha : 0 < a)
    (hDecay : Real.exp (-a * E) ≤ (1 / 2 : ℝ)) :
    Real.log 2 / a ≤ E :=
  energy_ge_log_two_div_step_of_half_rate a E ha hDecay

/--
Fail-closed physical time receipt relative to an externally fixed source
predicate saying which real number is the Euclidean time of one lattice
translation.
-/
structure YM20261007PhysicalTimeStepReceipt
    (IsPhysicalStepForOneLatticeTranslation : ℝ → Prop) where
  step : ℝ
  stepPositive : 0 < step
  sameSourceTimeUnit : IsPhysicalStepForOneLatticeTranslation step

namespace YM20261007PhysicalTimeStepReceipt

/-- Mass floor attached to this externally certified physical step. -/
def halfRateMassFloor
    {IsPhysicalStepForOneLatticeTranslation : ℝ → Prop}
    (time : YM20261007PhysicalTimeStepReceipt
      IsPhysicalStepForOneLatticeTranslation) : ℝ :=
  Real.log 2 / time.step

/-- The certified physical step turns the lattice half-rate into its physical energy floor. -/
theorem energy_ge_halfRateMassFloor
    {IsPhysicalStepForOneLatticeTranslation : ℝ → Prop}
    (time : YM20261007PhysicalTimeStepReceipt
      IsPhysicalStepForOneLatticeTranslation)
    (E : ℝ)
    (hDecay : Real.exp (-time.step * E) ≤ (1 / 2 : ℝ)) :
    time.halfRateMassFloor ≤ E :=
  energy_ge_log_two_div_step_of_half_rate
    time.step E time.stepPositive hDecay

end YM20261007PhysicalTimeStepReceipt

/-- Exact remaining source time-unit producer relative to the fixed source predicate. -/
def YM20261007PhysicalTimeStepProducerExists
    (IsPhysicalStepForOneLatticeTranslation : ℝ → Prop) : Prop :=
  Nonempty (YM20261007PhysicalTimeStepReceipt
    IsPhysicalStepForOneLatticeTranslation)

/-! ## Preferred same-H final gap assembly -/

/--
Final gap-facing receipt on the preferred carrier-first route.  The dense
source-first Wilson family and the discrete OS transfer are the SAME objects by
construction.  The externally fixed generator authority is indexed by the
selected `OSGramData`, so choosing the source carrier selects an authority
instance but cannot redefine its meaning.
-/
structure YM20261007PreferredSameHGapAssembly
    (State V Hamiltonian : Type*)
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (HamiltonianSelfAdjoint : Hamiltonian → Prop)
    (HamiltonianNonnegative : Hamiltonian → Prop)
    (GeneratedByOSSemigroup :
      ∀ data : OSGramData V,
        OSSymmetricPositiveStronglyContinuousSemigroup data.Hilbert →
          Hamiltonian → Prop)
    (IsPhysicalStepForOneLatticeTranslation : ℝ → Prop)
    (SpectrumSeparatedBy : Hamiltonian → ℝ → Prop) where
  sameFamily : SameHOSRawMixedHalfRateWeld State V
  e2 : YM20261007E2ContinuousTimeGeneratorReceipt
    sameFamily.data.Hilbert Hamiltonian
    HamiltonianSelfAdjoint HamiltonianNonnegative
    (GeneratedByOSSemigroup sameFamily.data)
  sameDiscreteTransfer : e2.discreteTransfer = sameFamily.transfer
  physicalTime : YM20261007PhysicalTimeStepReceipt
    IsPhysicalStepForOneLatticeTranslation
  standardOSSpectralTransfer :
    SpectrumSeparatedBy e2.hamiltonian physicalTime.halfRateMassFloor

/-- Exact preferred same-H assembly producer before local/all-group completion. -/
def YM20261007PreferredSameHGapAssemblyExists
    (State V Hamiltonian : Type*)
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (HamiltonianSelfAdjoint : Hamiltonian → Prop)
    (HamiltonianNonnegative : Hamiltonian → Prop)
    (GeneratedByOSSemigroup :
      ∀ data : OSGramData V,
        OSSymmetricPositiveStronglyContinuousSemigroup data.Hilbert →
          Hamiltonian → Prop)
    (IsPhysicalStepForOneLatticeTranslation : ℝ → Prop)
    (SpectrumSeparatedBy : Hamiltonian → ℝ → Prop) : Prop :=
  Nonempty (YM20261007PreferredSameHGapAssembly
    State V Hamiltonian
    HamiltonianSelfAdjoint HamiltonianNonnegative GeneratedByOSSemigroup
    IsPhysicalStepForOneLatticeTranslation SpectrumSeparatedBy)

/-! ## G remains downstream and semantic predicates are fixed externally -/

structure YM20261007LocalCompactSimpleCompletion
    (LocalFieldRegularity : Prop)
    (NontrivialLocalQFT : Prop)
    (CompactSimpleGroupUniformRG : Prop)
    (CompactSimpleGroupUniformGap : Prop) where
  localFieldRegularity : LocalFieldRegularity
  nontrivialLocalQFT : NontrivialLocalQFT
  compactSimpleGroupUniformRG : CompactSimpleGroupUniformRG
  compactSimpleGroupUniformGap : CompactSimpleGroupUniformGap

/-- No local/all-group inhabitant is manufactured; all target propositions are caller-fixed. -/
def YM20261007GProducerExists
    (LocalFieldRegularity : Prop)
    (NontrivialLocalQFT : Prop)
    (CompactSimpleGroupUniformRG : Prop)
    (CompactSimpleGroupUniformGap : Prop) : Prop :=
  Nonempty (YM20261007LocalCompactSimpleCompletion
    LocalFieldRegularity NontrivialLocalQFT
    CompactSimpleGroupUniformRG CompactSimpleGroupUniformGap)

end RequestProject.YangMills
