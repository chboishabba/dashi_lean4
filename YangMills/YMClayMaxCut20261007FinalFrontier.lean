import Mathlib
import YangMills.CMP119SelectedExactComponentReflection
import YangMills.ProjectiveCylinderPhysicalReflectionRepresentation
import YangMills.WilsonCylinderDeterminingSource
import YangMills.OSCenteredSameFamilyWeld
import YangMills.OSVacuumContinuousExcitation
import YangMills.OSStronglyContinuousSemigroup
import YangMills.HalfRatePhysicalTimeNormalization

/-!
# Yang--Mills max-cut frontier — 2026-10-07, centered terminal cut

This owner is the current shortest honest route.

* A remains off the active board modulo exact-head kernel verification.
* BC certificates are tied component-by-component to designated actual E/R/B
  kernels, with finite negative samples as decisive falsifiers.  Current Agda
  source still marks the source-to-literal reflection dictionaries, time-half
  classifier and E/R/B crossing audits conditional.
* E1 is representation-first: physical reflection and multiplication are chosen
  once, and the transported bounded cylinder reflected product is definitionally
  their selected observable representation.
* DF2's generalized cylinder carrier/measure-determining machinery remains
  constructive.  No stronger gauge-field topology is inferred.
* F1 uses the modern source-first Wilson carrier.  R556 makes same-family
  continuum covariance convergence compiler-owned on the exact CMP119/T5
  carrier; R573/R574/R576 isolate W1 mixed-log connected-cluster expansion and
  W3 connecting-tail control as the genuine Wilson source leaves.
* F2 is centered: the decaying vectors are dense in the vacuum-orthogonal
  excitation sector, not in a Hilbert space containing an invariant vacuum.
  Once the physical vacuum and raw carrier are fixed, this density is structural
  by continuous centering of the already-dense raw OS vectors.
* E2's null quotient, Hilbert completion and discrete contraction semigroup are
  constructive.  Continuous time is represented by an actual symmetric positive
  strongly-continuous contraction semigroup.  If it fixes the same normalized
  vacuum, it restricts canonically to the same excitation sector.
* The elementary half-rate -> `log 2 / a` energy conversion is proved once a
  positive physical Euclidean step is source-identified.
* The remaining generator and spectrum statements are external standard
  functional-analytic authority relations; they are caller-fixed and cannot be
  manufactured by defining local predicates to be `True`.
* Local/nontrivial QFT reconstruction and all-compact-simple-group extension are
  downstream.
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

/-! ## F1/F2: centered same-family Wilson/OS carrier -/

/--
Exact preferred same-family producer.  Physical mixed covariance is identified
with centered OS-vector matrix coefficients of the same completed transfer.
The normalized vacuum is fixed by that transfer.  Density of these centered
vectors in `Ω⊥` is construction-owned and is not a new source hypothesis.
-/
def YM20261007PreferredCenteredSameFamilyProducerExists
    (State V : Type*)
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V] : Prop :=
  Nonempty (SameHOSCenteredMixedHalfRateWeld State V)

/-- The source half-rate holds on the same centered OS vectors. -/
theorem ym20261007PreferredCenteredPairHalfRate
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V)
    (left right : V) :
    HalfRateMatrixBound weld.transfer
      (weld.centeredVector left) (weld.centeredVector right) :=
  weld.centered_pair_half_rate left right

/-- Centered source-first Wilson vectors are dense in the excitation sector. -/
theorem ym20261007PreferredCenteredSameFamilyDenseSector
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V) :
    Dense
      (Submodule.span ℝ
        (Set.range (weld.data.centeredRawVector
          weld.vacuum weld.vacuumNormalized)) :
        Set (vacuumOrthogonalSubmodule weld.vacuum)) :=
  weld.dense_centered_span

/-- The same discrete OS transfer preserves the centered excitation sector. -/
theorem ym20261007PreferredTransferPreservesExcitation
    {State V : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (weld : SameHOSCenteredMixedHalfRateWeld State V)
    (time : ℕ) {x : weld.data.Hilbert}
    (hx : x ∈ vacuumOrthogonalSubmodule weld.vacuum) :
    weld.transfer time x ∈ vacuumOrthogonalSubmodule weld.vacuum :=
  weld.transfer_preserves_excitation time hx

/-! ## E2: concrete C0-type OS semigroup, external generator authority only -/

/--
Concrete E2 receipt.  The continuous semigroup is an actual symmetric positive
strongly-continuous contraction semigroup on `ℝ≥0` whose integer times are
exactly the discrete OS transfer.  Only the unbounded-generator theorem is
supplied by an externally fixed authority relation.
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

/-! ## Preferred same-H centered final gap assembly -/

/--
Final gap-facing receipt on the preferred centered carrier-first route.  The
source-first Wilson covariance and the discrete OS transfer are the SAME
objects; continuous OS time extends exactly that transfer and fixes the SAME
normalized vacuum.  The externally fixed generator authority is indexed by the
selected `OSGramData`, so an inhabitant cannot redefine its meaning.
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
  sameFamily : SameHOSCenteredMixedHalfRateWeld State V
  e2 : YM20261007E2ContinuousTimeGeneratorReceipt
    sameFamily.data.Hilbert Hamiltonian
    HamiltonianSelfAdjoint HamiltonianNonnegative
    (GeneratedByOSSemigroup sameFamily.data)
  sameDiscreteTransfer : e2.discreteTransfer = sameFamily.transfer
  continuousVacuumFixed :
    ∀ t : ℝ≥0,
      e2.continuousExtension
        .toOSSymmetricPositiveStronglyContinuousSemigroup
        .toOSStronglyContinuousSemigroup.transfer t sameFamily.vacuum =
      sameFamily.vacuum
  physicalTime : YM20261007PhysicalTimeStepReceipt
    IsPhysicalStepForOneLatticeTranslation
  standardOSSpectralTransfer :
    SpectrumSeparatedBy e2.hamiltonian physicalTime.halfRateMassFloor

namespace YM20261007PreferredSameHGapAssembly

/-- The continuous extension, equipped with the same normalized fixed vacuum. -/
def continuousVacuumSemigroup
    {State V Hamiltonian : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    {HamiltonianSelfAdjoint HamiltonianNonnegative : Hamiltonian → Prop}
    {GeneratedByOSSemigroup :
      ∀ data : OSGramData V,
        OSSymmetricPositiveStronglyContinuousSemigroup data.Hilbert →
          Hamiltonian → Prop}
    {IsPhysicalStepForOneLatticeTranslation : ℝ → Prop}
    {SpectrumSeparatedBy : Hamiltonian → ℝ → Prop}
    (assembly : YM20261007PreferredSameHGapAssembly
      State V Hamiltonian HamiltonianSelfAdjoint HamiltonianNonnegative
      GeneratedByOSSemigroup IsPhysicalStepForOneLatticeTranslation
      SpectrumSeparatedBy) :
    OSVacuumStronglyContinuousSemigroup assembly.sameFamily.data.Hilbert where
  toOSSymmetricPositiveStronglyContinuousSemigroup :=
    assembly.e2.continuousExtension
      .toOSSymmetricPositiveStronglyContinuousSemigroup
  vacuum := assembly.sameFamily.vacuum
  vacuumNormalized := assembly.sameFamily.vacuumNormalized
  vacuumFixed := assembly.continuousVacuumFixed

/-- The same continuous OS semigroup restricts canonically to the excitation sector. -/
def excitationContinuousSemigroup
    {State V Hamiltonian : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    {HamiltonianSelfAdjoint HamiltonianNonnegative : Hamiltonian → Prop}
    {GeneratedByOSSemigroup :
      ∀ data : OSGramData V,
        OSSymmetricPositiveStronglyContinuousSemigroup data.Hilbert →
          Hamiltonian → Prop}
    {IsPhysicalStepForOneLatticeTranslation : ℝ → Prop}
    {SpectrumSeparatedBy : Hamiltonian → ℝ → Prop}
    (assembly : YM20261007PreferredSameHGapAssembly
      State V Hamiltonian HamiltonianSelfAdjoint HamiltonianNonnegative
      GeneratedByOSSemigroup IsPhysicalStepForOneLatticeTranslation
      SpectrumSeparatedBy) :
    OSSymmetricPositiveStronglyContinuousSemigroup
      (vacuumOrthogonalSubmodule assembly.sameFamily.vacuum) :=
  assembly.continuousVacuumSemigroup
    .toExcitationSymmetricPositiveStronglyContinuousSemigroup

end YM20261007PreferredSameHGapAssembly

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
