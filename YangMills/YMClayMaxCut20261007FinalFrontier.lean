import Mathlib
import YangMills.CMP119SelectedExactComponentReflection
import YangMills.ProjectiveCylinderPhysicalReflectionWeld
import YangMills.WilsonCylinderDeterminingSource
import YangMills.OSGramHilbertSemigroup
import YangMills.SameHWilsonMixedHalfRateWeld
import YangMills.HalfRatePhysicalTimeNormalization

/-!
# Yang--Mills max-cut frontier — 2026-10-07

This owner incorporates the stricter source/physics audit:

* A remains off the active board modulo exact-head kernel verification;
* BC certificates are tied component-by-component to designated actual E/R/B
  kernels, with finite negative samples as decisive falsifiers;
* E1 retains the explicit physical reflected-product = transported cylinder
  function same-object weld;
* DF2's generalized cylinder carrier/measure-determining machinery remains
  constructive, but no claim is made that this already reconstructs a stronger
  gauge-field topology;
* E2's null quotient, positive-definite pre-Hilbert norm, completion and
  discrete contraction semigroup remain constructive;
* F1 is upgraded to the source-correct mixed left/right R551 shape;
* F2 is merged with F1 only after the SAME half-rate-controlled Wilson vectors
  have dense real linear span in the reconstructed Hilbert sector;
* the elementary conversion from half-rate to physical energy floor is proved
  once a positive physical Euclidean time step is supplied;
* continuous-time OS reconstruction, same-H spectral transfer, source time-unit
  identification and G remain genuine downstream physical/analytic receipts.

All semantic predicates below are PARAMETERS, not fields selected by the
receipt itself.  Thus an inhabitant cannot manufacture its own notion of
"self-adjoint", "physical time", "spectral gap", or "local QFT" by choosing
those predicates to be `True`.
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

/-! ## E1: physical reflected product must be the transported cylinder product -/

/-- The projective weak-limit OS compiler after the physical same-object reflected-product weld. -/
theorem ym20261007PhysicalCylinderOSPositive
    {Ω Test : Type*} [MeasurableSpace Ω]
    (weld : PhysicalCylinderReflectionWeld Ω Test) :
    RealCountableObservableNormMomentSource.ProjectiveCylinderOSPositive
      weld.source weld.cylinderReflectedProduct :=
  physical_cylinder_os_positive weld

/-- Exact remaining E1 same-object producer. -/
def YM20261007E1PhysicalReflectionProducerExists
    (Ω Test : Type*) [MeasurableSpace Ω] : Prop :=
  Nonempty (PhysicalCylinderReflectionWeld Ω Test)

/-! ## DF2: cylinder-first continuum carrier -/

/--
The preferred generalized continuum carrier is the compact closure of the
bounded Wilson coordinate image.  This puts each cutoff law on that carrier and
produces the bounded determining source directly there.
-/
noncomputable def ym20261007CylinderContinuumSource
    {Ω : Type*} [MeasurableSpace Ω]
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i))
    (cutoffLaw : ℕ → ProbabilityMeasure Ω) :
    RealCountableObservableDeterminingSource (WilsonCylinderState raw) :=
  wilsonCylinderDeterminingSource raw hMeas cutoffLaw

/-! ## E2: analytic authority starts after the discrete Hilbert semigroup -/

/--
Remaining E2 receipt.  The semantic relations are supplied externally.  The
receipt therefore cannot define its own vacuous notion of self-adjointness,
nonnegativity, or OS reconstruction.
-/
structure YM20261007E2ContinuousTimeGeneratorReceipt
    (H Hamiltonian : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (HamiltonianSelfAdjoint : Hamiltonian → Prop)
    (HamiltonianNonnegative : Hamiltonian → Prop)
    (ReconstructedByContinuousOSSemigroup :
      (ℕ → H →L[ℝ] H) → Hamiltonian → Prop) where
  discreteTransfer : ℕ → H →L[ℝ] H
  hamiltonian : Hamiltonian
  selfAdjoint : HamiltonianSelfAdjoint hamiltonian
  nonnegative : HamiltonianNonnegative hamiltonian
  reconstructedFromSameDiscreteTransfer :
    ReconstructedByContinuousOSSemigroup discreteTransfer hamiltonian

/-- Exact remaining E2 analytic producer relative to fixed external semantics. -/
def YM20261007E2ProducerExists
    (H Hamiltonian : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (HamiltonianSelfAdjoint : Hamiltonian → Prop)
    (HamiltonianNonnegative : Hamiltonian → Prop)
    (ReconstructedByContinuousOSSemigroup :
      (ℕ → H →L[ℝ] H) → Hamiltonian → Prop) : Prop :=
  Nonempty (YM20261007E2ContinuousTimeGeneratorReceipt
    H Hamiltonian HamiltonianSelfAdjoint HamiltonianNonnegative
    ReconstructedByContinuousOSSemigroup)

/-! ## F1/F2: the SAME clustered family must be dense -/

/--
The corrected F1/F2 producer: mixed R551 clustering is welded to the same
transfer family and the real span of exactly those Wilson vectors is dense.
This is the receipt that rules out the hidden-mode counterexample.
-/
def YM20261007DenseSameFamilyHalfRateProducerExists
    (State Obs H : Type*)
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] : Prop :=
  Nonempty (SameHDenseWilsonMixedHalfRateWeld State Obs H)

/-- Any nonzero vector is detected by the same dense half-rate-controlled Wilson span. -/
theorem ym20261007SameFamilyDetectsNonzero
    {State Obs H : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (weld : SameHDenseWilsonMixedHalfRateWeld State Obs H)
    (v : H) (hv : v ≠ 0) :
    ∃ w ∈ Submodule.span ℝ (Set.range weld.vector), ⟪w, v⟫_ℝ ≠ 0 :=
  weld.detects_nonzero v hv

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

/-! ## Same-H final gap assembly authority -/

/--
Final gap-facing receipt after all generic algebraic cuts.  Every semantic
relation is fixed externally.  The E2 Hamiltonian must be generated by the SAME
discrete transfer family appearing in the dense mixed-Wilson half-rate weld,
and the standard spectral theorem must separate that Hamiltonian at the mass
floor determined by the source-certified physical time step.
-/
structure YM20261007SameHGapAssembly
    (State Obs H Hamiltonian : Type*)
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (HamiltonianSelfAdjoint : Hamiltonian → Prop)
    (HamiltonianNonnegative : Hamiltonian → Prop)
    (ReconstructedByContinuousOSSemigroup :
      (ℕ → H →L[ℝ] H) → Hamiltonian → Prop)
    (IsPhysicalStepForOneLatticeTranslation : ℝ → Prop)
    (SpectrumSeparatedBy : Hamiltonian → ℝ → Prop) where
  denseWilson : SameHDenseWilsonMixedHalfRateWeld State Obs H
  e2 : YM20261007E2ContinuousTimeGeneratorReceipt
    H Hamiltonian HamiltonianSelfAdjoint HamiltonianNonnegative
    ReconstructedByContinuousOSSemigroup
  sameDiscreteTransfer :
    e2.discreteTransfer = denseWilson.transfer
  physicalTime : YM20261007PhysicalTimeStepReceipt
    IsPhysicalStepForOneLatticeTranslation
  standardOSSpectralTransfer :
    SpectrumSeparatedBy e2.hamiltonian physicalTime.halfRateMassFloor

/-- Exact final same-H gap assembly producer before G, relative to fixed semantics. -/
def YM20261007SameHGapAssemblyExists
    (State Obs H Hamiltonian : Type*)
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (HamiltonianSelfAdjoint : Hamiltonian → Prop)
    (HamiltonianNonnegative : Hamiltonian → Prop)
    (ReconstructedByContinuousOSSemigroup :
      (ℕ → H →L[ℝ] H) → Hamiltonian → Prop)
    (IsPhysicalStepForOneLatticeTranslation : ℝ → Prop)
    (SpectrumSeparatedBy : Hamiltonian → ℝ → Prop) : Prop :=
  Nonempty (YM20261007SameHGapAssembly
    State Obs H Hamiltonian HamiltonianSelfAdjoint HamiltonianNonnegative
    ReconstructedByContinuousOSSemigroup
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
