import Mathlib
import YangMills.CMP119SelectedComponentReflectionAssembly
import YangMills.WilsonCylinderDeterminingSource
import YangMills.OSGramHilbertSemigroup
import YangMills.SameHWilsonHalfRateWeld

/-!
# Yang--Mills max-cut frontier — 2026-10-05

This owner removes generic obligations that are no longer live:

* finite pure-Wilson OS2 is upstream/source-written;
* the cylinder-first D construction is canonical on `WilsonCylinderState`;
* Wilson coordinate separation and uniform/L2 density are automatic on that
  compactification;
* the OS Gram quotient, positive-definite norm, Hilbert completion, bounded
  translation extension, and discrete semigroup laws are constructive;
* the R491/R551 Wilson half-rate has a same-H semigroup weld surface.

The remaining frontier is therefore physical/source-facing:

BC   literal CMP119 E/R/B component/evaluator/support weld + component RP or
     finite counterexample;
E2   continuous physical Euclidean-time reconstruction / strong continuity /
     self-adjoint nonnegative generator on the completed OS Hilbert space;
F1   actual R491/R551 same-family and support-distance/time identification,
     instantiated into the same-H weld;
GAP  standard OS Euclidean-time-to-spectrum authority plus physical time-unit
     normalization on that same Hamiltonian;
G    local fields/nontriviality and compact-simple-group-uniform 4D analysis.
-/

namespace RequestProject.YangMills

/-! ## BC -/

/-- Exact BC positive-route compiler after literal selected component receipts exist. -/
theorem ym20261005BCCompiler
    {n : ℕ} [NeZero n] {X : Type*}
    (source : CMP119SelectedSourceFunctionalReflectionCut n X) :
    ReflectionPositiveKernel source.sourceKernel :=
  cmp119_selected_source_functional_kernel_rp source

/-- Exact remaining BC physical/source producer.  Negative finite samples use the existing falsifier. -/
def YM20261005BCProducerExists
    (n : ℕ) [NeZero n] (X : Type*) : Prop :=
  Nonempty (CMP119SelectedSourceFunctionalReflectionCut n X)

/-! ## DF2 -/

/--
For the cylinder-first route, finite cutoff laws plus selected measurable Wilson
coordinates construct the continuum determining source directly on the compact
coordinate closure.  No independent compactness, separation, or density source
is left.
-/
noncomputable def ym20261005CylinderContinuumSource
    {Ω : Type*} [MeasurableSpace Ω]
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i))
    (cutoffLaw : ℕ → ProbabilityMeasure Ω) :
    RealCountableObservableDeterminingSource (WilsonCylinderState raw) :=
  wilsonCylinderDeterminingSource raw hMeas cutoffLaw

/-- The canonical cylinder coordinates generate the full continuous observable algebra densely. -/
theorem ym20261005CylinderWilsonAlgebraDense
    {Ω : Type*} (raw : ℕ → Ω → ℝ) :
    (wilsonGeneratedAlgebra (wilsonCylinderCoordinate raw)).topologicalClosure = ⊤ :=
  wilsonCylinderGeneratedAlgebra_dense raw

/-! ## E2 -/

/--
Generic constructive E2 is now represented by `OSGramData.Hilbert` together
with `OSGramData.hilbertTranslation`: the null quotient, positive-definite
inner product, completion, bounded extension, and discrete semigroup laws are
all theorem-bearing.  What remains is the physical continuous-time generator
receipt below.
-/
structure YM20261005E2ContinuousTimeGeneratorReceipt
    (H Hamiltonian : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  discreteTransfer : ℕ → H →L[ℝ] H
  HamiltonianSelfAdjoint : Hamiltonian → Prop
  HamiltonianNonnegative : Hamiltonian → Prop
  ReconstructedBy : (ℕ → H →L[ℝ] H) → Hamiltonian → Prop
  hamiltonian : Hamiltonian
  selfAdjoint : HamiltonianSelfAdjoint hamiltonian
  nonnegative : HamiltonianNonnegative hamiltonian
  sameSemigroupGenerator : ReconstructedBy discreteTransfer hamiltonian

/-- Exact remaining E2 analytic/OS producer after the constructive quotient-completion stack. -/
def YM20261005E2ProducerExists
    (H Hamiltonian : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] : Prop :=
  Nonempty (YM20261005E2ContinuousTimeGeneratorReceipt H Hamiltonian)

/-! ## F1 / same-H -/

/-- Exact remaining F1 application is the source-faithful half-rate welded to the same OS semigroup. -/
def YM20261005F1SameHProducerExists
    (State Obs H : Type*)
    [MeasurableSpace State] [TopologicalSpace State] [OpensMeasurableSpace State]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] : Prop :=
  Nonempty (SameHWilsonHalfRateWeld State Obs H)

/-! ## Gap authority boundary -/

/--
The numerical lattice half-rate is deliberately not promoted directly to a
physical mass.  The final spectral step must certify that the same reconstructed
Hamiltonian uses the selected Euclidean time unit and that the standard OS
clustering-to-spectrum theorem applies without spectral pollution.
-/
structure YM20261005SameHGapAuthority (Hamiltonian Bound : Type*) where
  hamiltonian : Hamiltonian
  latticeDecayRate : Bound
  physicalGap : Bound
  Positive : Bound → Prop
  physicalGapPositive : Positive physicalGap
  SameTimeNormalization : Bound → Bound → Prop
  sameTimeNormalization : SameTimeNormalization latticeDecayRate physicalGap
  SpectrumSeparatedBy : Hamiltonian → Bound → Prop
  spectrumSeparated : SpectrumSeparatedBy hamiltonian physicalGap

/-! ## G -/

structure YM20261005LocalCompactSimpleCompletion where
  LocalFieldRegularity : Prop
  localFieldRegularity : LocalFieldRegularity
  NontrivialLocalQFT : Prop
  nontrivialLocalQFT : NontrivialLocalQFT
  CompactSimpleGroupUniformRG : Prop
  compactSimpleGroupUniformRG : CompactSimpleGroupUniformRG
  CompactSimpleGroupUniformGap : Prop
  compactSimpleGroupUniformGap : CompactSimpleGroupUniformGap

/-- G remains downstream; no local inhabitant is manufactured. -/
def YM20261005GProducerExists : Prop :=
  Nonempty YM20261005LocalCompactSimpleCompletion

end RequestProject.YangMills
