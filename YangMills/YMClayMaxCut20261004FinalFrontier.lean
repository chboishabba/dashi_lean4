import Mathlib
import YangMills.YMClayMaxCut20261004
import YangMills.CMP119FunctionalResidualReflectionCut
import YangMills.FunctionalReflectionFalsifier
import YangMills.CanonicalCountableCoordinateDetermining
import YangMills.OSGramQuotientSemigroup
import YangMills.CMP116WilsonHalfRateClustering
import YangMills.WilsonUniformToL2Density

/-!
# Yang--Mills max-cut final frontier — 2026-10-04

This file consolidates the strongest theorem-bearing cuts currently available
without manufacturing the remaining physical/source receipts.

A is closed by the literal finite pure-Wilson OS2 theorem already exported by
`YMClayMaxCut20261004`.

B is stated on the correct functional boundary carrier: positivity means PSD on
every finite sampled family.  Fixed finite matrices remain valid falsifiers but
are not promoted to the full OS theorem.

C remains the literal CMP119 selected E/R/B/V same-object source-instantiation
producer.  The source repository still marks that literal complete-density
instantiation conditional, so no local inhabitant is manufactured.

D is closed abstractly on the canonical countable coordinate carrier.  For a
physical Yang--Mills state space the sole remaining D theorem is now a countable
measurable point-separating raw family (equivalently, an injective same-object
coordinate map).  Coordinatewise `tanh` then gives the bounded determining
source and D3 continuum measure automatically.

E2 has an actual algebraic OS null quotient and an actual descended discrete
translation semigroup.  The remaining E2 theorem is analytic reconstruction:
pre-Hilbert/norm completion, continuous/self-adjoint contraction extension and
the Hamiltonian generator on the same reconstructed state.

F1 uses the source-faithful R491/R551 Wilson half-rate shape directly.  The
remaining physical producer is the same-family finite Wilson estimate plus its
same-object continuum/time-distance identification.

F2 shares the main physical theorem with D: if the Wilson/cylinder algebra is
uniformly dense in bounded continuous functions, Mathlib's dense
bounded-continuous-to-L2 map transports that density to L2 automatically.
Spectral detection then follows from the existing dense-vector theorem.

G remains genuinely downstream: local-field/Wightman regularity and the
uniform group-dependent four-dimensional compact-simple-G RG/OS/gap estimates
cannot be obtained by relabelling the SU(2) construction.
-/

open MeasureTheory

namespace RequestProject.YangMills

/-! ## A: finite pure Wilson -/

/-- Terminal finite pure-Wilson OS2 theorem, re-exported on the final board. -/
theorem ym_20261004_final_a_finite_wilson_os2 :
    LiteralSU2BoundaryGaugeProjectionRPExact :=
  ym_20261004_block_a_finite_wilson_os2

/-! ## B: complete action functional RP -/

/-- Correct Block-B producer: actual residual certificates on the full boundary carrier. -/
def YM20261004BFunctionalResidualProducerExists (X : Type*) : Prop :=
  CMP119FunctionalResidualReflectionCut.FunctionalProducerExists X

/-- Any populated functional residual cut is RP on every finite sample. -/
theorem ym_20261004_b_functional_residual_rp
    {X : Type*}
    (cut : CMP119FunctionalResidualReflectionCut X) :
    ReflectionPositiveKernel cut.sourceKernel :=
  cmp119_functional_complete_residual_kernel_rp cut

/-- Wilson RP times the actual functional residual cut gives complete-action RP. -/
theorem ym_20261004_b_complete_action_rp
    {X : Type*}
    (wilsonKernel : X → X → ℝ)
    (hWilsonSymm : SymmetricKernel wilsonKernel)
    (hWilsonRP : ReflectionPositiveKernel wilsonKernel)
    (cut : CMP119FunctionalResidualReflectionCut X) :
    ReflectionPositiveKernel
      (fun x y => wilsonKernel x y * cut.sourceKernel x y) :=
  cmp119_wilson_mul_functional_complete_residual_rp
    wilsonKernel hWilsonSymm hWilsonRP cut

/-! ## C: literal CMP119 provenance -/

/-- Exact remaining Block-C source inhabitance proposition. -/
def YM20261004CSelectedSourceInstantiationExists : Prop :=
  CMP119SelectedSourceInstantiation.CMP119SelectedSourceInstantiationExists

/-! ## D: bounded determining coordinates -/

/--
The sole physical D producer after generic compactness/determining machinery:
a countable measurable real family separates the intended state space.
-/
def YM20261004DPhysicalSeparatingProducer
    {Ω : Type*} [MeasurableSpace Ω]
    (raw : ℕ → Ω → ℝ) : Prop :=
  (∀ i, Measurable (raw i)) ∧
    Function.Injective (countableObservableMap raw)

/-- Such a physical separating family gives the exact bounded determining source. -/
theorem ym_20261004_d_physical_separating_to_determining
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (cutoffLaw : ℕ → ProbabilityMeasure Ω)
    (raw : ℕ → Ω → ℝ)
    (h : YM20261004DPhysicalSeparatingProducer raw) :
    RealCountableObservableDeterminingSource.ProducerExists
      cutoffLaw (fun i x => Real.tanh (raw i x)) :=
  tanh_determining_observable_producer_exists
    cutoffLaw raw h.1 h.2

/-- On the canonical coordinate carrier, D has no remaining abstract theorem. -/
noncomputable def ym_20261004_d_canonical_determining_source
    (cutoffLaw : ℕ → ProbabilityMeasure (ℕ → ℝ)) :
    RealCountableObservableDeterminingSource (ℕ → ℝ) :=
  canonicalCountableCoordinateDeterminingSource cutoffLaw

/-! ## E2: OS quotient and translation semigroup -/

/-- Exact remaining analytic E2 producer after algebraic quotient/semigroup descent. -/
structure YM20261004E2AnalyticReconstructionSource
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  transfer : ℕ → H →L[ℝ] H
  transferZero : transfer 0 = ContinuousLinearMap.id ℝ H
  transferAdd : ∀ s t, transfer (s + t) = (transfer s).comp (transfer t)
  contractive : ∀ t, ‖transfer t‖ ≤ 1
  symmetric : ∀ t (x y : H),
    ⟪x, transfer t y⟫_ℝ = ⟪transfer t x, y⟫_ℝ
  positive : ∀ t (x : H), 0 ≤ ⟪x, transfer t x⟫_ℝ

/-- Existence of the analytic reconstructed transfer-semigroup package. -/
def YM20261004E2AnalyticReconstructionProducerExists : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H),
    Nonempty (YM20261004E2AnalyticReconstructionSource H)

/-! ## F1: source-faithful Wilson clustering -/

/-- Exact source-faithful F1 producer after removing the obsolete printed-J seam. -/
def YM20261004F1WilsonHalfRateProducerExists
    {Ω Obs : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] : Prop :=
  CMP116WilsonHalfRateClusteringSource.ProducerExists
    (Ω := Ω) (Obs := Obs)

/-! ## F2: Wilson density / cyclicity -/

/-- Exact uniform-observable F2 producer.  Its L2 consequence is theorem-bearing. -/
def YM20261004F2WilsonUniformDensityProducerExists
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    (wilsonSubmodule : Submodule ℝ (Ω →ᵇ ℝ)) : Prop :=
  WilsonUniformDensityProducerExists wilsonSubmodule

/-- Uniform Wilson density transports automatically to L2 density. -/
theorem ym_20261004_f2_uniform_to_L2_density
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [BorelSpace Ω] [SecondCountableTopology Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    (wilsonSubmodule : Submodule ℝ (Ω →ᵇ ℝ))
    (hDense : YM20261004F2WilsonUniformDensityProducerExists wilsonSubmodule) :
    (wilsonSubmodule.map
      (BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ).toLinearMap).topologicalClosure = ⊤ :=
  wilson_uniform_dense_to_L2_dense μ wilsonSubmodule hDense

/-! ## G: local fields and all compact simple groups -/

/--
Final group/local-QFT producer boundary.  This deliberately records actual
remaining mathematics instead of asserting a source-free group promotion.
-/
structure YM20261004CompactSimpleLocalQFTProducer where
  LocalFieldRegularity : Prop
  localFieldRegularity : LocalFieldRegularity
  CompactSimpleGroupUniformRG : Prop
  compactSimpleGroupUniformRG : CompactSimpleGroupUniformRG
  ContinuumOSReconstruction : Prop
  continuumOSReconstruction : ContinuumOSReconstruction
  PositivePhysicalGap : Prop
  positivePhysicalGap : PositivePhysicalGap

/-- No local inhabitant is manufactured for the final G producer. -/
def YM20261004GProducerExists : Prop :=
  Nonempty YM20261004CompactSimpleLocalQFTProducer

end RequestProject.YangMills
