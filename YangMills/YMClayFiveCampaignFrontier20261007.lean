import Mathlib
import YangMills.YMClayMaxCut20261007FinalFrontier
import YangMills.CMP119SelectedCompleteFunctionalRP
import YangMills.CMP119SelectedPhysicalCutoff
import YangMills.OSCenteredExcitationHalfRate
import YangMills.SameHSubgapSpectralWindow

open MeasureTheory

/-!
# Yang--Mills five-campaign max-cut frontier — 2026-10-07

This capstone replaces the older six-producer bookkeeping by the five live
mathematical campaigns that remain after the centered-vacuum and excitation
restriction cuts.

1. BC: actual CMP119 E/R/B source supports, reflection geometry and crossing
   kernels, ending in functional RP or an explicit finite negative sample.  If
   the strict selected source cut is inhabited, the literal Wilson crossing
   kernel and the exact E/R/B/V residual now assemble directly into one complete
   functional RP kernel on the same boundary carrier.
2. C/E1: same physical source law and observable representation.  On the
   preferred Lean finite route the reference measure is now canonical literal
   product Haar and beta is definitionally `4/g^2`; the source bridge only has
   to identify the selected CMP119/CMP109 history with those same values.
3. F1: W1 mixed-log connected-cluster expansion plus W3 absolute connecting
   tail and physical support/time semantics.
4. E2 + GEN/GAP: physical C0 extension of the same OS transfer, the genuine
   unbounded nonnegative self-adjoint generator theorem, physical Euclidean
   time, and standard functional calculus.  The no-pollution implication is no
   longer assumed: any subgap spectrum must produce a nonzero spectral transfer
   window, and the dense centered half-rate theorem proves such a window cannot
   exist.
5. G: same-theory local/nontrivial Wightman reconstruction and uniform extension
   to every compact simple gauge group.

No source-conditional BC/W1/W3 theorem is promoted here.
-/

namespace RequestProject.YangMills

/-! ## BC: successful source extraction reaches the complete functional crossing kernel -/

/--
The strict selected E/R/B/V source realization Schur-multiplies directly with
the literal Wilson crossing kernel.  No separate post-BC assembly theorem
remains on the preferred route.
-/
theorem ym20261007BCCompleteFunctionalCompiler
    {n : ℕ} [NeZero n]
    {P : Type*} [DecidableEq P]
    (crossings : Finset P)
    (β : ℝ) (hβ : 0 ≤ β)
    (cut : CMP119SelectedSourceExactFunctionalReflectionCut n
      (SU2CrossingBoundary P)) :
    ReflectionPositiveKernel
      (fun left right =>
        su2WilsonCrossingPlaneKernel crossings β left right *
          cut.sourceKernel left right) :=
  cmp119_selected_complete_crossing_functional_rp
    crossings β hβ cut

/-! ## C: preferred finite physical cutoff has canonical Haar and beta -/

/-- Preferred C-level finite producer after removing arbitrary Haar and beta choices. -/
def YM20261007PreferredPhysicalCutoffProducerExists
    (n : ℕ) [NeZero n] : Prop :=
  Nonempty (CMP119SelectedPhysicalCutoff n)

/-- The literal positive Wilson beta is compiler-related to the same source inverse coupling. -/
theorem ym20261007PreferredCutoffBetaNormalization
    {n : ℕ} [NeZero n]
    (cutoff : CMP119SelectedPhysicalCutoff n) :
    cutoff.beta = 4 * cutoff.sourceInverseCoupling :=
  cutoff.beta_eq_four_mul_sourceInverseCoupling

/-- The preferred finite law is the exact selected-source Gibbs law over canonical product Haar. -/
noncomputable def ym20261007PreferredFiniteGibbsLaw
    {n : ℕ} [NeZero n]
    (cutoff : CMP119SelectedPhysicalCutoff n) :
    ProbabilityMeasure (SU2TorusLinks (2 * n)) :=
  cutoff.gibbsLaw

/-! ## Physical time conversion shared by the final spectral cut -/

namespace YM20261007PhysicalTimeStepReceipt

/-- Forget only the source predicate, retaining the exact positive physical step. -/
def toWilsonPhysicalTimeStep
    {IsPhysicalStepForOneLatticeTranslation : ℝ → Prop}
    (time : YM20261007PhysicalTimeStepReceipt
      IsPhysicalStepForOneLatticeTranslation) : WilsonPhysicalTimeStep where
  step := time.step
  stepPositive := time.stepPositive

/-- The old source-certified and generic Wilson mass-floor definitions coincide exactly. -/
@[simp] theorem toWilsonPhysicalTimeStep_halfRateMassFloor
    {IsPhysicalStepForOneLatticeTranslation : ℝ → Prop}
    (time : YM20261007PhysicalTimeStepReceipt
      IsPhysicalStepForOneLatticeTranslation) :
    time.toWilsonPhysicalTimeStep.halfRateMassFloor =
      time.halfRateMassFloor := by
  rfl

end YM20261007PhysicalTimeStepReceipt

/-! ## GAP: spectral separation is derived from the minimal spectral-window authority -/

/--
Preferred same-H final gap assembly after the no-pollution compiler.

`SubgapSpectrum` is fixed by the caller and represents the genuine spectral
statement for the selected unbounded Hamiltonian.  The external spectral
calculus is required only to prove that such a subgap spectrum would produce a
nonzero projection with the standard transfer lower bound.  The contradiction
with centered Wilson half-rate is proved internally.
-/
structure YM20261007FiveCampaignSameHGapAssembly
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
    (SubgapSpectrum : Hamiltonian → ℝ → Prop) where
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
  spectralCalculusSubgapWindow :
    SubgapSpectrum e2.hamiltonian physicalTime.halfRateMassFloor →
      Nonempty (SameHSubgapTransferWindow
        sameFamily physicalTime.toWilsonPhysicalTimeStep)

namespace YM20261007FiveCampaignSameHGapAssembly

/-- The continuous extension equipped with the same normalized fixed vacuum. -/
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
    {SubgapSpectrum : Hamiltonian → ℝ → Prop}
    (assembly : YM20261007FiveCampaignSameHGapAssembly
      State V Hamiltonian HamiltonianSelfAdjoint HamiltonianNonnegative
      GeneratedByOSSemigroup IsPhysicalStepForOneLatticeTranslation
      SubgapSpectrum) :
    OSVacuumStronglyContinuousSemigroup assembly.sameFamily.data.Hilbert where
  toOSSymmetricPositiveStronglyContinuousSemigroup :=
    assembly.e2.continuousExtension
      .toOSSymmetricPositiveStronglyContinuousSemigroup
  vacuum := assembly.sameFamily.vacuum
  vacuumNormalized := assembly.sameFamily.vacuumNormalized
  vacuumFixed := assembly.continuousVacuumFixed

/-- The same continuous semigroup restricts constructively to `Ω⊥`. -/
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
    {SubgapSpectrum : Hamiltonian → ℝ → Prop}
    (assembly : YM20261007FiveCampaignSameHGapAssembly
      State V Hamiltonian HamiltonianSelfAdjoint HamiltonianNonnegative
      GeneratedByOSSemigroup IsPhysicalStepForOneLatticeTranslation
      SubgapSpectrum) :
    OSSymmetricPositiveStronglyContinuousSemigroup
      (vacuumOrthogonalSubmodule assembly.sameFamily.vacuum) :=
  assembly.continuousVacuumSemigroup
    .toExcitationSymmetricPositiveStronglyContinuousSemigroup

/--
At every integer time, the continuously reconstructed excitation transfer is
literally the same restricted operator as the discrete centered OS transfer.
This removes a final same-H adapter seam from the spectral argument.
-/
theorem excitation_continuous_nat_eq_discrete
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
    {SubgapSpectrum : Hamiltonian → ℝ → Prop}
    (assembly : YM20261007FiveCampaignSameHGapAssembly
      State V Hamiltonian HamiltonianSelfAdjoint HamiltonianNonnegative
      GeneratedByOSSemigroup IsPhysicalStepForOneLatticeTranslation
      SubgapSpectrum)
    (n : ℕ) :
    assembly.excitationContinuousSemigroup.toOSStronglyContinuousSemigroup.transfer
      (n : ℝ≥0) = assembly.sameFamily.excitationTransfer n := by
  ext x
  apply Subtype.ext
  change
    assembly.e2.continuousExtension
        .toOSSymmetricPositiveStronglyContinuousSemigroup
        .toOSStronglyContinuousSemigroup.transfer (n : ℝ≥0) (x : assembly.sameFamily.data.Hilbert) =
      assembly.sameFamily.transfer n (x : assembly.sameFamily.data.Hilbert)
  rw [assembly.e2.continuousExtension.discreteAgreement n,
    assembly.sameDiscreteTransfer]

/--
The spectral gap statement is now a theorem: any claimed subgap spectrum would
produce a forbidden nonzero same-H transfer window.
-/
theorem no_subgap_spectrum
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
    {SubgapSpectrum : Hamiltonian → ℝ → Prop}
    (assembly : YM20261007FiveCampaignSameHGapAssembly
      State V Hamiltonian HamiltonianSelfAdjoint HamiltonianNonnegative
      GeneratedByOSSemigroup IsPhysicalStepForOneLatticeTranslation
      SubgapSpectrum) :
    ¬ SubgapSpectrum assembly.e2.hamiltonian
      assembly.physicalTime.halfRateMassFloor := by
  intro hSubgap
  exact no_sameH_subgap_transfer_window
    assembly.sameFamily assembly.physicalTime.toWilsonPhysicalTimeStep
    (assembly.spectralCalculusSubgapWindow hSubgap)

end YM20261007FiveCampaignSameHGapAssembly

/-- Exact remaining same-H producer after internalizing no-pollution. -/
def YM20261007FiveCampaignSameHGapAssemblyExists
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
    (SubgapSpectrum : Hamiltonian → ℝ → Prop) : Prop :=
  Nonempty (YM20261007FiveCampaignSameHGapAssembly
    State V Hamiltonian HamiltonianSelfAdjoint HamiltonianNonnegative
    GeneratedByOSSemigroup IsPhysicalStepForOneLatticeTranslation
    SubgapSpectrum)

end RequestProject.YangMills
