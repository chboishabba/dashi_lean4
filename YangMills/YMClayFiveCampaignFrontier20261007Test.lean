import Mathlib
import YangMills.YMClayFiveCampaignFrontier20261007

open MeasureTheory

namespace RequestProject.YangMills

example
    {n : ℕ} [NeZero n]
    {P : Type*} [DecidableEq P]
    (crossings : Finset P) (β : ℝ) (hβ : 0 ≤ β)
    (cut : CMP119SelectedSourceExactFunctionalReflectionCut n
      (SU2CrossingBoundary P)) :
    ReflectionPositiveKernel
      (fun left right =>
        su2WilsonCrossingPlaneKernel crossings β left right *
          cut.sourceKernel left right) :=
  ym20261007BCCompleteFunctionalCompiler crossings β hβ cut

example
    {n : ℕ} [NeZero n]
    (cutoff : CMP119SelectedPhysicalCutoff n) :
    cutoff.beta = 4 * cutoff.sourceInverseCoupling :=
  ym20261007PreferredCutoffBetaNormalization cutoff

example
    {State V Hamiltonian : Type*}
    [MeasurableSpace State] [TopologicalSpace State] [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (HamiltonianSelfAdjoint HamiltonianNonnegative : Hamiltonian → Prop)
    (GeneratedByOSSemigroup :
      ∀ data : OSGramData V,
        OSSymmetricPositiveStronglyContinuousSemigroup data.Hilbert →
          Hamiltonian → Prop)
    (IsPhysicalStepForOneLatticeTranslation : ℝ → Prop)
    (SubgapSpectrum : Hamiltonian → ℝ → Prop)
    (assembly : YM20261007FiveCampaignSameHGapAssembly
      State V Hamiltonian
      HamiltonianSelfAdjoint HamiltonianNonnegative GeneratedByOSSemigroup
      IsPhysicalStepForOneLatticeTranslation SubgapSpectrum)
    (n : ℕ) :
    assembly.excitationContinuousSemigroup.toOSStronglyContinuousSemigroup.transfer
      (n : ℝ≥0) = assembly.sameFamily.excitationTransfer n :=
  assembly.excitation_continuous_nat_eq_discrete n

example
    {State V Hamiltonian : Type*}
    [MeasurableSpace State] [TopologicalSpace State] [OpensMeasurableSpace State]
    [AddCommGroup V] [Module ℝ V]
    (HamiltonianSelfAdjoint HamiltonianNonnegative : Hamiltonian → Prop)
    (GeneratedByOSSemigroup :
      ∀ data : OSGramData V,
        OSSymmetricPositiveStronglyContinuousSemigroup data.Hilbert →
          Hamiltonian → Prop)
    (IsPhysicalStepForOneLatticeTranslation : ℝ → Prop)
    (SubgapSpectrum : Hamiltonian → ℝ → Prop)
    (assembly : YM20261007FiveCampaignSameHGapAssembly
      State V Hamiltonian
      HamiltonianSelfAdjoint HamiltonianNonnegative GeneratedByOSSemigroup
      IsPhysicalStepForOneLatticeTranslation SubgapSpectrum) :
    ¬ SubgapSpectrum assembly.e2.hamiltonian
      assembly.physicalTime.halfRateMassFloor :=
  assembly.no_subgap_spectrum

end RequestProject.YangMills
