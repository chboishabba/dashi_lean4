import Mathlib
import YangMills.YMClayFiveCampaignFrontier20261007

open MeasureTheory

namespace RequestProject.YangMills

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
      IsPhysicalStepForOneLatticeTranslation SubgapSpectrum) :
    ¬ SubgapSpectrum assembly.e2.hamiltonian
      assembly.physicalTime.halfRateMassFloor :=
  assembly.no_subgap_spectrum

end RequestProject.YangMills
