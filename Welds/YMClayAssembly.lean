import RequestProject.YangMills.Clay.MassGapAssembly

namespace Welds.YMClayAssembly

open scoped InnerProductSpace
open MeasureTheory
open RequestProject.YangMills.BIDI
open RequestProject.YangMills.Clay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/--
The active source-to-Clay assembly.

For every cutoff Hamiltonian, the physical spectral representation and the
already-owned source covariance decay are enough to build the BIDI
`ClusteringSpectralData`.  The retained Clay assembly then transports the
resulting uniform finite vacuum gap through the physical graph limit and the
YM/OS same-object evolution weld.

No source estimate, graph-limit theorem, or OS identification is invented here:
those remain exactly the displayed physical inputs.
-/
theorem massGapOfSourceCovariance
    {Δ : ℝ} (hΔ : 0 < Δ)
    (C : CutoffFamily E)
    (S : ∀ n, SpectralRepresentation (C.ham n) (C.vacuum n))
    (covInf : ∀ n, (C.ham n).domain → ℝ → ℂ)
    (clusterConst : ∀ n, (C.ham n).domain → ℝ)
    (hos : ∀ n (psi : (C.ham n).domain),
      ⟪C.vacuum n, (psi : E)⟫_ℂ = 0 → ∀ t : ℝ, 0 ≤ t →
        ∫ x, Real.exp (-(t * x)) ∂((S n).spectralMeasure psi)
          ≤ ‖covInf n psi t‖)
    (hsrc : ∀ n (psi : (C.ham n).domain), ∀ t : ℝ, 0 ≤ t →
      ‖covInf n psi t‖ ≤ clusterConst n psi * Real.exp (-(Δ * t)))
    {Hos : E →ₗ.[ℂ] E}
    (W : OSWeld C.limitHam Hos) :
    MassGapConclusion Hos C.vac Δ := by
  refine clay_mass_gap_of_inputs C hΔ (fun n => ?_) W
  exact hasVacuumFormGap_of_clustering
    (ClusteringSpectralData.ofSourceBound
      (S n) (covInf n) (clusterConst n) (hos n) (hsrc n))

/-- The Row-A1/form route exposed on the active weld surface. -/
theorem massGapOfEnergyForms
    {Δ : ℝ} (hΔ : 0 < Δ)
    (F : EnergyFormFamily E Δ)
    (C : CutoffFamily E)
    (hfam : C.ham = F.ham)
    (hvac : C.vacuum = F.vacuum)
    {Hos : E →ₗ.[ℂ] E}
    (W : OSWeld C.limitHam Hos) :
    MassGapConclusion Hos C.vac Δ :=
  clay_mass_gap_of_energyForms hΔ F C hfam hvac W

end Welds.YMClayAssembly

#print axioms Welds.YMClayAssembly.massGapOfSourceCovariance
#print axioms Welds.YMClayAssembly.massGapOfEnergyForms
