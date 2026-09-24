/-
# Source covariance decay -> vacuum form gap

The retained BIDI development already proves both halves of equation (25):
`ClusteringSpectralData.ofSourceBound` turns a physical spectral representation
plus a continuum covariance decay estimate into clustering spectral data, and
`hasVacuumFormGap_of_clustering` turns that data into the vacuum-complement
quadratic-form gap.

This weld exposes their composition as one consumer-facing theorem so the live
proof ledger does not incorrectly list covariance-decay -> form-gap as missing
infrastructure.  It does not manufacture the physical spectral representation;
that same-object inhabitant remains explicit when it is not already supplied by
the physical OS/reconstruction lane.
-/
import RequestProject.YangMills.BIDI.ClusteringGap

namespace Welds.YMSourceClusteringGap

open MeasureTheory
open scoped InnerProductSpace
open RequestProject.YangMills.VacuumSectorSpectralGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Equation (25), exposed as a single theorem:

continuum covariance exponential decay + the physical spectral representation
of that same Hamiltonian imply the vacuum-sector form gap with the same mass.
-/
theorem vacuumFormGapOfSourceCovariance
    {H : E →ₗ.[ℂ] E} {vac : E} {m : ℝ}
    (S : RequestProject.YangMills.BIDI.SpectralRepresentation H vac)
    (covInf : H.domain → ℝ → ℂ)
    (c : H.domain → ℝ)
    (hos : ∀ psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 → ∀ t : ℝ, 0 ≤ t →
      ∫ x, Real.exp (-(t * x)) ∂(S.spectralMeasure psi) ≤ ‖covInf psi t‖)
    (hsrc : ∀ psi : H.domain, ∀ t : ℝ, 0 ≤ t →
      ‖covInf psi t‖ ≤ c psi * Real.exp (-(m * t))) :
    HasVacuumFormGap H vac m := by
  exact RequestProject.YangMills.BIDI.hasVacuumFormGap_of_clustering
    (RequestProject.YangMills.BIDI.ClusteringSpectralData.ofSourceBound
      S covInf c hos hsrc)

#print axioms vacuumFormGapOfSourceCovariance

end Welds.YMSourceClusteringGap
