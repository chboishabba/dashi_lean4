import Mathlib
import YangMills.CMP116WilsonHalfRateClustering

open Filter MeasureTheory

/-!
# Same-H weld for the source-faithful Wilson half-rate

The remaining physical F1 obligation is not another clustering theorem.  The
R491/R551 Wilson covariance must be identified with a matrix coefficient of the
SAME reconstructed OS transfer semigroup used to define the Hamiltonian.

This record states exactly that weld and immediately transports the already
proved continuum half-rate to the same Hilbert-space semigroup.  The subsequent
continuous-time normalization and spectral-gap implication remain the standard
OS reconstruction authority boundary.
-/

namespace RequestProject.YangMills

structure SameHWilsonHalfRateWeld
    (State Obs H : Type*)
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  source : CMP116WilsonHalfRateClusteringSource State Obs
  cutoffConverges : Tendsto source.cutoffLaw atTop (𝓝 source.continuumLaw)
  transfer : ℕ → H →L[ℝ] H
  vector : Obs → H
  sameCorrelation :
    ∀ obs time,
      |probabilityCovariance source.continuumLaw
          (source.left obs time) (source.right obs time)| =
        |⟪vector obs, transfer time (vector obs)⟫_ℝ|

namespace SameHWilsonHalfRateWeld

/-- The literal R491/R551 half-rate is now a bound on the SAME reconstructed semigroup. -/
theorem semigroup_half_rate
    {State Obs H : Type*}
    [MeasurableSpace State] [TopologicalSpace State]
    [OpensMeasurableSpace State]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (weld : SameHWilsonHalfRateWeld State Obs H)
    (obs : Obs) (time : ℕ) :
    |⟪weld.vector obs, weld.transfer time (weld.vector obs)⟫_ℝ| ≤
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ time := by
  rw [← weld.sameCorrelation obs time]
  exact weld.source.continuum_half_rate weld.cutoffConverges obs time

end SameHWilsonHalfRateWeld

end RequestProject.YangMills
