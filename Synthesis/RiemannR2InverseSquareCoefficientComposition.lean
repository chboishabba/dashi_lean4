import Mathlib
import Synthesis.RiemannFarShellQuarticCutoff

/-!
# Inverse-square coefficient composition for the RH R2 complement

This is deliberately domain-neutral.  It isolates the real-analysis arithmetic
behind the current R2 target:

    near(t) + far(t) + gamma(t) < cluster(t).

If all three complement channels are bounded by inverse-square envelopes and
the actual cluster response has a matching inverse-square lower coefficient,
then strict coefficient slack implies the full strict response inequality.

The far-shell specialization composes the existing quartic cutoff theorem,
making the far coefficient literally 144*A.
-/

namespace Synthesis

theorem inverseSquare_threeChannel_lt_cluster
    {t near far gamma cluster cNear cFar cGamma cCluster : ℝ}
    (ht : 0 < t)
    (hNear : near ≤ cNear / (t ^ 2))
    (hFar : far ≤ cFar / (t ^ 2))
    (hGamma : gamma ≤ cGamma / (t ^ 2))
    (hCluster : cCluster / (t ^ 2) ≤ cluster)
    (hCoeff : cNear + cFar + cGamma < cCluster) :
    near + far + gamma < cluster := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hScale :
      (cNear + cFar + cGamma) / (t ^ 2) <
        cCluster / (t ^ 2) :=
    div_lt_div_of_pos_right hCoeff ht2
  have hSum :
      near + far + gamma ≤
        (cNear + cFar + cGamma) / (t ^ 2) := by
    calc
      near + far + gamma
          ≤ cNear / (t ^ 2) + cFar / (t ^ 2) + cGamma / (t ^ 2) := by
            linarith
      _ = (cNear + cFar + cGamma) / (t ^ 2) := by ring
  exact lt_of_le_of_lt hSum (lt_of_lt_of_le hScale hCluster)

theorem quarticFar_threeChannel_lt_cluster
    {A t near gamma cluster cNear cGamma cCluster : ℝ}
    (hA : 0 ≤ A)
    (ht : 1 ≤ t)
    (hNear : near ≤ cNear / (t ^ 2))
    (hGamma : gamma ≤ cGamma / (t ^ 2))
    (hCluster : cCluster / (t ^ 2) ≤ cluster)
    (hCoeff : cNear + 144 * A + cGamma < cCluster) :
    near +
      (18 * A * Real.log (t + 4) / (t ^ 4) +
        72 * A / Real.sqrt (t ^ 4)) +
      gamma < cluster := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hFar :=
    farShell_quartic_le_inverseSquare (A := A) (t := t) hA ht
  exact inverseSquare_threeChannel_lt_cluster
    htpos hNear hFar hGamma hCluster hCoeff

/-- The consumer-faithful form recovered from the vendored 8889 theorem.
Rather than comparing every channel with an absolute inverse-square cluster
coefficient, compare the complement budget's excess over the shared positive
baseline with the actual cluster surplus over that baseline. -/
theorem baselineExcess_lt_cluster
    {budget baseline excess margin cluster : ℝ}
    (hBudget : budget ≤ baseline + excess)
    (hCluster : baseline + margin ≤ cluster)
    (hExcess : excess < margin) :
    budget < cluster := by
  linarith

/-- The actual 8889 cluster surplus is quadratic in horizontal displacement.
Any complement excess below that quadratic margin closes the strict R2 scalar
comparison. -/
theorem baselineExcess_lt_cluster_quadraticMargin
    {budget baseline excess a secondMoment cluster : ℝ}
    (hBudget : budget ≤ baseline + excess)
    (hCluster :
      baseline + (Real.sqrt 2 / 2) * (a ^ 2 * secondMoment) ≤ cluster)
    (hExcess :
      excess < (Real.sqrt 2 / 2) * (a ^ 2 * secondMoment)) :
    budget < cluster :=
  baselineExcess_lt_cluster hBudget hCluster hExcess


end Synthesis
