import Synthesis.RiemannR2InverseSquareCoefficientComposition

namespace Synthesis

example
    {t near far gamma cluster cNear cFar cGamma cCluster : ℝ}
    (ht : 0 < t)
    (hNear : near ≤ cNear / (t ^ 2))
    (hFar : far ≤ cFar / (t ^ 2))
    (hGamma : gamma ≤ cGamma / (t ^ 2))
    (hCluster : cCluster / (t ^ 2) ≤ cluster)
    (hCoeff : cNear + cFar + cGamma < cCluster) :
    near + far + gamma < cluster :=
  inverseSquare_threeChannel_lt_cluster
    ht hNear hFar hGamma hCluster hCoeff

example
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
      gamma < cluster :=
  quarticFar_threeChannel_lt_cluster
    hA ht hNear hGamma hCluster hCoeff

end Synthesis
