import Synthesis.NavierStokesR854RealTimeIntegratedRateConditionalExact

/-!
# R856 optimal integer-envelope cut, original R829/R854/R855 3-4-5 data

Source: DASHI Agda R829/R854/R855/R856, with same r0,L,T.
Exact source arithmetic only. The physical Galerkin flow, R853
derivative envelope, global continuation remain separate OPEN goals.
Lean 4.28 candidate; no kernel checked in this environment.
-/

namespace Synthesis
noncomputable section

def nsR856LargestPointwiseInteger : ℝ := 10065030
def nsR856FirstUnsafePointwiseInteger : ℝ := 10065031
def nsR856LargestIntegratedInteger : ℝ := 20130061
def nsR856FirstUnsafeIntegratedInteger : ℝ := 20130062

theorem nsR856LargestPointwiseCapNegative :
    nsR854InitialRate +
      (nsR856LargestPointwiseInteger * nsR854Lipschitz) * nsR854Horizon < 0 := by
  norm_num [nsR854InitialRate, nsR854Lipschitz, nsR854Horizon,
    nsR856LargestPointwiseInteger]

theorem nsR856NextPointwiseCapPositive :
    0 < nsR854InitialRate +
      (nsR856FirstUnsafePointwiseInteger * nsR854Lipschitz) * nsR854Horizon := by
  norm_num [nsR854InitialRate, nsR854Lipschitz, nsR854Horizon,
    nsR856FirstUnsafePointwiseInteger]

theorem nsR856LargestIntegratedAffineNegative :
    nsR854InitialRate * nsR854Horizon +
      ((nsR856LargestIntegratedInteger * nsR854Lipschitz) *
        nsR854Horizon * nsR854Horizon) / 2 < 0 := by
  norm_num [nsR854InitialRate, nsR854Lipschitz, nsR854Horizon,
    nsR856LargestIntegratedInteger]

theorem nsR856NextIntegratedAffinePositive :
    0 < nsR854InitialRate * nsR854Horizon +
      ((nsR856FirstUnsafeIntegratedInteger * nsR854Lipschitz) *
        nsR854Horizon * nsR854Horizon) / 2 := by
  norm_num [nsR854InitialRate, nsR854Lipschitz, nsR854Horizon,
    nsR856FirstUnsafeIntegratedInteger]

/-- Strict pointwise negativity on the ORIGINAL R854 interval,
conditional on a real envelope for the ACTUAL physical R853 rate. -/
theorem nsR856RateNegFromOriginalEnvelope
    (rate : ℝ → ℝ)
    (hSourceRate :
      ∀ t ∈ Set.Icc (0 : ℝ) nsR854Horizon,
        rate t ≤ nsR854InitialRate +
          (nsR856LargestPointwiseInteger * nsR854Lipschitz) * t) :
    ∀ t ∈ Set.Icc (0 : ℝ) nsR854Horizon, rate t < 0 := by
  intro t ht
  have hm : 0 ≤ nsR856LargestPointwiseInteger * nsR854Lipschitz := by
    norm_num [nsR856LargestPointwiseInteger, nsR854Lipschitz]
  have he := mul_le_mul_of_nonneg_left ht.2 hm
  have hs := hSourceRate t ht
  have hn := nsR856LargestPointwiseCapNegative
  linarith

#print axioms nsR856LargestPointwiseCapNegative
#print axioms nsR856LargestIntegratedAffineNegative
#print axioms nsR856RateNegFromOriginalEnvelope

end
end Synthesis
