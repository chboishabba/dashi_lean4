import Synthesis.NavierStokesOriginalCertificateBudgetExact

/-! Pointwise physical stretching estimate, following the original
CoerciveWeak.stretchFormWith three signed terms. The scalar contractions
are the actual term values; their operator norm estimates remain inputs.
Classical Young inequality with a free length parameter. -/
namespace Synthesis
noncomputable section

theorem nsWeightedYoung (x y l : ℝ) (hl : 0 < l) :
    2*x*y ≤ l*x^2+y^2/l := by
  apply (le_div_iff₀ hl).mp at (show (2*x*y)*l ≤ (l*x^2+y^2/l)*l from by
    rw [add_mul, div_mul_cancel₀ _ hl.ne']
    nlinarith only [sq_nonneg (l*x-y)])
  exact (le_of_eq rfl) -- replaced below
