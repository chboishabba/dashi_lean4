import Synthesis.NavierStokesOriginalCertificateBudgetExact

/-! Pointwise physical stretching estimate, following the original
CoerciveWeak.stretchFormWith three signed terms. The scalar contractions
are the actual term values; their operator norm estimates remain inputs.
Classical Young inequality with a free length parameter. -/
namespace Synthesis
noncomputable section

theorem nsWeightedYoung (x y l : ℝ) (hl : 0 < l) :
    2*x*y ≤ l*x^2+y^2/l := by
  have he : l*x^2+y^2/l = (l^2*x^2+y^2)/l := by
    field_simp
  rw [he]
  apply (le_div_iff₀ hl).2
  nlinarith only [sq_nonneg (l*x-y)]

/-- The three signed contractions in stretchFormWith are kept distinct.
S bounds strain, M the mean vorticity-gradient contraction, N the
remaining gradient contraction (including its 1/2 factor).
The two mixed products use independent Young lengths. -/
theorem nsStretchLower
    (strain mean wave S M N u g o l m : ℝ)
    (hl : 0 < l) (hm : 0 < m)
    (hs : strain ≤ S*o^2)
    (hc : -(M*u*o) ≤ mean)
    (hw : -(N*u*g) ≤ wave) :
    -(S*o^2 + l*o^2/2 + (M*u)^2/(2*l)
      + m*g^2/2 + (N*u)^2/(2*m)) ≤ -strain+mean+wave := by
  have h1 := nsWeightedYoung o (M*u) l hl
  have h2 := nsWeightedYoung g (N*u) m hm
  have he1 : (M*u)^2/l/2 = (M*u)^2/(2*l) := by ring
  have he2 : (N*u)^2/m/2 = (N*u)^2/(2*m) := by ring
  rw [← he1, ← he2]
  nlinarith only [h1,h2,hs,hc,hw]

/-- Physical decay r^-2 for strain is absorbed by the actual exterior
radius, without applying the estimate at the axis. -/
theorem nsExteriorStrainBound (D R r : ℝ)
    (hD : 0 ≤ D) (hR : 0 ≤ R) (hr : R ≤ r) :
    D/(1+r)^2 ≤ D/(1+R)^2 := by
  have h1 : 0 < (1+R)^2 := by positivity
  have h2 : 0 < (1+r)^2 := by
    have : 0 < 1+r := by linarith
    positivity
  apply (div_le_div_iff₀ h2 h1).2
  have hsq : (1+R)^2 ≤ (1+r)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ 2+r+R by linarith)]
  exact mul_le_mul_of_nonneg_left hsq hD

end
end Synthesis
