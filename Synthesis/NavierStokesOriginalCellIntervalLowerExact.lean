import Synthesis.NavierStokesPhysicalCoefficientExact

/-! Outward interval endpoints for the literal five-channel density.
The cell bounds and the Hardy budget must be supplied from the actual
profile; this theorem only consumes them. No profile is asserted. -/
namespace Synthesis

theorem nsBaseDensityIntervalLower
    (d z c w dd dz x2 xc x1 xo x0 : ℝ)
    (dl du zl zu cu wu ddu dzu H a : ℝ)
    (hd : dl ≤ d) (hd' : d ≤ du)
    (hz : zl ≤ z) (hz' : z ≤ zu)
    (hc : 0 ≤ c) (hc' : c ≤ cu)
    (hw : 0 ≤ w) (hw' : w ≤ wu)
    (hdd : dd ≤ ddu) (hdz : dz ≤ dzu) (hdu : 0 ≤ dzu)
    (hHardy : x0^2 ≤ H*(x2^2+xc^2+x1^2+xo^2))
    (h1 : a ≤ dl-cu) (h2 : a ≤ 1-du)
    (h3 : a ≤ 1/4-zu) (h4 : a ≤ zl-ddu-cu*wu) :
    (a-dzu*H)*(x2^2+xc^2+x1^2+xo^2) ≤
      nsBaseDensity d z c w dd dz x2 xc x1 xo x0 := by
  have hcw : c*w ≤ cu*wu :=
    mul_le_mul hc' hw' hw (hc.trans hc')
  apply nsBaseDensityLower
  · linarith
  · linarith
  · linarith
  · linarith
  · calc
      dz*x0^2 ≤ dzu*x0^2 := mul_le_mul_of_nonneg_right hdz (sq_nonneg _)
      _ ≤ dzu*(H*(x2^2+xc^2+x1^2+xo^2)) :=
        mul_le_mul_of_nonneg_left hHardy hdu
      _ = _ := by ring

end Synthesis
