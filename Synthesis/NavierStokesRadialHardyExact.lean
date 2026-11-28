import Synthesis.NavierStokesPhysicalStretchExact

/-! Classical radial Hardy ground-state transform, with boundary flux
retained. The original weighted carrier must supply the integration by
parts identity and endpoint flux; no pointwise Hardy inequality is used. -/
namespace Synthesis
noncomputable section

theorem nsRadialHardyDensity (r u du : ℝ) :
    (r*du+u/2)^2 = r^2*du^2-u^2/4+(u^2+2*r*u*du)/2 := by
  ring

theorem nsWeightedHardyDensity (r u du w dw : ℝ) :
    w*(r*du+u/2)^2 =
      w*r^2*du^2-(w+2*r*dw)*u^2/4+
      (w*u^2+r*dw*u^2+2*r*w*u*du)/2 := by
  ring

/-- Integration of the square identity, with the upper minus lower
boundary flux as an explicit signed term. -/
theorem nsRadialHardyFromFlux (energy mass flux squareMass : ℝ)
    (hs : 0 ≤ squareMass)
    (hi : squareMass = energy-mass/4+flux/2) :
    mass ≤ 4*energy+2*flux := by linarith

/-- Weighted version: W is the integral of (w+2*r*w') u². -/
theorem nsWeightedHardyFromFlux (energy weightedMass flux squareMass : ℝ)
    (hs : 0 ≤ squareMass)
    (hi : squareMass = energy-weightedMass/4+flux/2) :
    weightedMass ≤ 4*energy+2*flux := by linarith

/-- Retain the axis/exterior seam: opposite orientations cancel only
when their actual traces agree. -/
theorem nsHardySeam (eI eE mI mE axis left right infinity : ℝ)
    (hi : mI ≤ 4*eI+2*(left-axis))
    (he : mE ≤ 4*eE+2*(infinity-right))
    (hs : left = right) :
    mI+mE ≤ 4*(eI+eE)+2*(infinity-axis) := by linarith

/-- Integrated five-channel absorption using the Hardy estimate, not
an invalid pointwise bound on velocity by its derivatives. -/
theorem nsIntegratedHardyCoercivity
    (a dz e2 ec e1 eo mass density flux : ℝ)
    (hdz : 0 ≤ dz) (he2 : 0 ≤ e2) (hec : 0 ≤ ec) (heo : 0 ≤ eo)
    (hm : mass ≤ 4*e1+2*flux)
    (hbase : a*(e2+ec+e1+eo)-dz*mass ≤ density) :
    (a-4*dz)*(e2+ec+e1+eo)-2*dz*flux ≤ density := by
  have h1 := mul_le_mul_of_nonneg_left hm hdz
  have h2 := mul_nonneg hdz (show 0 ≤ e2+ec+eo by linarith)
  nlinarith only [h1,h2,hbase]

/-- Interior and exterior block budgets, keeping mixed-sign cross terms. -/
theorem nsInteriorExteriorCoercivity
    (cI cE debt eI eE bI bE cross : ℝ)
    (heI : 0 ≤ eI) (heE : 0 ≤ eE)
    (hi : cI*eI ≤ bI) (he : cE*eE ≤ bE)
    (hx : -(debt*(eI+eE)) ≤ cross) :
    (min cI cE-debt)*(eI+eE) ≤ bI+bE+cross := by
  have h1 := mul_le_mul_of_nonneg_right (min_le_left cI cE) heI
  have h2 := mul_le_mul_of_nonneg_right (min_le_right cI cE) heE
  nlinarith only [h1,h2,hi,he,hx]

end
end Synthesis
