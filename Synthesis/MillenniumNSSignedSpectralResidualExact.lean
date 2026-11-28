import Mathlib

/-! Signed spectral affine residual identities. Companion:
Agda #1551, Docs/roadmaps/Clay369PhaseCompleteEndpointMaxCut20261128.md.
Algebra only: no physical uniform budget or continuum claim.
-/
namespace DASHI.NavierStokes.SignedSpectral

theorem affine_residual (x y z p q r w₁ w₂ w₃ α β : ℝ)
    (hE : p + q + r = 0)
    (hH : x*p + y*q + z*r = 0) :
    w₁*p + w₂*q + w₃*r =
      (w₁-α-β*x)*p + (w₂-α-β*y)*q + (w₃-α-β*z)*r := by
  linear_combination α * hE + β * hH

theorem secant_numerator (x y z p q r w₁ w₂ w₃ : ℝ)
    (hE : p + q + r = 0)
    (hH : x*p + y*q + z*r = 0) :
    (z-x)*(w₁*p+w₂*q+w₃*r) =
      q*((z-x)*(w₂-w₁)-(w₃-w₁)*(y-x)) := by
  linear_combination (z*w₁-x*w₃)*hE + (w₃-w₁)*hH

theorem secant_quotient (x y z p q r w₁ w₂ w₃ : ℝ)
    (hE : p + q + r = 0)
    (hH : x*p + y*q + z*r = 0) (h : z-x ≠ 0) :
    w₁*p+w₂*q+w₃*r =
      q*(w₂-w₁-(w₃-w₁)*(y-x)/(z-x)) := by
  have hh := secant_numerator x y z p q r w₁ w₂ w₃ hE hH
  apply (mul_left_cancel₀ h)
  calc
    (z-x)*(w₁*p+w₂*q+w₃*r) =
        q*((z-x)*(w₂-w₁)-(w₃-w₁)*(y-x)) := hh
    _ = (z-x)*(q*(w₂-w₁-(w₃-w₁)*(y-x)/(z-x))) := by
      field_simp [h] <;> ring

end DASHI.NavierStokes.SignedSpectral
