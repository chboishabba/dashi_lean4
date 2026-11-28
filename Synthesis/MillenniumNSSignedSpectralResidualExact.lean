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



/-- Exact phase-complete cubic interaction telescope on the original
complex-coefficient carrier. It does NOT discard relative triad phase. -/
theorem complex_cubic_telescope (a b c A B C : ℂ) :
    a*b*star c - A*B*star C =
      (a-A)*b*star c + A*(b-B)*star c + A*B*star (c-C) := by
  simp only [star_sub]
  ring

/-- Certified absolute residual on an actual cubic interaction.
No assumptions of phase independence or helical-sector preservation. -/
theorem complex_cubic_error_bound (a b c A B C : ℂ) :
    ‖a*b*star c - A*B*star C‖ ≤
      ‖a-A‖*‖b‖*‖c‖ +
      ‖A‖*‖b-B‖*‖c‖ +
      ‖A‖*‖B‖*‖c-C‖ := by
  rw [complex_cubic_telescope]
  calc
    ‖(a-A)*b*star c + A*(b-B)*star c + A*B*star (c-C)‖
        ≤ ‖(a-A)*b*star c + A*(b-B)*star c‖ +
          ‖A*B*star (c-C)‖ := norm_add_le _ _
    _ ≤ (‖(a-A)*b*star c‖ + ‖A*(b-B)*star c‖) +
          ‖A*B*star (c-C)‖ := add_le_add_right (norm_add_le _ _) _
    _ = ‖a-A‖*‖b‖*‖c‖ + ‖A‖*‖b-B‖*‖c‖ +
          ‖A‖*‖B‖*‖c-C‖ := by simp [norm_mul, mul_assoc]

/-- The same exact trilinear source reverses under phase inversion at
one mode: squared norms are unchanged, while real transfer changes sign. -/
theorem complex_cubic_phase_flip (a b c : ℂ) :
    a*b*star (-c) = -(a*b*star c) := by
  simp [mul_assoc]

end DASHI.NavierStokes.SignedSpectral
