import Mathlib

/-!
# Ordinary mixed-prime axis factor

For the actual two-prime distribution, summation over the other prime's
unit addresses yields the numerator below via the original good-prime
Hecke relation. This is the algebraic step of that calculation. It does
not establish the complex untwisted second derivative.
-/

namespace DASHI.BSD.MixedPrime

theorem axis_numerator_factor (a u p ap : ℂ)
    (h : a^2 - ap*a + p = 0) (hu : u ≠ 0) :
    a*(ap-u-u⁻¹)-(p-1) = (a-u)*(a-u⁻¹) := by
  have hh : u*u⁻¹ = 1 := mul_inv_cancel₀ hu
  linear_combination -h - hh

theorem normalized_axis_factor (a u p ap : ℂ)
    (h : a^2 - ap*a + p = 0) (ha : a ≠ 0) (hu : u ≠ 0) :
    a⁻¹*(ap-u-u⁻¹-(p-1)*a⁻¹) =
      (1-a⁻¹*u)*(1-a⁻¹*u⁻¹) := by
  calc
    a⁻¹*(ap-u-u⁻¹-(p-1)*a⁻¹) =
        a⁻¹*a⁻¹*(a*(ap-u-u⁻¹)-(p-1)) := by
          field_simp [ha, hu] <;> ring
    _ = (1-a⁻¹*u)*(1-a⁻¹*u⁻¹) := by
          rw [axis_numerator_factor a u p ap h hu]
          field_simp [ha, hu] <;> ring

/-- A unit-modulus character value cannot equal an ordinary root of
complex norm greater than one. The inverse character is retained. -/
theorem axis_numerator_ne_zero (a u : ℂ)
    (ha : 1 < ‖a‖) (hu : ‖u‖ = 1) :
    (a-u)*(a-u⁻¹) ≠ 0 := by
  have hui : ‖u⁻¹‖ = 1 := by rw [norm_inv, hu, inv_one]
  apply mul_ne_zero
  · intro h
    have eq := sub_eq_zero.mp h
    rw [eq, hu] at ha
    exact (lt_irrefl 1) ha
  · intro h
    have eq := sub_eq_zero.mp h
    rw [eq, hui] at ha
    exact (lt_irrefl 1) ha

theorem normalized_axis_ne_zero (a u : ℂ)
    (ha : 1 < ‖a‖) (hu : ‖u‖ = 1) :
    (1-a⁻¹*u)*(1-a⁻¹*u⁻¹) ≠ 0 := by
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    norm_num at ha
  have hfactor :
      (1-a⁻¹*u)*(1-a⁻¹*u⁻¹) =
        (a*a)⁻¹*((a-u)*(a-u⁻¹)) := by
    field_simp [ha0]
    <;> ring
  rw [hfactor]
  exact mul_ne_zero (inv_ne_zero (mul_ne_zero ha0 ha0))
    (axis_numerator_ne_zero a u ha hu)

/-- Actual marginal twist values survive multiplication by the Euler factor. -/
theorem nonzero_twist_survives (a u L : ℂ)
    (ha : 1 < ‖a‖) (hu : ‖u‖ = 1) (hL : L ≠ 0) :
    ((1-a⁻¹*u)*(1-a⁻¹*u⁻¹))*L ≠ 0 :=
  mul_ne_zero (normalized_axis_ne_zero a u ha hu) hL

end DASHI.BSD.MixedPrime
