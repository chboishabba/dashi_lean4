import Mathlib

/-! Local real-coordinate eliminated-pivot calculus.  This is a conditional
calculus weld, not an identification of the selected CMP99 source. -/
namespace CMP99Pivot

theorem pivot_bidi (a b c : ℝ) (ha : a ≠ 0) :
    a * c + b = 0 ↔ c = -b / a := by
  constructor
  · intro h
    apply (eq_div_iff ha).2
    linarith [mul_comm a c]
  · intro h
    have hh := (eq_div_iff ha).1 h
    linarith [mul_comm a c]

theorem pivot_derivative {a b : ℝ → ℝ} {t da db : ℝ}
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t)
    (hn : a t ≠ 0) :
    HasDerivAt (fun s => -b s / a s)
      ((b t * da - a t * db) / (a t)^2) t := by
  convert hb.neg.div ha hn using 1 <;> ring

/-- Differentiate the actual constraint a*c+b=0 twice, without dividing
until the nonzero pivot has been supplied. -/
theorem second_pivot_bidi (a da dda c dc ddc ddb : ℝ) (ha : a ≠ 0) :
    a * ddc + 2 * da * dc + dda * c + ddb = 0 ↔
      ddc = -(2 * da * dc + dda * c + ddb) / a := by
  constructor
  · intro h
    apply (eq_div_iff ha).2
    linarith [mul_comm a ddc]
  · intro h
    have hh := (eq_div_iff ha).1 h
    linarith [mul_comm a ddc]

theorem pivot_defect (a₀ a₁ b₀ b₁ : ℝ)
    (h₀ : a₀ ≠ 0) (h₁ : a₁ ≠ 0) :
    -b₁ / a₁ - (-b₀ / a₀) =
      (b₀ * (a₁-a₀) - a₀ * (b₁-b₀)) / (a₀*a₁) := by
  field_simp [h₀, h₁] <;> ring

end CMP99Pivot
