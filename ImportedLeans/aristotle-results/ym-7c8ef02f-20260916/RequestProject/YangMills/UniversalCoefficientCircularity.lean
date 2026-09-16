/-
# Row A1a — audit: a "universal coefficient" field is not a derivation

A tempting shortcut for the Gaussian floor is a lane that proves the value
`11/12` for the SU(2) infrared coefficient.  Its upstream carrier, however,
contains a *field* asserting

    infraredCoefficient = universalColorCoefficient,

and the value is then read off that field.  This file proves, in the abstract,
what such a carrier can and cannot support.

* `coefficient_of_universalField` : the value does follow — but only from the
  field, so the implication is "carrier satisfying the universal-coefficient
  field ⟹ value", not "literal integrand ⟹ value".
* `universalField_uninformative` : for *every* integrand and *every* value there
  is a carrier with that integrand and that coefficient satisfying the field.
  The field therefore places no constraint whatsoever on the literal integrand.
* `coefficient_not_determined_by_integrand` : two carriers with the *same*
  integrand and *different* coefficients, both satisfying the field.  So the
  coefficient is not a function of the integrand, and the value cannot be used
  as evidence for a Gaussian floor `b_Z` of the literal Bałaban Gaussian —
  doing so would be a circular normalisation claim.
* `coefficient_determined_of_derived` : the contrast.  If the coefficient is
  *derived*, i.e. equal to a fixed functional of the integrand, then equal
  integrands do force equal coefficients.  This is the shape a genuine
  derivation must have.

Consequently no theorem in this development uses a universal-coefficient carrier
as an input to the Gaussian floor.
-/
import Mathlib

namespace YangMills

/-- Abstract model of the upstream carrier: a literal scalar integrand, an
infrared coefficient, a universal colour coefficient, and the *field* asserting
that the two agree. -/
structure UniversalCoefficientCarrier where
  integrand : ℝ → ℝ
  infraredCoefficient : ℝ
  universalColorCoefficient : ℝ
  infraredCoefficientExact : infraredCoefficient = universalColorCoefficient

/-- The value follows from the field, not from the integrand. -/
theorem coefficient_of_universalField (E : UniversalCoefficientCarrier)
    (h : E.universalColorCoefficient = 11 / 12) :
    E.infraredCoefficient = 11 / 12 := by
  rw [E.infraredCoefficientExact, h]

/-- **The field is uninformative about the integrand.**  Any integrand and any
value can be carried simultaneously. -/
theorem universalField_uninformative (f : ℝ → ℝ) (v : ℝ) :
    ∃ E : UniversalCoefficientCarrier, E.integrand = f ∧ E.infraredCoefficient = v :=
  ⟨⟨f, v, v, rfl⟩, rfl, rfl⟩

/-- **The coefficient is not a function of the literal integrand.**  Two
carriers with the same integrand carry different coefficients, both satisfying
the universal-coefficient field. -/
theorem coefficient_not_determined_by_integrand :
    ∃ E₁ E₂ : UniversalCoefficientCarrier,
      E₁.integrand = E₂.integrand ∧
      E₁.infraredCoefficient ≠ E₂.infraredCoefficient := by
  refine ⟨⟨fun _ => 0, 11 / 12, 11 / 12, rfl⟩, ⟨fun _ => 0, 0, 0, rfl⟩, rfl, ?_⟩
  norm_num

/-- In particular the value `11/12` carried by such a structure is consistent
with a literal integrand that is identically zero, i.e. with a vanishing
Gaussian coefficient. -/
theorem universalField_consistent_with_zero_integrand :
    ∃ E : UniversalCoefficientCarrier,
      E.integrand = (fun _ => 0) ∧ E.infraredCoefficient = 11 / 12 :=
  ⟨⟨fun _ => 0, 11 / 12, 11 / 12, rfl⟩, rfl, rfl⟩

/-- **The contrast: a derived coefficient is determined.**  If the coefficient
equals a fixed functional of the integrand, equal integrands force equal
coefficients.  This is the shape that an actual extraction from the source must
have before it may feed a Gaussian floor. -/
theorem coefficient_determined_of_derived (Phi : (ℝ → ℝ) → ℝ)
    {E₁ E₂ : UniversalCoefficientCarrier}
    (h₁ : E₁.infraredCoefficient = Phi E₁.integrand)
    (h₂ : E₂.infraredCoefficient = Phi E₂.integrand)
    (h : E₁.integrand = E₂.integrand) :
    E₁.infraredCoefficient = E₂.infraredCoefficient := by
  rw [h₁, h₂, h]

end YangMills
