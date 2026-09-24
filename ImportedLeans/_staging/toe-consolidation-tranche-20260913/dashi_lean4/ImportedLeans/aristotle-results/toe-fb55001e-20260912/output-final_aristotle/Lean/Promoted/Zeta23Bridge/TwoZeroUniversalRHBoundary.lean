import Mathlib

namespace Zeta23Bridge
namespace TwoZeroUniversalRHBoundary

/-- A one-point finite model witnesses the logical gap: existence of one off-line
    object does not imply existence of three objects with strictly ordered
    positive heights. This is a dependency/nonpromotion theorem, not a zeta model. -/
inductive OneZero where
  | rho

deriving DecidableEq

open OneZero

def OffLine : OneZero → Prop := fun _ => True

def PositiveHeight : OneZero → Prop := fun _ => True

def StrictHeightBelow : OneZero → OneZero → Prop := fun _ _ => False

example : ∃ ρ, OffLine ρ := ⟨rho, trivial⟩

theorem no_ordered_positive_triple :
    ¬ ∃ σ₁ σ₂ target : OneZero,
      PositiveHeight σ₁ ∧ PositiveHeight σ₂ ∧ PositiveHeight target ∧
      StrictHeightBelow σ₁ σ₂ ∧ StrictHeightBelow σ₂ target := by
  rintro ⟨σ₁, σ₂, target, _, _, _, h12, _⟩
  exact h12

/-- Therefore a universal RH contradiction compiler must not silently use the
    inhabited two-zero theorem unless its two additional ordered zero witnesses
    are produced from the literal zeta carrier. -/
theorem one_offline_does_not_logically_supply_ordered_triple :
    (∃ ρ, OffLine ρ) ∧
    (¬ ∃ σ₁ σ₂ target : OneZero,
      PositiveHeight σ₁ ∧ PositiveHeight σ₂ ∧ PositiveHeight target ∧
      StrictHeightBelow σ₁ σ₂ ∧ StrictHeightBelow σ₂ target) :=
  ⟨⟨rho, trivial⟩, no_ordered_positive_triple⟩

end TwoZeroUniversalRHBoundary
end Zeta23Bridge
