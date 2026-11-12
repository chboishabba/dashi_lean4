import Synthesis.MillenniumBSDCMQ2ActualCurveValuationExact
import Synthesis.MillenniumBSDSquareClassGroups
import Mathlib.Tactic

/-!
# BSD: actual Q_2 square-class valuation parity, not a new proxy carrier

The original repo owns PadicSquareClass 2 as the quotient of actual
NonzeroPadic 2 values by PadicSquareRel.  Multiplication by a square
changes Padic.valuation by an even integer. Hence the integer remainder
modulo two is well-defined on the ORIGINAL quotient.

The selected curve's ordinary first x-T coordinate is x. Applying the
genuine Q_2 affine valuation theorem yields zero parity in this actual
local square-class quotient. Exceptional torsion Kummer conventions
remain separate, as do the all-place Selmer and classical Sha bridges.

Source-written; pinned local Lean kernel check pending.
-/

namespace Synthesis.Millennium.BSD

/-- The repository's original Q_2 square equivalence preserves parity
of the actual integer-valued p-adic valuation. -/
theorem cmQ2SquareRel_preservesValuationParity
    (a b : NonzeroPadic 2)
    (h : PadicSquareRel 2 a b) :
    ((a : ℚ_[2]).valuation % 2) =
      ((b : ℚ_[2]).valuation % 2) := by
  rcases h with ⟨s, t, hst⟩
  have hval :
      (a : ℚ_[2]).valuation + 2 * (s : ℚ_[2]).valuation =
        (b : ℚ_[2]).valuation + 2 * (t : ℚ_[2]).valuation := by
    calc
      (a : ℚ_[2]).valuation + 2 * (s : ℚ_[2]).valuation =
          ((a : ℚ_[2]) * (s : ℚ_[2]) ^ 2).valuation := by
            rw [Padic.valuation_mul a.property (pow_ne_zero 2 s.property)]
            rw [Padic.valuation_pow]
            ring
      _ = ((b : ℚ_[2]) * (t : ℚ_[2]) ^ 2).valuation :=
        congrArg Padic.valuation hst
      _ = (b : ℚ_[2]).valuation + 2 * (t : ℚ_[2]).valuation := by
            rw [Padic.valuation_mul b.property (pow_ne_zero 2 t.property)]
            rw [Padic.valuation_pow]
            ring
  omega

/-- Actual valuation-parity projection on the original quotient
Q_2^*/Q_2^{*2}. Its result is the canonical representative 0 or 1. -/
def cmQ2SquareClassValuationParity :
    PadicSquareClass 2 → ℤ :=
  Quotient.lift
    (fun a : NonzeroPadic 2 => (a : ℚ_[2]).valuation % 2)
    (fun a b h => cmQ2SquareRel_preservesValuationParity a b h)

/-- Original quotient projection evaluates to its representative's
actual Q_2 valuation parity. -/
theorem cmQ2SquareClassValuationParity_rep
    (a : NonzeroPadic 2) :
    cmQ2SquareClassValuationParity (padicSquareClassOf 2 a) =
      (a : ℚ_[2]).valuation % 2 := rfl

/-- An actual p-adic nonzero element with even valuation has
parity zero in the original square-class quotient. -/
theorem cmQ2SquareClassValuationParity_of_even
    (a : NonzeroPadic 2)
    (heven : Even (a : ℚ_[2]).valuation) :
    cmQ2SquareClassValuationParity (padicSquareClassOf 2 a) = 0 := by
  rw [cmQ2SquareClassValuationParity_rep]
  rcases heven with ⟨k, hk⟩
  omega

/-- The original nonexceptional x-T first-coordinate square class
has even 2-adic valuation on genuine Q_2 affine curve points.
No independent Selmer or local-image carrier is introduced. -/
theorem cmQ2OrdinaryXTSquareClassParity_zero
    (x y : ℚ_[2])
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    cmQ2SquareClassValuationParity
      (padicSquareClassOf 2
        (⟨x, (cmQ2Affine_nonzero_factors x y hcurve hy).1⟩ :
          NonzeroPadic 2)) = 0 := by
  exact cmQ2SquareClassValuationParity_of_even
    ⟨x, (cmQ2Affine_nonzero_factors x y hcurve hy).1⟩
    (cmQ2NonexceptionalXValuationEven x y hcurve hy)


/-- First local x-T torsion coordinate of O and (1,0): the original
Q_2 square class of one has parity zero. -/
theorem cmQ2TorsionFirstSquareClassOneParity_zero :
    cmQ2SquareClassValuationParity
      (padicSquareClassOf 2
        (⟨1, by norm_num⟩ : NonzeroPadic 2)) = 0 := by
  rw [cmQ2SquareClassValuationParity_rep]
  simp [Padic.valuation_one]

/-- First local x-T torsion coordinate of (0,0) and (-1,0):
the original Q_2 square class of minus one has parity zero. -/
theorem cmQ2TorsionFirstSquareClassNegOneParity_zero :
    cmQ2SquareClassValuationParity
      (padicSquareClassOf 2
        (⟨-1, by norm_num⟩ : NonzeroPadic 2)) = 0 := by
  rw [cmQ2SquareClassValuationParity_rep, cmQ2Valuation_negOne]
  omega

/-- Every exceptional first x-T representative in the selected
rational torsion table is 1 or -1, hence its ORIGINAL Q_2 square
class has even valuation. This is an arithmetic value theorem,
not yet the local geometric Kummer naturality statement. -/
theorem cmQ2ExceptionalFirstKummerRepresentativeParity_zero
    (a : NonzeroPadic 2)
    (ha : (a : ℚ_[2]) = 1 ∨ (a : ℚ_[2]) = -1) :
    cmQ2SquareClassValuationParity (padicSquareClassOf 2 a) = 0 := by
  rw [cmQ2SquareClassValuationParity_rep]
  rcases ha with h | h
  · rw [h, Padic.valuation_one]
    omega
  · rw [h, cmQ2Valuation_negOne]
    omega

end Synthesis.Millennium.BSD
