import Mathlib.Tactic

/-!
# Exact rational 3-4-5 signed-reserve witness

Lean mirror of the rational arithmetic layer of Agda R828-R831.

The eight fixed-output coherent-work rows and six production/dissipation rows
are exact rationals. This file kernel-checks their aggregation and the
canonical R815 rate. It does not prove that the rows are already the values of
the live Agda R30/R230/R692/R744 operators.
-/

namespace NSBControl
namespace Rational345ReserveWitness

def workRows : List ℚ :=
  [ -48
  , 322917 / 250
  , -48
  , -(428272 / 125)
  , -(428272 / 125)
  , -48
  , 322917 / 250
  , -48
  ]

def productionRows : List ℚ :=
  [-128, -672, 800, 800, -672, -128]

def dissipationRows : List ℚ :=
  [6425, 468, 1024, 1024, 468, 6425]

def commutatorWork : ℚ := workRows.sum
def criticalProduction : ℚ := productionRows.sum
def criticalDissipation : ℚ := dissipationRows.sum

def canonicalSignedRate : ℚ :=
  6 * (12 * commutatorWork - criticalProduction + criticalDissipation)

theorem commutatorWork_exact :
    commutatorWork = -(557627 / 125 : ℚ) := by
  norm_num [commutatorWork, workRows]

theorem criticalProduction_exact :
    criticalProduction = 0 := by
  norm_num [criticalProduction, productionRows]

theorem criticalDissipation_exact :
    criticalDissipation = 15834 := by
  norm_num [criticalDissipation, dissipationRows]

theorem canonicalSignedRate_exact :
    canonicalSignedRate = -(28273644 / 125 : ℚ) := by
  rw [canonicalSignedRate, commutatorWork_exact,
      criticalProduction_exact, criticalDissipation_exact]
  norm_num

theorem canonicalSignedRate_negative : canonicalSignedRate < 0 := by
  rw [canonicalSignedRate_exact]
  norm_num

/-- Any concrete selected repository scalar proved equal to this rational
witness is strictly negative at the initial snapshot. -/
theorem matchingRate_negative
    (actualRate : ℚ)
    (hmatch : actualRate = canonicalSignedRate) :
    actualRate < 0 := by
  rw [hmatch]
  exact canonicalSignedRate_negative

/-- A universal pointwise nonnegativity claim cannot survive a same-object
identification with this snapshot. -/
theorem noNonnegativeMatchingRate
    (actualRate : ℚ)
    (hmatch : actualRate = canonicalSignedRate)
    (hnonnegative : 0 ≤ actualRate) : False := by
  exact (not_le_of_gt (matchingRate_negative actualRate hmatch)) hnonnegative

end Rational345ReserveWitness
end NSBControl
