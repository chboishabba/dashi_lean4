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


namespace NSBControl
namespace Rational345ReserveWitness

/-!
## Same physical row data, real scalar

R847/R849/R850 identify the literal Agda finite Fourier work,
production and dissipation with workRows, productionRows and
dissipationRows over Q. Cast the WHOLE row lists, not just their
aggregates, to the real scalar codomain of a genuine real-time flow.
This is the exact seed-data cast, not an arbitrary-mode real helical
projector proof.
-/

def realWorkRows : List ℝ := workRows.map (fun q : ℚ => (q : ℝ))
def realProductionRows : List ℝ :=
  productionRows.map (fun q : ℚ => (q : ℝ))
def realDissipationRows : List ℝ :=
  dissipationRows.map (fun q : ℚ => (q : ℝ))

def realCoherentWork : ℝ := realWorkRows.sum
def realCriticalProduction : ℝ := realProductionRows.sum
def realCriticalDissipation : ℝ := realDissipationRows.sum

theorem realCoherentWork_same_rows :
    realCoherentWork = (commutatorWork : ℝ) := by
  simp [realCoherentWork, realWorkRows, commutatorWork]

theorem realCriticalProduction_same_rows :
    realCriticalProduction = (criticalProduction : ℝ) := by
  simp [realCriticalProduction, realProductionRows, criticalProduction]

theorem realCriticalDissipation_same_rows :
    realCriticalDissipation = (criticalDissipation : ℝ) := by
  simp [realCriticalDissipation, realDissipationRows, criticalDissipation]

/-- Real selected R815/R853 pointwise normal form on identical seed rows. -/
def selectedRealRateFromSourceRows : ℝ :=
  6 * (12 * realCoherentWork -
    realCriticalProduction + realCriticalDissipation)

theorem selectedRealRateFromSourceRows_eq_cast :
    selectedRealRateFromSourceRows = (canonicalSignedRate : ℝ) := by
  rw [selectedRealRateFromSourceRows,
    realCoherentWork_same_rows,
    realCriticalProduction_same_rows,
    realCriticalDissipation_same_rows]
  norm_num [canonicalSignedRate]

theorem selectedRealRateFromSourceRows_exact :
    selectedRealRateFromSourceRows = -(28273644 : ℝ) / 125 := by
  rw [selectedRealRateFromSourceRows_eq_cast, canonicalSignedRate_exact]
  norm_num

theorem selectedRealRateFromSourceRows_negative :
    selectedRealRateFromSourceRows < 0 := by
  rw [selectedRealRateFromSourceRows_exact]
  norm_num

end Rational345ReserveWitness
end NSBControl


namespace NSBControl
namespace Rational345ReserveWitness

/--
The actual REAL helical-projector denominators on the selected active
3-4-5 seed modes agree with the rational R835 reciprocals. The statement
does NOT assert rational norms on inactive lattice modes or at later times.
-/
theorem selected_three_four_five_real_norms :
    Real.sqrt (9 : ℝ) = (3 : ℝ) ∧
    Real.sqrt (16 : ℝ) = (4 : ℝ) ∧
    Real.sqrt (25 : ℝ) = (5 : ℝ) := by
  constructor
  · norm_num
  constructor <;> norm_num

theorem selected_three_four_five_real_inverse_norms :
    (Real.sqrt (9 : ℝ))⁻¹ = ((1 / 3 : ℚ) : ℝ) ∧
    (Real.sqrt (16 : ℝ))⁻¹ = ((1 / 4 : ℚ) : ℝ) ∧
    (Real.sqrt (25 : ℝ))⁻¹ = ((1 / 5 : ℚ) : ℝ) := by
  rcases selected_three_four_five_real_norms with ⟨h3, h4, h5⟩
  rw [h3, h4, h5]
  constructor
  · norm_num
  constructor <;> norm_num

end Rational345ReserveWitness
end NSBControl
