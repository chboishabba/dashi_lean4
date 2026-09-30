import Integration.OggSSP2BActualRestrictedTate

/-!
# Grading-normalization collision audit: 2B vacuum and half shift

Two distinct operations must not be conflated:
1. Ordinary Tate on Carnahan-Urano's actual Z[C4] source, restricted to
   H=<g²>=C2. On the fixed integral vacuum lattice this gives Hhat0=F2,
   Hhat1=0.
2. Applying tau -> tau+1/2 coefficientwise to a formal q^(n-1)
   series with vacuum coefficient q^(-1). Its vacuum half-sum is 0,
   and its half-difference is 1.

Therefore the naive coefficientwise identification
'half sum = ordinary Hhat0' in the SAME vacuum grading is inconsistent.
This does not disprove Carnahan's Corollary 3.25: it exhibits the
precise requirement to check its graded supercharacter and Tate
normalization before using it as a degree-by-degree module statement.

No source-defined five-inertia-sector decomposition is introduced.
-/

namespace Integration.OggSSP2BActualSourceParityNormalizationAudit

namespace Tate := Integration.OggSSP2BActualRestrictedTate
namespace M := Integration.OggSSP2B4AActualIntegralMultiplicities

/-- Characteristic zero coefficient of q^-1 in a normalized Hauptmodul. -/
def vacuumCoefficient : ℤ := 1

/-- Half-period translation takes q^-1 to -q^-1. -/
def shiftedVacuumCoefficient : ℤ := -1

def naiveHalfSumVacuum : ℤ :=
  (vacuumCoefficient + shiftedVacuumCoefficient) / 2

def naiveHalfDifferenceVacuum : ℤ :=
  (vacuumCoefficient - shiftedVacuumCoefficient) / 2

theorem naive_half_sum_zero : naiveHalfSumVacuum = 0 := by decide

theorem naive_half_difference_one : naiveHalfDifferenceVacuum = 1 := by decide

theorem actual_source_vacuum_H0_one :
    Tate.gradeH0Length M.vacuum = 1 := by decide

theorem actual_source_vacuum_H1_zero :
    Tate.gradeH1Length M.vacuum = 0 := by decide

theorem naive_halfsum_does_not_equal_actual_vacuum_H0 :
    naiveHalfSumVacuum ≠
      (Tate.gradeH0Length M.vacuum : ℤ) := by decide

theorem naive_halfdifference_does_not_equal_actual_vacuum_H1 :
    naiveHalfDifferenceVacuum ≠
      (Tate.gradeH1Length M.vacuum : ℤ) := by decide

/-- Source-revision hygiene: the missing convention is not paid by
rewriting the source's q-degree or by calling a defect a module length. -/
theorem naive_same_grading_identification_impossible :
    ¬ (naiveHalfSumVacuum =
      (Tate.gradeH0Length M.vacuum : ℤ) ∧
       naiveHalfDifferenceVacuum =
      (Tate.gradeH1Length M.vacuum : ℤ)) := by
  intro h
  exact naive_halfsum_does_not_equal_actual_vacuum_H0 h.1

end Integration.OggSSP2BActualSourceParityNormalizationAudit
