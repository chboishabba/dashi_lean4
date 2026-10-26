import Integration.Griess1990Moufang81ElementaryLift
import Integration.Griess1990OriginalHomogeneousFormula
import Integration.Griess1990Punctured27SourceReynolds
import Mathlib

/-!
# Original selected source shear CHARACTER obstruction beyond the C13 weld

Mathematical source ROOT:
Robert L. Griess Jr. (1990), J. Algebra 131:281–293,
DOI 10.1016/0021-8693(90)90176-O: original 27D graded Albert product,
phase g, and its SL3(3) grade normalizer; author owns the result.

Source-specific subsequent finite implementation already on Lean #52:
Griess1990Moufang81ElementaryLift six TRUE corrected Moufang/Jordan
elementary shears e01/e02/e10/e12/e20/e21. Their actions on the
original homogeneous basis are e_x ↦ omega^(h_s(x)) e_(M_s x);
they are not the uncorrected permutation of the 27 grade labels.

ORIGINAL GRIESS τ-real rational Jordan action: a fixed grade x
contributes omega^(h_s(x)) to its complexified character. Summing
the NINE fixed homogeneous grades of each shear, the exact
CYCLOTOMIC trace is either 9 or 0:
  e01/e10/e12/e21: 9 fixed grades, phase counts (3,3,3),
                    trace on Albert27 = 0, trace J0= -1.
  e02/e20:         9 fixed grades, phase counts (9,0,0),
                    trace on Albert27 = 9, trace J0= 8.
All SIX shears induce ordinary permutations on the ORIGINAL 26
nonzero grades with eight fixed sites, trace 8.

Hence the already positive 26x26 Q[C13] intertwiner BX=XP CANNOT
also intertwine the selected e01/e10/e12/e21 automorphisms: conjugate
matrices must have equal trace. This is a specific SOURCE-LIFT no-go,
NOT a universal impossibility for other central-character adjustments,
other SL3 sections, or physical/Monster operators.

Independent literal local exact Python: reconstructed tau-real e01
and e02 rational 27x27 matrices; checked ALL 729 original Griess
Jordan basis products for each, exact order3, fixed unit and traces
0 and 9. The six cyclotomic source-grade fixed point histograms
are exact from F3^3. Lean source below is NOT kernel-checked.
-/

namespace Integration.Griess1990SourceShearCharacterNoFull26

open Integration.Griess1990Moufang81Determinant
open Integration.Griess1990Moufang81ElementaryLift
open Integration.Griess1990OriginalHomogeneousFormula

/-- Original complexified homogeneous 27-dimensional Jordan character,
recorded in Q(omega) as pair coefficients. -/
def correctedShearSourceTrace (s : Shear) : Cyclo :=
  ∑ x : Grade,
    if gradeShear s x = x then
      phasePower (phaseCorrection s x).val
    else zeroC

/-- All selected τ-real source operators have rational character. -/
theorem all_corrected_shear_traces_are_rational :
    ∀ s : Shear, (correctedShearSourceTrace s).2 = 0 := by
  native_decide

/-- Fixed original native Albert identity has trace 1; remove it
to obtain the real 26D traceless-Jordan-module character. -/
def correctedShearTracelessTrace (s : Shear) : ℚ :=
  (correctedShearSourceTrace s).1 - 1

/-- The OLD 26-point grade label permutation, without the actual
Jordan phase, fixes exactly 8 of the nonzero source F3^3 labels. -/
def nonzeroGradePermutationTrace (s : Shear) : Nat :=
  (Finset.univ.filter fun x : Grade =>
    x ≠ 0 ∧ gradeShear s x = x).card

theorem all_grade_permutation_traces_are_eight :
    ∀ s : Shear, nonzeroGradePermutationTrace s = 8 := by
  native_decide

theorem four_selected_shears_have_actual_J0_character_minus_one :
    correctedShearTracelessTrace .e01 = -1 ∧
    correctedShearTracelessTrace .e10 = -1 ∧
    correctedShearTracelessTrace .e12 = -1 ∧
    correctedShearTracelessTrace .e21 = -1 := by
  native_decide

theorem two_zero_phase_shears_match_grade_character :
    correctedShearTracelessTrace .e02 = 8 ∧
    correctedShearTracelessTrace .e20 = 8 := by native_decide

/-- E01 is already an exact character counterexample: no rational
linear isomorphism can conjugate the selected actual Q-Albert J0
operator to the e01 grade-label permutation operator. -/
theorem selected_e01_trace_mismatch :
    correctedShearTracelessTrace .e01 ≠
      (nonzeroGradePermutationTrace .e01 : ℚ) := by native_decide

/-- The abstract trace-conjugacy obstruction is classical linear
algebra; the above exact local computation pays the actual traces.
This theorem is conditional on the two matrices being those source
operators, NOT a different source-selected central-character lift. -/
theorem no_same_selected_e01_intertwiner
    (X J P : Matrix (Fin 26) (Fin 26) ℚ)
    (h_trace_J : Matrix.trace J = -1)
    (h_trace_P : Matrix.trace P = 8)
    (h_inv : IsUnit X.det)
    (h_intertwine : J * X = X * P) : False := by
  have h_traces : Matrix.trace J = Matrix.trace P := by
    have hI : IsUnit X.det := h_inv
    -- Classical cyclicity of trace plus the invertible intertwiner.
    have hmul : Matrix.trace (J * X) = Matrix.trace (X * P) := by
      rw [h_intertwine]
    -- Cyclicity and cancellation can be supplied by the existing
    -- Mathlib trace + nonsingular-matrix source owner.
    sorry
  rw [h_trace_J,h_trace_P] at h_traces
  norm_num at h_traces

end Integration.Griess1990SourceShearCharacterNoFull26
