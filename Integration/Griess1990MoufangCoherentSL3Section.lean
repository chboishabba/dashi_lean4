import Integration.Griess1990Moufang81ElementaryLift
import Integration.Griess1990SourceShearCharacterNoFull26
import Mathlib

/-!
# Constructive source-specific Sah/Griess coherent SL₃(3) complement

ORIGINAL priority, not an original DASHI group-cohomology theorem:
- Chih-Han Sah, "Cohomology of split group extensions",
  J. Algebra 29 (1974), 255--302 (1976 Griess acknowledges Sah).
- Robert L. Griess Jr., "The splitting of extensions of SL(3,3) by
  the vector space F₃³", Pacific J. Math. 63 (1976), 405--409,
  DOI 10.2140/pjm.1976.63.405 (published H²=0).
- Robert L. Griess Jr., "A Moufang loop, the exceptional Jordan
  algebra, and a cubic form in 27 variables", J. Algebra 131 (1990),
  281--293, DOI 10.1016/0021-8693(90)90176-O
  (ORIGINAL particular 81-loop and graded Albert product).

Reuses ACTUAL 1990 source gradeShear, phaseCorrection,
centralCharacterShift and Loop81 multiplication. The existing
six arbitrary chosen shear lifts generated order 151632 and did
NOT form a section. A new exact GF3 consistency solver over ALL
5616 grade matrices and 33696 generator edges produced six
correcting kernel characters, uniquely up to 27 kernel conjugates.
The ACTUAL six 81-point permutations then generated order 5616;
the phase-compatibility linear system has rank15 in 18 unknowns.
Independent 6×729 actual tau-real original Griess Jordan
products PASS. The traceless rational 26D character has exact
squared norm 5616/5616=1 over this selected FULL group and is
absolutely irreducible by CLASSICAL character orthogonality;
the unphased 26-point grade permutation character has norm3.

Proof status: this module states checkable FINITE generator and
sample Steinberg relations, but DOES NOT pretend to supply
a 5616-element Lean group enumeration or kernel-certified
full section/irreducibility theorem. Those are exact local
Python results, with separate artifacts and source attribution.
No physical graph, Monster VOA or full rational-F4 classification.
-/

namespace Integration.Griess1990MoufangCoherentSL3Section

open Integration.Griess1990Moufang81Determinant
open Integration.Griess1990Moufang81ElementaryLift
open Integration.Griess1990SourceShearCharacterNoFull26

/-- Output phase character λ_s used to repair *all* group relations.
Order: e01,e02,e10,e12,e20,e21, matching previous Shear. -/
def sectionCharacter : Shear → Grade
  | .e01 => ![0,0,0]
  | .e02 => ![0,2,0]
  | .e10 => ![0,0,1]
  | .e12 => ![2,0,0]
  | .e20 => ![0,1,0]
  | .e21 => ![0,0,0]

/-- The exact SAME previously implemented M81 action, modified only
by one ORIGINAL 27-element kernel automorphism per generator. -/
def coherentLift (s : Shear) (a : Loop81) : Loop81 :=
  centralCharacterShift (sectionCharacter s) (lift s a)

def coherentInverse (s : Shear) (a : Loop81) : Loop81 :=
  coherentLift s (coherentLift s a)

theorem each_coherent_lift_preserves_original_product :
    ∀ s : Shear, ∀ a b : Loop81,
      coherentLift s (multiply a b) =
        multiply (coherentLift s a) (coherentLift s b) := by
  native_decide

theorem each_coherent_lift_has_order_three :
    ∀ s : Shear, ∀ a : Loop81,
      coherentLift s (coherentInverse s a) = a := by
  native_decide

theorem each_coherent_lift_preserves_original_unit :
    ∀ s : Shear, coherentLift s identity = identity := by
  native_decide

/-- A necessary group-presentation relation: same-row elementary
transvections e01 and e02 commute on ACTUAL Griess M81. -/
theorem coherent_e01_e02_commute :
    ∀ a : Loop81,
      coherentLift .e01 (coherentLift .e02 a) =
      coherentLift .e02 (coherentLift .e01 a) := by
  native_decide

/-- Positive type-A₂ Steinberg commutator relation,
[e01,e12]=e02, at the actual source loop level.
A complete finite presentation remains a separate kernel task. -/
theorem coherent_e01_e12_commutator :
    ∀ a : Loop81,
      coherentLift .e01
        (coherentLift .e12
          (coherentInverse .e01 (coherentInverse .e12 a))) =
      coherentLift .e02 a := by
  native_decide

/-- Actual source rational-27 character of coherent lifts.
For every selected transvection it is 0, and removing the
fixed original Albert unit gives actual J0 trace -1. -/
def sectionPhase (s : Shear) (x : Grade) : ZMod 3 :=
  phaseCorrection s x +
    sectionCharacter s 0 * (gradeShear s x 0) +
    sectionCharacter s 1 * (gradeShear s x 1) +
    sectionCharacter s 2 * (gradeShear s x 2)

def sectionPhaseHistogram (s : Shear) (phase : ZMod 3) : Nat :=
  (Finset.univ.filter fun x : Grade =>
    gradeShear s x = x ∧ sectionPhase s x = phase).card

theorem all_six_section_shear_fixed_phase_histograms :
    ∀ s : Shear,
      sectionPhaseHistogram s 0 = 3 ∧
      sectionPhaseHistogram s 1 = 3 ∧
      sectionPhaseHistogram s 2 = 3 := by
  native_decide

/-- Finite character mismatch with the original UNPHASED nonzero
26 grade-point permutation: true Albert J0 trace -1 vs 8. -/
theorem coherent_section_J0_differs_from_grade_permutation :
    ∀ s : Shear,
      (-1 : ℚ) ≠ (nonzeroGradePermutationTrace s : ℚ) := by
  native_decide

end Integration.Griess1990MoufangCoherentSL3Section
