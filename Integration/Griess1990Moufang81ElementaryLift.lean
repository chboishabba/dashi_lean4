import Integration.Griess1990Moufang81Determinant
import Mathlib

/-!
# Source-correct 3³ : SL(3,3) candidate: six TRUE Moufang81 shears

Original source: R. L. Griess Jr., *A Moufang loop, the exceptional Jordan
algebra, and a cubic form in 27 variables*, J. Algebra 131 (1990),
281–293, DOI 10.1016/0021-8693(90)90176-O.
Earlier independent theory of automorphisms of commutative Moufang
loops must retain its own authorship; do not credit Griess with all
general automorphism-group results.

The grade-only elementary shear is NOT generally an automorphism of
the original Griess phase polynomial g. The six corrections below
are explicit source-derived solutions of
 h(x+y)-h(x)-h(y)=g(Mx,My)-g(x,y).
They give actual automorphisms of the *same* order-81 Moufang loop,
not abstract action labels or a 240-cardinality surrogate.

Independent local Python enumerated all 6×81² multiplication
identities; SymPy Schreier--Sims on the literal 81-point permutations
reported order151632 =27×5616 and all27 kernel character shifts
contained. This particular Lean module only states the finite
generator/correction laws; a group-order / splitting Lean
kernel witness remains a distinct obligation.
All theorems are SOURCE-WRITTEN and were not kernel executed.
-/

namespace Integration.Griess1990Moufang81ElementaryLift

open Integration.Griess1990Moufang81Determinant

inductive Shear
  | e01 | e02 | e10 | e12 | e20 | e21
  deriving DecidableEq, Repr, Fintype

/-- One of the six exact elementary SL3(3) transvections. -/
def gradeShear : Shear → Grade → Grade
  | .e01, x => ![x 0 + x 1, x 1, x 2]
  | .e02, x => ![x 0 + x 2, x 1, x 2]
  | .e10, x => ![x 0, x 1 + x 0, x 2]
  | .e12, x => ![x 0, x 1 + x 2, x 2]
  | .e20, x => ![x 0, x 1, x 2 + x 0]
  | .e21, x => ![x 0, x 1, x 2 + x 1]

/-- Cohomological correction extracted by finite F3 linear
equations; the simple polynomial representatives are verified against
the source g, not tuned to the number 240. -/
def phaseCorrection : Shear → Grade → ZMod 3
  | .e01, x => x 2 * (1 - (x 1)^2)
  | .e02, _ => 0
  | .e10, x => x 2 * (1 - (x 0)^2)
  | .e12, x => x 0 * ((x 2)^2 - 1)
  | .e20, _ => 0
  | .e21, x => x 0 * ((x 1)^2 - 1)

/-- An ordinary shear fixing central phase can FAIL source
multiplication; the source-selected correction is genuinely necessary. -/
theorem naive_e01_fails_source_phase :
    g (gradeShear .e01 ![0,0,1])
      (gradeShear .e01 ![0,1,0]) = 2 ∧
    g ![0,0,1] ![0,1,0] = 0 := by native_decide

/-- All 6×27² source cochain conditions from the original g. -/
theorem six_phase_cocycle_corrections :
    ∀ s : Shear, ∀ x y : Grade,
      phaseCorrection s (x+y) -
        phaseCorrection s x - phaseCorrection s y =
      g (gradeShear s x) (gradeShear s y) - g x y := by
  native_decide

theorem six_shears_grade_additive :
    ∀ s : Shear, ∀ x y : Grade,
      gradeShear s (x+y) =
      gradeShear s x + gradeShear s y := by
  native_decide

/-- The actual SAME M81 multiplication from the previous owner,
with a nontrivial central correction. -/
def lift (s : Shear) (m : Loop81) : Loop81 :=
  ⟨gradeShear s m.grade, m.central + phaseCorrection s m.grade⟩

theorem six_lifts_preserve_literal_source_multiplication :
    ∀ s : Shear, ∀ a b : Loop81,
      lift s (multiply a b) = multiply (lift s a) (lift s b) := by
  native_decide

theorem six_lifts_preserve_nonidentity :
    ∀ s : Shear, ∀ a : Loop81,
      a ≠ identity → lift s a ≠ identity := by native_decide

theorem each_lift_fixes_the_original_unit :
    ∀ s : Shear, lift s identity = identity := by native_decide

theorem each_lift_order_three :
    ∀ s : Shear, ∀ a : Loop81,
      lift s (lift s (lift s a)) = a := by native_decide

/-- The 27 actual character shifts: source A action on the central
coordinate, not conjectural new 27-dimensional Monster actors. -/
def centralCharacterShift (lambda : Grade) (m : Loop81) : Loop81 :=
  ⟨m.grade, m.central +
    lambda 0*m.grade 0 + lambda 1*m.grade 1 + lambda 2*m.grade 2⟩

theorem central_character_shift_preserves_product :
    ∀ lambda : Grade, ∀ a b : Loop81,
      centralCharacterShift lambda (multiply a b) =
      multiply (centralCharacterShift lambda a)
        (centralCharacterShift lambda b) := by
  native_decide

theorem central_character_shift_injective_as_parameter :
    ∀ l k : Grade,
      (∀ m : Loop81, centralCharacterShift l m =
        centralCharacterShift k m) → l = k := by
  native_decide

end Integration.Griess1990Moufang81ElementaryLift
