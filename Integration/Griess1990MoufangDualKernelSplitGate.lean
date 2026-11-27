import Integration.Griess1990Moufang81ElementaryLift
import Mathlib

/-!
# ACTUAL source M81 character-kernel dual action, historical H² splitting gate

Original original-source roots, in priority order:
* Chih-Han Sah, 'Cohomology of split group extensions',
  J. Algebra 29 (1974), 255-302: prior published cohomology result
  explicitly acknowledged in Griess's 1976 introduction.
* Robert L. Griess Jr., 'The splitting of extensions of SL(3,3)
  by the vector space F3^3', Pacific J. Math. 63 (1976), 405-409,
  DOI 10.2140/pjm.1976.63.405: two original elementary proofs of
  H²(SL3(3), natural F3^3)=0, so such extensions SPLIT.
* R. L. Griess Jr., J. Algebra 131 (1990), 281-293,
  DOI 10.1016/0021-8693(90)90176-O: the PARTICULAR graded 27D
  Albert algebra, source g and associated M81 automorphisms.
* Bénéteau--Lacaze, Eur. J. Combin. 1 (1980) 299-309:
  independent original commutative-Moufang automorphism theory.

Existing Lean #52 owner already defines ACTUAL central character kernel
`centralCharacterShift lambda` (27 maps) and six *corrected* shears
`lift s`. Exact independent Python PASS on all 6*27*81=13122 triples
shows conjugation by the selected lift acts on its 27-element kernel
as the CONTRAGREDIENT / DUAL of the natural grade SL3 action:
   lift_s T_lambda lift_s^-1 = T_(lambda ∘ M_s^-1).
This verifies the dual kernel module needed to APPLY Griess1976
cohomological vanishing after precomposition by the graph automorphism
M->M^-T. DO NOT manufacture a new original splitting theorem or
a concrete section. A fully kernel-checked exact sequence G of order
151632 -> SL3(3) of order5616 with natural/dual kernel27 and an
EXPLICIT consistent complement are still separate payments.

Selected e01/e02 source-corrected lifts can have DIFFERENT actual
traceless-Albert characters (-1 vs8) though their grade projections
have the same 26-point permutation character8. Thus the six
initial lifts DO NOT represent a globally source-selected group
section merely because their grade permutations generate SL3.
No selected Monster3B, native P3 graph or physical gauge action.
All Lean theorems SOURCE-WRITTEN, NO Lean kernel run.
-/

namespace Integration.Griess1990MoufangDualKernelSplitGate

open Integration.Griess1990Moufang81Determinant
open Integration.Griess1990Moufang81ElementaryLift

/-- DUAL action on the central 27 characters, not the natural action
on the original 27 *grades*. For elementary transvection i<-i+j,
lambda_j transforms to lambda_j - lambda_i. -/
def dualShear : Shear → Grade → Grade
  | .e01, l => ![l 0, l 1 - l 0, l 2]
  | .e02, l => ![l 0, l 1, l 2 - l 0]
  | .e10, l => ![l 0 - l 1, l 1, l 2]
  | .e12, l => ![l 0, l 1, l 2 - l 1]
  | .e20, l => ![l 0 - l 2, l 1, l 2]
  | .e21, l => ![l 0, l 1 - l 2, l 2]

/-- The source lift has order three: inverse lift_s = lift_s²
on the ACTUAL source M81. -/
def liftInverse (s : Shear) (a : Loop81) : Loop81 :=
  lift s (lift s a)

/-- Check on ACTUAL source `Loop81`, not an abstract group of
81 unrelated labels, all 13122 selected-conjugation equations. -/
theorem actual_six_shear_conjugates_character_kernel_dually :
    ∀ s : Shear, ∀ lambda : Grade, ∀ a : Loop81,
      lift s (centralCharacterShift lambda (liftInverse s a)) =
        centralCharacterShift (dualShear s lambda) a := by
  native_decide

/-- Source-selected grade action and natural-dual pairing preserve
the classical evaluation lambda(x); the kernel coordinate MUST
retain its orientation and source role. -/
theorem actual_dual_grade_pairing :
    ∀ s : Shear, ∀ lambda x : Grade,
      dualShear s lambda 0 * gradeShear s x 0 +
      dualShear s lambda 1 * gradeShear s x 1 +
      dualShear s lambda 2 * gradeShear s x 2 =
      lambda 0 * x 0 + lambda 1 * x 1 + lambda 2 * x 2 := by
  native_decide

end Integration.Griess1990MoufangDualKernelSplitGate
