import Synthesis.MillenniumHodgeP1QProjExact
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Hodge max-cut: degree-zero ring of the selected P¹ Proj is Q

For the ordinary grading on Q[X₀,X₁], a degree-zero homogeneous polynomial is
literally a constant.  This file packages that standard fact as a ring
equivalence between the grade-zero ring used by `Proj.toSpecZero` and Q.

This is the base-ring identification needed before constructing the displayed
structure morphism P¹_Q -> Spec Q and the rational section [1:0].
-/

namespace Synthesis.Millennium.Hodge

open MvPolynomial

/-- Constant coefficient of a degree-zero homogeneous polynomial. -/
noncomputable def p1QGradeZeroToRat :
    P1QGrading 0 →+* ℚ where
  toFun p := p.1.coeff 0
  map_zero' := by simp
  map_one' := by simp
  map_add' p q := by simp
  map_mul' p q := by simp

/-- Embed a rational scalar as the corresponding degree-zero homogeneous
polynomial. -/
noncomputable def ratToP1QGradeZero :
    ℚ →+* P1QGrading 0 where
  toFun q := ⟨C q, isHomogeneous_C q⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' p q := by ext; simp
  map_mul' p q := by ext; simp

@[simp] theorem p1QGradeZeroToRat_C (q : ℚ) :
    p1QGradeZeroToRat (ratToP1QGradeZero q) = q := by
  simp [p1QGradeZeroToRat, ratToP1QGradeZero]

/-- Every degree-zero homogeneous polynomial is exactly the constant given by
its constant coefficient. -/
theorem ratToP1QGradeZero_constantCoeff
    (p : P1QGrading 0) :
    ratToP1QGradeZero (p1QGradeZeroToRat p) = p := by
  apply Subtype.ext
  change C (p.1.coeff 0) = p.1
  symm
  apply (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp
  exact (MvPolynomial.totalDegree_zero_iff_isHomogeneous).mpr p.2

/-- Literal ring equivalence identifying the target of `Proj.toSpecZero` with
Q. -/
noncomputable def p1QGradeZeroRingEquiv :
    P1QGrading 0 ≃+* ℚ where
  toFun := p1QGradeZeroToRat
  invFun := ratToP1QGradeZero
  left_inv := ratToP1QGradeZero_constantCoeff
  right_inv := p1QGradeZeroToRat_C
  map_mul' := map_mul p1QGradeZeroToRat
  map_add' := map_add p1QGradeZeroToRat

/-!
MAX-CUT STATUS

PAID HERE (subject to exact-head kernel certification):
* exact ring equivalence (P1QGrading 0) ≃+* Q;
* therefore the canonical `Proj.toSpecZero` map is genuinely the usual
  projective-line structure morphism after the standard contravariant `Spec`
  transport.

NEXT:
* package the induced Spec isomorphism and displayed structure map to Spec Q;
* build the rational section [1:0] via `Proj.fromOfGlobalSections` or the X₀
  affine chart;
* feed that section into the already-paid relative ruling embeddings.
-/

end Synthesis.Millennium.Hodge
