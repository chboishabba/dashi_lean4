import Synthesis.MillenniumBSDMathlibLFunctionWeld
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

/-!
# K3: actual congruent-number-1 curve / rational unit-area triangle weld

This pays the exact, original, non-abstract algebraic correspondence
for E:y²=x³-x:
  nonexceptional rational affine point with y ≠ 0
  <=> rational right triangle with ab=2 (area exactly one).

Point -> triangle:
  a=(x²-1)/y, b=2x/y, c=(x²+1)/y.
Triangle -> point:
  x=(c+a)/b, y=2(c+a)/b².

Both satisfy their LITERAL equations over Q. There is no synthetic
point group, square-class receipt, or conjectural Kummer equality.

The remaining external arithmetic step is Fermat's theorem that
there exists NO nondegenerate rational right triangle of square area.
This source does not quietly use FLT(4) as a theorem of that shape:
Mathlib.NumberTheory.FLT.Four.not_fermat_42 excludes a⁴+b⁴=c²,
and the bridge from a unit-area rational Pythagorean triangle to
that integer witness still requires a formal infinite descent.
Once that theorem is supplied, this map eliminates ALL affine
points with y != 0, obtaining rank zero directly without having to
formalize Mordell–Weil finite generation.

Source-written; a local pinned Lean kernel run is still required.
-/

namespace Synthesis.Millennium.BSD

/-- The original signed rational right-triangle representation
has squared hypotenuse and EXACT unit area. -/
def CMHasRationalRightTriangleAreaOne : Prop :=
  ∃ a b c : ℚ,
    a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b = 2 ∧ a ≠ 0 ∧ b ≠ 0

def cmCurveTriangleA (x y : ℚ) : ℚ := (x ^ 2 - 1) / y
def cmCurveTriangleB (x y : ℚ) : ℚ := 2 * x / y
def cmCurveTriangleC (x y : ℚ) : ℚ := (x ^ 2 + 1) / y

/-- Curve-to-triangle Pythagorean equality is a ring identity,
requiring only y≠0 (not the elliptic equation). -/
theorem cmCurveTriangle_pythagorean
    (x y : ℚ) (hy : y ≠ 0) :
    cmCurveTriangleA x y ^ 2 +
      cmCurveTriangleB x y ^ 2 =
        cmCurveTriangleC x y ^ 2 := by
  unfold cmCurveTriangleA cmCurveTriangleB cmCurveTriangleC
  field_simp [hy]
  ring

/-- The selected original cubic forces EXACT area one:
ab/2 = x(x²−1)/y² = 1. -/
theorem cmCurveTriangle_area_one
    (x y : ℚ) (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    cmCurveTriangleA x y * cmCurveTriangleB x y = 2 := by
  unfold cmCurveTriangleA cmCurveTriangleB
  field_simp [hy]
  nlinarith [hcurve]

/-- Original affine rational non-torsion point supplies an actual
signed right triangle of rational area one. -/
theorem cmSelectedCurvePoint_implies_unitAreaTriangle
    (x y : ℚ) (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    CMHasRationalRightTriangleAreaOne := by
  have hp := cmCurveTriangle_pythagorean x y hy
  have ha := cmCurveTriangle_area_one x y hcurve hy
  have ha0 : cmCurveTriangleA x y ≠ 0 := by
    intro hz
    rw [hz] at ha
    norm_num at ha
  have hb0 : cmCurveTriangleB x y ≠ 0 := by
    intro hz
    rw [hz] at ha
    norm_num at ha
  exact ⟨cmCurveTriangleA x y, cmCurveTriangleB x y,
    cmCurveTriangleC x y, hp, ha, ha0, hb0⟩

def cmUnitTriangleCurveX (a b c : ℚ) : ℚ := (c + a) / b
def cmUnitTriangleCurveY (a b c : ℚ) : ℚ :=
  2 * (c + a) / b ^ 2

/-- The rational triangle-to-curve inverse formula is on the
ACTUAL selected cubic. No infinite-descent theorem is used. -/
theorem cmUnitTriangle_curve_equation
    (a b c : ℚ)
    (hpyth : a ^ 2 + b ^ 2 = c ^ 2)
    (harea : a * b = 2)
    (hb : b ≠ 0) :
    cmUnitTriangleCurveY a b c ^ 2 =
      cmUnitTriangleCurveX a b c ^ 3 -
        cmUnitTriangleCurveX a b c := by
  have hdiff :
      (c + a) ^ 2 - b ^ 2 = 2 * a * (c + a) := by
    nlinarith [hpyth]
  have hpoly :
      b * (c + a) ^ 3 - b ^ 3 * (c + a) =
        4 * (c + a) ^ 2 := by
    calc
      b * (c + a) ^ 3 - b ^ 3 * (c + a) =
          b * (c + a) * ((c + a) ^ 2 - b ^ 2) := by ring
      _ = b * (c + a) * (2 * a * (c + a)) := by rw [hdiff]
      _ = (a * b) * (2 * (c + a) ^ 2) := by ring
      _ = 2 * (2 * (c + a) ^ 2) := by rw [harea]
      _ = 4 * (c + a) ^ 2 := by ring
  unfold cmUnitTriangleCurveY cmUnitTriangleCurveX
  field_simp [hb]
  nlinarith [hpoly]

/-- A signed unit-area right triangle yields an affine rational
point with NONZERO y on y²=x³−x. -/
theorem cmUnitAreaTriangle_implies_selected_nonTorsionPoint
    (h : CMHasRationalRightTriangleAreaOne) :
    ∃ x y : ℚ, y ^ 2 = x ^ 3 - x ∧ y ≠ 0 := by
  rcases h with ⟨a, b, c, hpyth, harea, ha, hb⟩
  have hcp : c + a ≠ 0 := by
    intro hzero
    have hc : c = -a := by linarith
    have hb2 : b ^ 2 = 0 := by
      rw [hc] at hpyth
      nlinarith [hpyth]
    exact (pow_ne_zero 2 hb) hb2
  refine ⟨cmUnitTriangleCurveX a b c,
    cmUnitTriangleCurveY a b c,
    cmUnitTriangle_curve_equation a b c hpyth harea hb, ?_⟩
  unfold cmUnitTriangleCurveY
  exact div_ne_zero (mul_ne_zero (by norm_num) hcp)
    (pow_ne_zero 2 hb)

/-- The precise same-object existence equivalence: 1 is a
congruent number iff the original CM curve has an affine
rational point with nonzero ordinate. -/
theorem cmSelectedCongruentOne_iff_curve_nonTorsion :
    CMHasRationalRightTriangleAreaOne ↔
      ∃ x y : ℚ, y ^ 2 = x ^ 3 - x ∧ y ≠ 0 := by
  constructor
  · exact cmUnitAreaTriangle_implies_selected_nonTorsionPoint
  · rintro ⟨x, y, hcurve, hy⟩
    exact cmSelectedCurvePoint_implies_unitAreaTriangle x y hcurve hy

end Synthesis.Millennium.BSD
