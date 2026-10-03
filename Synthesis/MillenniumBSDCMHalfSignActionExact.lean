import Synthesis.MillenniumBSDCMAlgClosureDoublingSurjectiveExact
import Synthesis.MillenniumBSDCMXTOrientationExact
import Mathlib.Tactic

/-!
# Selected CM half-point: exact root-sign action identities

For the selected curve

  E : y² = x(x-1)(x+1)

and a chosen half determined by square roots

  a² = x,   b² = x-1,   c² = x+1,

with `abc = -y`, the classical half has

  x_Q = x + ab + bc + ca.

The global x-T/cohomological Kummer comparison has been reduced to identifying
which root-sign flips translate Q by the literal two-torsion basis points
(0,0), (1,0), (-1,0).  This file pays the purely algebraic half of that
calculation, with no cohomology assumptions:

* x_Q = (a+b)(a+c);
* x_Q - 1 = (a+b)(b+c);
* x_Q + 1 = (a+c)(b+c);
* flipping b and c gives x_Q x_Q' = -1;
* flipping a and c gives (x_Q-1)(x_Q'-1) = 2;
* flipping a and b gives (x_Q+1)(x_Q'+1) = 2.

These are exactly the Möbius x-coordinate relations expected for translation
by (0,0), (1,0), and (-1,0), respectively.  The next owner must prove those
translation formulas on the actual Mathlib elliptic group and then the finite
sign table determines the Kummer-coordinate orientation.
-/

namespace Synthesis.Millennium.BSD

noncomputable section

open WeierstrassCurve

variable {x a b c : RatAlgClosure}

/-- Factorization of the selected half x-coordinate using a²=x. -/
theorem algClosureHalfX_factor_ab_ac
    (ha : a ^ 2 = x) :
    algClosureHalfX x a b c = (a + b) * (a + c) := by
  unfold algClosureHalfX
  rw [← ha]
  ring

/-- The shifted coordinate x_Q-1 factors through the roots of x and x-1. -/
theorem algClosureHalfX_sub_one_factor
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1) :
    algClosureHalfX x a b c - 1 = (a + b) * (b + c) := by
  unfold algClosureHalfX
  have hbx : b ^ 2 = a ^ 2 - 1 := by
    rw [ha] at hb
    exact hb
  nlinarith [hbx]

/-- The shifted coordinate x_Q+1 factors through the roots of x and x+1. -/
theorem algClosureHalfX_add_one_factor
    (ha : a ^ 2 = x)
    (hc : c ^ 2 = x + 1) :
    algClosureHalfX x a b c + 1 = (a + c) * (b + c) := by
  unfold algClosureHalfX
  have hcx : c ^ 2 = a ^ 2 + 1 := by
    rw [ha] at hc
    exact hc
  nlinarith [hcx]

/-- Even sign flip (b,c) preserves abc and sends the half x-coordinate through
`x ↦ -1/x`, the selected curve's x-coordinate formula for translating by the
literal two-torsion point (0,0). -/
theorem algClosureHalfX_flip_bc_product
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1) :
    algClosureHalfX x a b c *
      algClosureHalfX x a (-b) (-c) = -1 := by
  rw [algClosureHalfX_factor_ab_ac ha]
  have hflip :
      algClosureHalfX x a (-b) (-c) = (a - b) * (a - c) := by
    simpa [sub_eq_add_neg] using
      (algClosureHalfX_factor_ab_ac (x := x) (a := a) (b := -b) (c := -c) ha)
  rw [hflip]
  have hab : (a + b) * (a - b) = 1 := by
    rw [mul_sub, add_mul]
    nlinarith [ha, hb]
  have hac : (a + c) * (a - c) = -1 := by
    rw [mul_sub, add_mul]
    nlinarith [ha, hc]
  calc
    (a + b) * (a + c) * ((a - b) * (a - c))
        = ((a + b) * (a - b)) * ((a + c) * (a - c)) := by ring
    _ = -1 := by rw [hab, hac]; ring

/-- Even sign flip (a,c) preserves abc and sends the shifted coordinate through
`(x_Q-1)(x_Q'-1)=2`, the selected curve's x-coordinate relation for
translation by (1,0). -/
theorem algClosureHalfX_flip_ac_sub_one_product
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1) :
    (algClosureHalfX x a b c - 1) *
      (algClosureHalfX x (-a) b (-c) - 1) = 2 := by
  rw [algClosureHalfX_sub_one_factor ha hb]
  have ha' : (-a) ^ 2 = x := by simpa using ha
  have hb' : b ^ 2 = x - 1 := hb
  have hflip :=
    algClosureHalfX_sub_one_factor
      (x := x) (a := -a) (b := b) (c := -c) ha' hb'
  simp only [neg_add_rev, neg_neg] at hflip
  rw [hflip]
  have hab : (a + b) * (b - a) = -1 := by
    nlinarith [ha, hb]
  have hbc : (b + c) * (b - c) = -2 := by
    nlinarith [hb, hc]
  calc
    (a + b) * (b + c) * ((-a + b) * (b + -c))
        = ((a + b) * (b - a)) * ((b + c) * (b - c)) := by ring
    _ = 2 := by rw [hab, hbc]; norm_num

/-- Even sign flip (a,b) preserves abc and gives the third two-torsion
translation relation at x=-1. -/
theorem algClosureHalfX_flip_ab_add_one_product
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1) :
    (algClosureHalfX x a b c + 1) *
      (algClosureHalfX x (-a) (-b) c + 1) = 2 := by
  rw [algClosureHalfX_add_one_factor ha hc]
  have ha' : (-a) ^ 2 = x := by simpa using ha
  have hc' : c ^ 2 = x + 1 := hc
  have hflip :=
    algClosureHalfX_add_one_factor
      (x := x) (a := -a) (b := -b) (c := c) ha' hc'
  rw [hflip]
  have hac : (a + c) * (c - a) = 1 := by
    nlinarith [ha, hc]
  have hbc : (b + c) * (c - b) = 2 := by
    nlinarith [hb, hc]
  calc
    (a + c) * (b + c) * ((-a + c) * (-b + c))
        = ((a + c) * (c - a)) * ((b + c) * (c - b)) := by ring
    _ = 2 := by rw [hac, hbc]; norm_num

/-- The three even sign flips preserve the sign condition abc=-y. -/
theorem algClosureHalf_even_sign_flips_preserve_product
    {y : RatAlgClosure}
    (habc : a * b * c = -y) :
    (a * (-b) * (-c) = -y) ∧
    ((-a) * b * (-c) = -y) ∧
    ((-a) * (-b) * c = -y) := by
  constructor
  · simpa using habc
  constructor <;> simpa using habc

/-!
MAX-CUT STATUS

PAID HERE (subject to exact-head Lean certification):
* exact factorization of the selected half x-coordinate;
* exact x-coordinate relations for all three nontrivial even sign flips;
* exact preservation of the half-point sign constraint `abc=-y`.

DECISIVE NEXT ARITHMETIC OWNER:
* prove on the actual selected Mathlib elliptic group that translation by
  (0,0), (1,0), (-1,0) has precisely these three x-coordinate relations;
* use y-coordinate equality / uniqueness to identify the flipped half with
  Q+T for each literal two-torsion point;
* conclude the raw geometric Kummer coordinates are `(sign b, sign a)` and
  therefore `CMGeometricXTKummerOrientationTheorem`.

No H¹ or Selmer architecture remains in this global comparison step.
-/

end

end Synthesis.Millennium.BSD
