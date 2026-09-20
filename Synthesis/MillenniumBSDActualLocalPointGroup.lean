import Synthesis.MillenniumBSDTotalLocalKummer
import Synthesis.MillenniumBSDOddPrimeGoodReduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Tactic

/-!
# Replace the bespoke local point carrier by the actual elliptic point group

`PadicProjectivePoint p` was introduced before the local descent layer needed
the elliptic group law.  It is the correct underlying set (one point at
infinity plus affine solutions of y²=x³-x), but by itself it carries no
addition.

Mathlib's `WeierstrassCurve.Affine.Point` for the literal p-adic
Weierstrass model is the actual elliptic point group.  This file proves an
explicit equivalence between the two carriers and transfers the genuine
additive commutative group structure back to `PadicProjectivePoint p`.

After this file, expressions such as `P + Q` in the local Kummer theorem are
no longer shorthand: they are the actual elliptic group law.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

theorem cmPadic_equation_iff
    (p : ℕ) [Fact p.Prime]
    (x y : ℚ_[p]) :
    (cmPadicWeierstrass p).toAffine.Equation x y ↔
      y ^ 2 = x ^ 3 - x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [cmPadicWeierstrass, cmWeierstrass]
  ring_nf

noncomputable def padicProjectivePointEquivMathlib
    (p : ℕ) [Fact p.Prime] :
    PadicProjectivePoint p ≃
      (cmPadicWeierstrass p).toAffine.Point where
  toFun
    | .infinity => .zero
    | .affine x y h =>
        WeierstrassCurve.Affine.Point.mk
          ((cmPadic_equation_iff p x y).mpr h)
  invFun
    | .zero => .infinity
    | .some x y h =>
        .affine x y
          ((cmPadic_equation_iff p x y).mp
            (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h))
  left_inv := by
    intro P
    cases P with
    | infinity => rfl
    | affine x y h =>
        rfl
  right_inv := by
    intro P
    cases P with
    | zero => rfl
    | some x y h =>
        rfl

noncomputable instance padicProjectivePointAddCommGroup
    (p : ℕ) [Fact p.Prime] :
    AddCommGroup (PadicProjectivePoint p) :=
  (padicProjectivePointEquivMathlib p).addCommGroup

noncomputable def padicProjectivePointAddEquivMathlib
    (p : ℕ) [Fact p.Prime] :
    PadicProjectivePoint p ≃+
      (cmPadicWeierstrass p).toAffine.Point :=
  (padicProjectivePointEquivMathlib p).addEquiv

@[simp] theorem padicProjective_zero_eq_infinity
    (p : ℕ) [Fact p.Prime] :
    (0 : PadicProjectivePoint p) = .infinity := by
  apply (padicProjectivePointEquivMathlib p).injective
  simp [padicProjectivePointAddEquivMathlib]

theorem padicProjective_add_transport
    (p : ℕ) [Fact p.Prime]
    (P Q : PadicProjectivePoint p) :
    padicProjectivePointEquivMathlib p (P + Q)
      =
    padicProjectivePointEquivMathlib p P
      + padicProjectivePointEquivMathlib p Q := by
  exact (padicProjectivePointAddEquivMathlib p).map_add P Q

def TotalLocalKummerHomomorphismStatement
    (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ P Q : PadicProjectivePoint p,
    totalLocalKummer p (P + Q)
      =
    totalLocalKummer p P * totalLocalKummer p Q

theorem localKummerMulClosed_of_total_homomorphism
    (p : ℕ) [Fact p.Prime]
    (hδ : TotalLocalKummerHomomorphismStatement p) :
    LocalKummerMulClosed p := by
  intro a b ha hb
  rcases ha with ⟨P, rfl⟩
  rcases hb with ⟨Q, rfl⟩
  refine ⟨P + Q, ?_⟩
  exact hδ P Q

end Synthesis.Millennium.BSD
