import Synthesis.MillenniumBSDCMFiniteE2SignTableExact
import Mathlib.Tactic

/-!
# Selected CM curve: Galois action on a chosen half has an even root-sign pattern

For the selected half roots

  a² = x,  b² = x-1,  c² = x+1,  abc = -y,

an absolute-Galois automorphism fixing the rational target coordinates x,y can
only send each root to itself or its negative.  The product constraint and
`y ≠ 0` exclude the four odd sign patterns.  Hence the action lands in exactly
the four rows already identified with the literal E[2] table.

This file is deliberately pre-cohomological.  It pays the finite Galois/sign
classification on the same Qbar roots used by the explicit half.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

noncomputable section

/-- A Galois automorphism fixing the square of a chosen square root sends that
root to itself or its negative. -/
theorem cmGalois_sqrt_eq_self_or_neg
    (σ : RationalAbsoluteGalois)
    {x a : RatAlgClosure}
    (ha : a ^ 2 = x)
    (hx : σ x = x) :
    σ a = a ∨ σ a = -a := by
  apply (sq_eq_sq_iff_eq_or_eq_neg).mp
  calc
    (σ a) ^ 2 = σ (a ^ 2) := by simp
    _ = σ x := by rw [ha]
    _ = x := hx
    _ = a ^ 2 := ha.symm

/-- Under the selected half product constraint, the three individual root
signs have even parity.  The result is stated directly as the four concrete
sign patterns rather than introducing a parallel sign carrier. -/
theorem cmGalois_half_even_sign_patterns
    (σ : RationalAbsoluteGalois)
    {x y a b c : RatAlgClosure}
    (hy0 : y ≠ 0)
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y)
    (hx : σ x = x)
    (hy : σ y = y) :
    ((σ a = a) ∧ (σ b = b) ∧ (σ c = c)) ∨
    ((σ a = a) ∧ (σ b = -b) ∧ (σ c = -c)) ∨
    ((σ a = -a) ∧ (σ b = b) ∧ (σ c = -c)) ∨
    ((σ a = -a) ∧ (σ b = -b) ∧ (σ c = c)) := by
  have hxa := cmGalois_sqrt_eq_self_or_neg σ ha hx
  have hxb : σ b = b ∨ σ b = -b := by
    apply cmGalois_sqrt_eq_self_or_neg σ hb
    simpa [hx]
  have hxc : σ c = c ∨ σ c = -c := by
    apply cmGalois_sqrt_eq_self_or_neg σ hc
    simpa [hx]

  have hprod : (σ a) * (σ b) * (σ c) = a * b * c := by
    calc
      (σ a) * (σ b) * (σ c) = σ (a * b * c) := by simp
      _ = σ (-y) := by rw [habc]
      _ = -y := by simp [hy]
      _ = a * b * c := habc.symm

  have habc0 : a * b * c ≠ 0 := by
    rw [habc]
    exact neg_ne_zero.mpr hy0

  rcases hxa with hxa | hxa <;>
    rcases hxb with hxb | hxb <;>
    rcases hxc with hxc | hxc
  · exact Or.inl ⟨hxa, hxb, hxc⟩
  · exfalso
    rw [hxa, hxb, hxc] at hprod
    apply habc0
    have : (2 : RatAlgClosure) * (a * b * c) = 0 := by
      linear_combination hprod
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  · exfalso
    rw [hxa, hxb, hxc] at hprod
    apply habc0
    have : (2 : RatAlgClosure) * (a * b * c) = 0 := by
      linear_combination hprod
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  · exact Or.inr (Or.inl ⟨hxa, hxb, hxc⟩)
  · exfalso
    rw [hxa, hxb, hxc] at hprod
    apply habc0
    have : (2 : RatAlgClosure) * (a * b * c) = 0 := by
      linear_combination hprod
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  · exact Or.inr (Or.inr (Or.inl ⟨hxa, hxb, hxc⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hxa, hxb, hxc⟩))
  · exfalso
    rw [hxa, hxb, hxc] at hprod
    apply habc0
    have : (2 : RatAlgClosure) * (a * b * c) = 0 := by
      linear_combination hprod
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)

/-!
MAX-CUT STATUS

PAID HERE, subject to exact-head kernel certification:
* each selected square root has literal ±1 Galois sign;
* the product constraint excludes every odd sign pattern;
* every Galois action on a non-two-torsion selected half therefore lands in
  exactly one of the four rows already identified by
  `cmExplicitHalf_even_sign_E2_table`.

NEXT SAME-OBJECT WELD:
* evaluate `galoisPointMap` on `cmExplicitHalfPoint` in these four cases;
* invoke the three actual translation equalities from
  `MillenniumBSDCMFiniteE2SignTableExact` to compute `σ Q - Q` in literal E[2];
* transport that pointwise character through
  `cmGenericKummerE2H1MulEquivRatSquareClasses` and identify it with the
  existing explicit x-T class.
-/

end

end Synthesis.Millennium.BSD
