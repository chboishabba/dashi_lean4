import Synthesis.MillenniumBSDCMGaloisRootSignExact
import Synthesis.MillenniumBSDCMExplicitRootBitOrientationExact
import Mathlib.Tactic

/-!
# Selected CM curve: σQ-Q is literally the root-sign E[2] element

This is the decisive finite arithmetic theorem in the selected-curve global
Kummer comparison.  On the actual custom Qbar elliptic point group, for the
explicit half Q built from a²=x, b²=x-1, c²=x+1 and abc=-y,

  σQ - Q = E2Equiv(bit(b), bit(a)).

The order `(bit b, bit a)` is forced by the already-paid finite table:
`(1,0)` is `(0,0)` and `(0,1)` is `(1,0)`.
-/

namespace Synthesis.Millennium.BSD

noncomputable section

private theorem explicitRootBit_zero_of_fixed
    (σ : RationalAbsoluteGalois)
    {r : RatAlgClosure} (h : σ r = r) :
    rationalKummerBitOfRoot r σ = 0 := by
  simp [rationalKummerBitOfRoot, h]

private theorem explicitRootBit_one_of_neg
    (σ : RationalAbsoluteGalois)
    {r : RatAlgClosure} (hr0 : r ≠ 0) (h : σ r = -r) :
    rationalKummerBitOfRoot r σ = 1 := by
  have hne : σ r ≠ r := by
    rw [h]
    intro heq
    exact hr0 ((CharZero.neg_eq_self_iff).mp heq)
  simp [rationalKummerBitOfRoot, hne]

/-- The custom coordinate action on the explicit half differs from the half by
exactly the E[2] element encoded by the signs of b and a. -/
theorem cmExplicitHalf_galoisDifference_eq_rootBits
    (σ : RationalAbsoluteGalois)
    {x y a b c : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy0 : y ≠ 0)
    (ha : a ^ 2 = x)
    (hb : b ^ 2 = x - 1)
    (hc : c ^ 2 = x + 1)
    (habc : a * b * c = -y)
    (hx : σ x = x)
    (hy : σ y = y) :
    let Q := cmExplicitHalfPoint x y a b c ha hb hc habc
    cmAlgClosureGaloisAction σ Q - Q =
      (cmAlgClosureTwoTorsionEquiv
        (rationalKummerBitOfRoot b σ,
          rationalKummerBitOfRoot a σ)).1 := by
  dsimp
  have ha0 : a ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow] at ha
    have hx0 : x = 0 := ha.symm
    rw [hx0] at hcurve
    have : y = 0 := by
      have hy2 : y ^ 2 = 0 := by simpa using hcurve
      exact sq_eq_zero_iff.mp hy2
    exact hy0 this
  have hb0 : b ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow] at hb
    have hx1 : x = 1 := by linarith
    rw [hx1] at hcurve
    have : y = 0 := by
      have hy2 : y ^ 2 = 0 := by norm_num at hcurve ⊢; exact hcurve
      exact sq_eq_zero_iff.mp hy2
    exact hy0 this

  rcases cmGalois_half_even_sign_patterns σ hy0 ha hb hc habc hx hy with
      hnone | hbc | hac | hab
  · have hQa : cmAlgClosureGaloisAction σ
        (cmExplicitHalfPoint x y a b c ha hb hc habc) =
        cmExplicitHalfPoint x y a b c ha hb hc habc := by
      simp [cmAlgClosureGaloisAction, cmExplicitHalfPoint,
        algClosureHalfX, algClosureHalfY,
        hx, hy, hnone.1, hnone.2.1, hnone.2.2]
    have hba :
        (rationalKummerBitOfRoot b σ,
          rationalKummerBitOfRoot a σ) = (0, 0) := by
      apply Prod.ext
      · exact explicitRootBit_zero_of_fixed σ hnone.2.1
      · exact explicitRootBit_zero_of_fixed σ hnone.1
    rw [hQa, sub_self, hba]
    simp
  · have hQbc : cmAlgClosureGaloisAction σ
        (cmExplicitHalfPoint x y a b c ha hb hc habc) =
        cmExplicitHalfPoint x y a (-b) (-c)
          ha (by simpa using hb) (by simpa using hc)
          ((algClosureHalf_even_sign_flips_preserve_product habc).1) := by
      simp [cmAlgClosureGaloisAction, cmExplicitHalfPoint,
        algClosureHalfX, algClosureHalfY,
        hx, hy, hbc.1, hbc.2.1, hbc.2.2]
    have htrans := cmExplicitHalf_flip_bc_eq_add_torsion0
      hcurve hy0 ha hb hc habc
    have hba :
        (rationalKummerBitOfRoot b σ,
          rationalKummerBitOfRoot a σ) = (1, 0) := by
      apply Prod.ext
      · exact explicitRootBit_one_of_neg σ hb0 hbc.2.1
      · exact explicitRootBit_zero_of_fixed σ hbc.1
    rw [hQbc, ← htrans]
    simp [hba]
  · have hQac : cmAlgClosureGaloisAction σ
        (cmExplicitHalfPoint x y a b c ha hb hc habc) =
        cmExplicitHalfPoint x y (-a) b (-c)
          (by simpa using ha) hb (by simpa using hc)
          ((algClosureHalf_even_sign_flips_preserve_product habc).2.1) := by
      simp [cmAlgClosureGaloisAction, cmExplicitHalfPoint,
        algClosureHalfX, algClosureHalfY,
        hx, hy, hac.1, hac.2.1, hac.2.2]
    have htrans := cmExplicitHalf_flip_ac_eq_add_torsion1
      hcurve hy0 ha hb hc habc
    have hba :
        (rationalKummerBitOfRoot b σ,
          rationalKummerBitOfRoot a σ) = (0, 1) := by
      apply Prod.ext
      · exact explicitRootBit_zero_of_fixed σ hac.2.1
      · exact explicitRootBit_one_of_neg σ ha0 hac.1
    rw [hQac, ← htrans]
    simp [hba]
  · have hQab : cmAlgClosureGaloisAction σ
        (cmExplicitHalfPoint x y a b c ha hb hc habc) =
        cmExplicitHalfPoint x y (-a) (-b) c
          (by simpa using ha) (by simpa using hb) hc
          ((algClosureHalf_even_sign_flips_preserve_product habc).2.2) := by
      simp [cmAlgClosureGaloisAction, cmExplicitHalfPoint,
        algClosureHalfX, algClosureHalfY,
        hx, hy, hab.1, hab.2.1, hab.2.2]
    have htrans := cmExplicitHalf_flip_ab_eq_add_torsionNeg1
      hcurve hy0 ha hb hc habc
    have hba :
        (rationalKummerBitOfRoot b σ,
          rationalKummerBitOfRoot a σ) = (1, 1) := by
      apply Prod.ext
      · exact explicitRootBit_one_of_neg σ hb0 hab.2.1
      · exact explicitRootBit_one_of_neg σ ha0 hab.1
    rw [hQab, ← htrans]
    simp [hba]

/-- Rational-coordinate specialization: the finite Galois difference is the
paid scalar Kummer bit pair in raw geometric order. -/
theorem cmExplicitHalf_galoisDifference_eq_paidKummerBits
    (σ : RationalAbsoluteGalois)
    {x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy0 : y ≠ 0)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    {a b c : RatAlgClosure}
    (ha : a ^ 2 = (x : RatAlgClosure))
    (hb : b ^ 2 = (x : RatAlgClosure) - 1)
    (hc : c ^ 2 = (x : RatAlgClosure) + 1)
    (habc : a * b * c = -(y : RatAlgClosure)) :
    let Q := cmExplicitHalfPoint (x : RatAlgClosure) (y : RatAlgClosure)
      a b c ha hb hc habc
    cmAlgClosureGaloisAction σ Q - Q =
      (cmAlgClosureTwoTorsionEquiv
        (rationalKummerBit ⟨x - 1, sub_ne_zero.mpr hx1⟩ σ,
          rationalKummerBit ⟨x, hx0⟩ σ)).1 := by
  dsimp
  have hcurve' :
      (y : RatAlgClosure) ^ 2 =
        (x : RatAlgClosure) ^ 3 - (x : RatAlgClosure) := by
    exact_mod_cast hcurve
  have hy0' : (y : RatAlgClosure) ≠ 0 := by exact_mod_cast hy0
  have h := cmExplicitHalf_galoisDifference_eq_rootBits σ
    hcurve' hy0' ha hb hc habc (by simp) (by simp)
  rw [rationalKummerBit_sub_one_eq_explicitRoot σ hx1 hb,
    rationalKummerBit_eq_explicitRoot σ hx0 ha]
  exact h

/-!
MAX-CUT STATUS

PAID HERE, subject to exact-head kernel certification:
* the four sign rows are compiled to a single formula on the actual custom
  elliptic group;
* σQ-Q is exactly E2Equiv(bit b,bit a);
* for rational x the two bits are exactly the already-paid scalar Kummer bits
  for x-1 and x.

There is no finite-arithmetic ambiguity left in the selected ordinary-point
comparison.  The remaining ordinary global theorem is only transport of this
same literal E[2] element through the already-existing custom-point/generic-
point and actual-E[2]/trivial-E[2] equivalences used by
`cmGeometricKummerTrivialCharacter`.
-/

end

end Synthesis.Millennium.BSD
