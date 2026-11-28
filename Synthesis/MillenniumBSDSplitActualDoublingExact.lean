import Synthesis.MillenniumBSDSplitCyclicCocycleExact

namespace DASHI.BSD.SplitTangent
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [CharZero F]
variable (W : WeierstrassCurve F) [W.IsElliptic]

/-- The reverse-solved point has nonzero ordinate even when the target
ordinate is zero: pair sums cannot vanish for distinct roots. -/
theorem reverseHalfY_nonzero_of_distinct (x r s t a b c : F)
    (hr : r^2=x-a) (hs : s^2=x-b) (ht : t^2=x-c)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    reverseHalfY r s t ≠ 0 := by
  have hrs := reverseHalf_pair_nonzero r s a b x hr hs hab
  have hst := reverseHalf_pair_nonzero s t b c x hs ht hbc
  have htr := reverseHalf_pair_nonzero t r c a x ht hr hac.symm
  unfold reverseHalfY
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hrs hst) htr)

/-- The actual Mathlib tangent formula is paid by the root identities;
no assumption that the reverse-solved point is already a half. -/
theorem reverseHalf_actual_double (a b c : F) (h : SplitCoefficients W a b c)
    (x y r s t : F) (hr : r^2=x-a) (hs : s^2=x-b) (ht : t^2=x-c)
    (hp : r*s*t= -y) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (hP : W.toAffine.Nonsingular x y) :
    (2:ℕ) • reverseHalfPoint W a b c h x r s t hr hs ht =
      WeierstrassCurve.Affine.Point.some hP := by
  let X := reverseHalfX x r s t
  let Y := reverseHalfY r s t
  let m := -(r+s+t)
  have hy0 : Y≠0 := reverseHalfY_nonzero_of_distinct x r s t a b c hr hs ht hab hac hbc
  have hn : Y≠W.toAffine.negY X Y := by
    intro he
    unfold WeierstrassCurve.Affine.negY at he
    rw [h.a1_zero,h.a3_zero] at he
    apply hy0
    linear_combination (1/2:F)*he
  have ha : a=x-r^2 := by linear_combination hr
  have hb : b=x-s^2 := by linear_combination hs
  have hc : c=x-t^2 := by linear_combination ht
  have htan : 3*X^2+2*W.a₂*X+W.a₄-W.a₁*Y =
      m*(Y-W.toAffine.negY X Y) := by
    unfold X Y m reverseHalfX reverseHalfY pairSum WeierstrassCurve.Affine.negY
    rw [h.a1_zero,h.a3_zero,h.a2_eq,h.a4_eq,ha,hb,hc]
    ring
  have hsl : W.toAffine.slope X X Y Y=m := by
    rw [W.toAffine.slope_of_Y_ne rfl hn]
    exact (div_eq_iff (sub_ne_zero.mpr hn)).mpr htan
  have hx : W.toAffine.addX X X m=x := by
    unfold WeierstrassCurve.Affine.addX X m reverseHalfX pairSum
    rw [h.a1_zero,h.a2_eq,ha,hb,hc]
    ring
  have hy : W.toAffine.addY X X Y m=y := by
    unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    rw [hx]
    unfold WeierstrassCurve.Affine.negY X Y m reverseHalfX reverseHalfY pairSum
    rw [h.a1_zero,h.a3_zero]
    linear_combination -hp
  rw [two_nsmul]
  unfold reverseHalfPoint
  change (.some _ : W.toAffine.Point)+.some _=.some hP
  rw [WeierstrassCurve.Affine.Point.add_some (fun he=>hn he.2)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨by simpa [X,Y,hsl] using hx,by simpa [X,Y,hsl] using hy⟩

end
end DASHI.BSD.SplitTangent
