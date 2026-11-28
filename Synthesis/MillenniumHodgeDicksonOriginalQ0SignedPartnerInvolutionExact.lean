import Synthesis.MillenniumHodgeDicksonOriginalQ0SignedJacobianJetExact

/-!
Section39 — exact original Dickson quadratic Q0 signed partner
from the ORIGINAL polynomial first jet, no chosen square-root sign.

For every original chart coefficient a and root coordinate s:
  partner(s) = s + dField(a,s)/2
  Q0(a,partner(s)) = Q0(a,s)
  dField(a,partner(s)) = -dField(a,s)
  partner(partner(s)) = s.

The construction works also on the discriminant fold, where the
two roots merge: partner(s)=s iff dField(a,s)=0.
This is a genuine all-field original deck involution and exact
branch-locus criterion. It does NOT globally extend the actual
projective 10-deck cover or produce a primitive Chow cycle.

All assertions are source-written pending native Lean/Lake admission.
-/
namespace DASHI.Hodge.DicksonCoupled
noncomputable section

variable {F : Type*} [Field F] [CharZero F]

/-- Canonical other root from the original first-jet derivative.
No independent square root, selected chart orientation or division
by the discriminant: 2 is invertible from field characteristic 0. -/
def originalQ0SignedPartner (a s : F) : F :=
  s + dField a s / 2

theorem original_Q0_partner_preserves_original_equation
    (a s : F) :
    Q0Field a (originalQ0SignedPartner a s) = Q0Field a s := by
  have h := original_Q0_signed_first_jet a s (dField a s / 2)
  apply sub_eq_zero.mp
  calc
    Q0Field a (originalQ0SignedPartner a s) - Q0Field a s =
        (dField a s / 2) *
          (dField a s - 2 * (dField a s / 2)) := by
            simpa [originalQ0SignedPartner] using h
    _ = 0 := by ring

/-- The original signed root derivative reverses exactly under
the selected quadratic involution, even at a branch double root. -/
theorem original_Q0_partner_flips_signed_derivative
    (a s : F) :
    dField a (originalQ0SignedPartner a s) = -dField a s := by
  unfold originalQ0SignedPartner dField
  ring

/-- Global algebraic involution on this original quadratic
coordinate, without postulating a deck-transformation action. -/
theorem original_Q0_partner_involution (a s : F) :
    originalQ0SignedPartner a (originalQ0SignedPartner a s) = s := by
  change originalQ0SignedPartner a s +
      dField a (originalQ0SignedPartner a s) / 2 = s
  rw [original_Q0_partner_flips_signed_derivative]
  unfold originalQ0SignedPartner
  ring

/-- The branch/fixed locus equals vanishing of the ACTUAL
root-direction Jacobian, not a separately fitted discriminant. -/
theorem original_Q0_partner_fixed_iff_branch (a s : F) :
    originalQ0SignedPartner a s = s ↔ dField a s = 0 := by
  unfold originalQ0SignedPartner
  constructor
  · intro h
    have hz : dField a s / 2 = 0 := by
      apply add_left_cancel (a := s)
      simpa using h
    have htwo : (2 : F) ≠ 0 := by norm_num
    exact (div_eq_zero_iff).mp hz |>.resolve_right htwo
  · intro h
    simp [h]

/-- At each original nonbranch point, the partner is DISTINCT,
and has opposite signed derivative. This is the exact elementary
local two-sheet deck source behind the existing 5+5 construction. -/
theorem original_Q0_partner_distinct_off_branch
    (a s : F) (hs : dField a s ≠ 0) :
    originalQ0SignedPartner a s ≠ s ∧
      dField a (originalQ0SignedPartner a s) = -dField a s := by
  constructor
  · intro heq
    exact hs ((original_Q0_partner_fixed_iff_branch a s).mp heq)
  · exact original_Q0_partner_flips_signed_derivative a s

end
end DASHI.Hodge.DicksonCoupled
