import Synthesis.MillenniumHodgeDicksonOriginalQ0SignedPartnerInvolutionExact

/-!
Section40 original Dickson six-address signed quadratic deck.

Apply the SAME original Q0 partner to each of the six real address
coordinates. This is the ALL-SIX source operation, not a generic
surrogate involution. Every Q0 source equation survives, each
original signed derivative reverses, and the derivative square
(discriminant) is exactly invariant. This is a true local six-sheet
gluing input; it does not yet prove original global projective
homogenization, Chow cycle or primitive Hodge pairing.

No independent root choice or analytic branch cut. Pending native Lean.
-/
namespace DASHI.Hodge.DicksonCoupled
open scoped BigOperators
noncomputable section

variable {F : Type*} [Field F] [CharZero F]

def originalQ0AllSixPartner (a s : Address → F) : Address → F :=
  fun i => originalQ0SignedPartner (a i) (s i)

/-- The complete six-coordinate root polynomial profile is
unchanged, at each original address, by the same Q0 partner. -/
theorem original_Q0_all_six_partner_preserves_profile
    (a s : Address → F) :
    ∀ i : Address,
      Q0Field (a i) (originalQ0AllSixPartner a s i) =
        Q0Field (a i) (s i) := by
  intro i
  exact original_Q0_partner_preserves_original_equation (a i) (s i)

/-- The signed Jacobian changes sign at EACH original address,
not just at a selected numerical sample or deck anchor. -/
theorem original_Q0_all_six_partner_derivative_flip
    (a s : Address → F) :
    ∀ i : Address,
      dField (a i) (originalQ0AllSixPartner a s i) =
        -dField (a i) (s i) := by
  intro i
  exact original_Q0_partner_flips_signed_derivative (a i) (s i)

/-- The actual squared signed discriminant profile remains
invariant at all six addresses, including at the fold locus. -/
theorem original_Q0_all_six_partner_discriminant_invariant
    (a s : Address → F) :
    ∀ i : Address,
      (dField (a i) (originalQ0AllSixPartner a s i))^2 =
        (dField (a i) (s i))^2 := by
  intro i
  rw [original_Q0_all_six_partner_derivative_flip a s i]
  ring

/-- One true six-coordinate quadratic deck involution, not six
independent choices that could discard the signed coupling. -/
theorem original_Q0_all_six_partner_involution
    (a s : Address → F) :
    originalQ0AllSixPartner a (originalQ0AllSixPartner a s) = s := by
  funext i
  exact original_Q0_partner_involution (a i) (s i)

/-- All six signed quadratic root derivatives vanish exactly where
the original six-coordinate partner is fixed. This separates
the fold locus from the generic nontrivial deck orbits. -/
theorem original_Q0_all_six_partner_fixed_iff
    (a s : Address → F) :
    originalQ0AllSixPartner a s = s ↔
      ∀ i : Address, dField (a i) (s i) = 0 := by
  constructor
  · intro h i
    have hi := congrFun h i
    exact (original_Q0_partner_fixed_iff_branch (a i) (s i)).mp hi
  · intro h
    funext i
    exact (original_Q0_partner_fixed_iff_branch (a i) (s i)).mpr (h i)

end
end DASHI.Hodge.DicksonCoupled
