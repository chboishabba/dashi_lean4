import Synthesis.MillenniumHodgeDicksonOriginalCoupledSixSignedDeckExact

/-!
Section41 continuation: the actual sixfold Q0 partner is a true
order-two PERMUTATION of the ORIGINAL coupled root fibre.

On the original punctured incidence δ != 0, it has NO fixed points:
the original signed-product source forces every derivative coordinate
to be nonzero. This is a genuine free C2 deck action on the ACTUAL
signed-product fibre, not an independent quadratic coordinate action.

Native Lean checking pending. A free finite fibre action alone is NOT
global projective Chow-cycle existence or Hodge nonzero pairing.
-/
namespace DASHI.Hodge.DicksonCoupled
noncomputable section

variable {F : Type*} [Field F] [CharZero F]

/-- The true original sixfold partner as a permutation of the ACTUAL
coupled signed-product root incidence, with its own inverse. -/
def originalQ0CoupledSixPartnerEquiv
    (a y : Address → F) (δ : F) :
    Equiv.Perm (ActualRootFibre a y δ) where
  toFun := originalQ0CoupledSixPartner a y δ
  invFun := originalQ0CoupledSixPartner a y δ
  left_inv := original_Q0_coupled_six_partner_involution a y δ
  right_inv := original_Q0_coupled_six_partner_involution a y δ

/-- The original signed coupling δ != 0 prohibits a fixed point
of the all-six partner: at least one source derivative would then
vanish, forcing the entire actual signed product to vanish. -/
theorem original_Q0_coupled_partner_no_fixed_on_puncture
    (a y : Address → F) (δ : F) (hδ : δ ≠ 0)
    (s : ActualRootFibre a y δ) :
    originalQ0CoupledSixPartner a y δ s ≠ s := by
  intro he
  have hp : originalQ0AllSixPartner a s.1 = s.1 :=
    congrArg Subtype.val he
  have hall := (original_Q0_all_six_partner_fixed_iff a s.1).mp hp
  have hzero : dField (a (0 : Address)) (s.1 (0 : Address)) = 0 :=
    hall 0
  have hnonzero : dField (a (0 : Address)) (s.1 (0 : Address)) ≠ 0 := by
    have hd := signedFibre_nonzero
      ((actualRootFibreEquiv a y δ) s) hδ (0 : Address)
    exact hd
  exact hnonzero hzero

/-- The real original punctured coupled fibre decomposes into
two-element partner orbits: each point differs from its image,
and applying the same action twice gives the ORIGINAL point.
This does not yet count the global projective monodromy or Chow. -/
theorem original_Q0_coupled_punctured_partner_two_cycle
    (a y : Address → F) (δ : F) (hδ : δ ≠ 0)
    (s : ActualRootFibre a y δ) :
    originalQ0CoupledSixPartner a y δ s ≠ s ∧
      originalQ0CoupledSixPartner a y δ
        (originalQ0CoupledSixPartner a y δ s) = s := by
  exact ⟨original_Q0_coupled_partner_no_fixed_on_puncture
      a y δ hδ s,
    original_Q0_coupled_six_partner_involution a y δ s⟩

end
end DASHI.Hodge.DicksonCoupled
