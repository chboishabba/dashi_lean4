import Synthesis.MillenniumHodgeDicksonOriginalAllSixQ0PartnerExact
import Synthesis.MillenniumHodgeDicksonGenericSignedFibreExact

/-!
Section41 — weld the ORIGINAL six-address Q0 partner into the
ORIGINAL COUPLED signed-product fibre.

Section40 paid individual Q0 equations, discriminant squares and
derivative signs, but did NOT pay the crucial actual orientation
constraint: the product of SIX signed derivatives equals δ.

Because the original address carrier is Fin 6, simultaneously
reversing every sign multiplies the orientation by (-1)^6 = +1.
The same global partner thus acts ON ActualRootFibre(a,y,δ),
not only on independent quadratic roots. It is an involution and
is equivariant under the pre-existing signed-fibre equivalence.

This is genuine original geometric glue, not a claim of global
projective cycle or primitive Hodge class. Native Lean unrun.
-/
namespace DASHI.Hodge.DicksonCoupled
open scoped BigOperators
noncomputable section

variable {F : Type*} [Field F] [CharZero F]

/-- The canonical all-negative sign is an ACTUAL even deck element
because the original carrier has six, not five or seven, addresses. -/
def originalAllSixNegativeEvenDeck : EvenDeck F where
  val := fun _ => -1
  property := by
    constructor
    · intro i
      ring
    · simp [Fin.prod_univ_succ]

/-- The original signed derivative PRODUCT is invariant under the
simultaneous actual quadratic Q0 partner. This pays the specific
orientation obstruction omitted by the componentwise source. -/
theorem original_Q0_six_partner_preserves_signed_product
    (a s : Address → F) :
    (∏ i : Address,
      dField (a i) (originalQ0AllSixPartner a s i)) =
      (∏ i : Address, dField (a i) (s i)) := by
  calc
    (∏ i : Address,
      dField (a i) (originalQ0AllSixPartner a s i)) =
      ∏ i : Address, ((-1 : F) * dField (a i) (s i)) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [original_Q0_all_six_partner_derivative_flip]
        ring
    _ = (∏ i : Address, (-1 : F)) *
          (∏ i : Address, dField (a i) (s i)) := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ i : Address, dField (a i) (s i)) := by
          have he := (originalAllSixNegativeEvenDeck (F := F)).property.2
          simpa using congrArg
            (fun t : F => t * (∏ i : Address, dField (a i) (s i)))
            he

/-- The actual ORIGINAL coupled root incidence is stable under
simultaneously changing all six Q0 roots. No independent coordinate
choice is made; the signed δ orientation remains the SAME. -/
def originalQ0CoupledSixPartner (a y : Address → F) (δ : F) :
    ActualRootFibre a y δ → ActualRootFibre a y δ :=
  fun s => ⟨originalQ0AllSixPartner a s.1, by
    constructor
    · intro i
      rw [original_Q0_all_six_partner_preserves_profile]
      exact s.2.1 i
    · rw [original_Q0_six_partner_preserves_signed_product]
      exact s.2.2⟩

/-- It is an involution ON THE TRUE source fibre, not merely
on six unrelated copies of a quadratic equation. -/
theorem original_Q0_coupled_six_partner_involution
    (a y : Address → F) (δ : F)
    (s : ActualRootFibre a y δ) :
    originalQ0CoupledSixPartner a y δ
      (originalQ0CoupledSixPartner a y δ s) = s := by
  apply Subtype.ext
  exact original_Q0_all_six_partner_involution a s.1

/-- Under the existing ORIGINAL root↔signed-derivative equivalence,
the all-six partner becomes multiplication by the nontrivial
global even-sign deck element; coupling is retained. -/
theorem original_Q0_coupled_six_partner_signed_fibre_equivariant
    (a y : Address → F) (δ : F)
    (s : ActualRootFibre a y δ) :
    (actualRootFibreEquiv a y δ
      (originalQ0CoupledSixPartner a y δ s)).1 =
    (fun i => (originalAllSixNegativeEvenDeck (F := F)).1 i *
      (actualRootFibreEquiv a y δ s).1 i) := by
  funext i
  exact original_Q0_all_six_partner_derivative_flip a s.1 i

end
end DASHI.Hodge.DicksonCoupled
