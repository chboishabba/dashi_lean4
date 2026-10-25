import Integration.Griess1990MoufangOriginal240Action
import Integration.Griess1990Original240E8WeylPrime13Obstruction
import Mathlib

/-!
# Source-selected order-13 obstruction with only THREE corrected M81 shears

Mathematical source: R. L. Griess Jr., J. Algebra 131 (1990),
281–293, DOI 10.1016/0021-8693(90)90176-O (phase polynomial and M81).
DASHI computed the short source-corrected word and checked every point.

Shear word: e01, then e12, then e20 (composition right-to-left).
Grade matrix over F3:
   [1 1 0]
   [0 1 1]
   [1 1 1].
The *corrected full-loop* lift has order exactly 13:
  M81:       3 fixed + 6 * (13-cycle) = 81
  originalT5:6 fixed + 18 * (13-cycle) = 240.

This is a much cheaper exact verification than a permutation-group
order computation on 151632 elements. Any root-system automorphism of
the *fixed E8 root datum* belongs to Weyl(E8), of order 696729600,
not divisible by 13. Thus no bijective same-action intertwiner can
send this explicit original-T5 source automorphism to an actual
E8 Weyl-root permutation. It does not rule out unrelated bijections.

The cyclic formulae and finite proof obligations here are SOURCE
WRITTEN only; Lean kernel was unavailable in the authoring environment.
-/

namespace Integration.Griess1990Moufang81Explicit13Cycle

open Integration.Griess1990Moufang81Determinant
open Integration.Griess1990Moufang81ElementaryLift
open Integration.Griess1990OriginalT5Moufang243240Chart
open Integration.Griess1990MoufangOriginal240Action
open Integration.Griess1990Original240E8WeylPrime13Obstruction

def shortOrder13Lift (m : Loop81) : Loop81 :=
  lift .e20 (lift .e12 (lift .e01 m))

def shortOrder13OnOld240 (z : Old240) : Old240 :=
  actOnOriginal240 .e20 (actOnOriginal240 .e12 (actOnOriginal240 .e01 z))

/-- The exact first image is an externally reproducible orientation
and central-phase discriminator. A grade-only (uncorrected) lift
gives the wrong central coefficient 2. -/
def selectedWitness : Loop81 := ⟨![1,0,0],0⟩

theorem first_lifted_image :
    shortOrder13Lift selectedWitness = ⟨![1,0,1],2⟩ := by
  native_decide

/-- One element with exact prime order 13 is sufficient to block
a conjugate E8 root-system automorphism, even WITHOUT reconstructing
the complete 151632-element source group. -/
theorem source_short_lift_order_thirteen :
    ∀ m : Loop81, (shortOrder13Lift^[13]) m = m := by
  native_decide

theorem source_witness_has_no_shorter_period :
    ∀ n : Fin 13,
      (shortOrder13Lift^[n.val]) selectedWitness ≠ selectedWitness := by
  native_decide

/-- On the original diagonal-punctured T5 carrier; not on
the separately structured 240 E8 root type. -/
theorem transported_short_lift_order_thirteen :
    ∀ z : Old240, (shortOrder13OnOld240^[13]) z = z := by
  native_decide

theorem transported_short_lift_six_fixed :
    (Finset.univ.filter fun z : Old240 =>
      shortOrder13OnOld240 z = z).card = 6 := by
  native_decide

theorem transported_short_lift_234_nonfixed :
    (Finset.univ.filter fun z : Old240 =>
      shortOrder13OnOld240 z ≠ z).card = 234 := by
  native_decide

/-- The exact numeric order-13 obstruction is a theorem target
independent of any claimed categorical E8/Monster physics bridge. -/
theorem explicit_thirteen_forbidden_in_weyl :
    ¬ (13 ∣ Integration.E8StructuredFullWeylRecognition.expectedWE8Order) :=
  e8_weyl_order_excludes_thirteen

end Integration.Griess1990Moufang81Explicit13Cycle
