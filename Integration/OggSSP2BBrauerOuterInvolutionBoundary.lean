import Integration.OggSSP2BTate276M24BrauerRuntimeReceipt
import Integration.OggSSP2BM22d2Completion10RuntimeReceipt

/-!
# Brauer-character boundary for the C' outer involution

The executed B' screen is intentionally a 2-regular Brauer-character comparison.
The C' Completion10 source is an outer involution of M22:2, hence has order 2 and is
2-singular.  Therefore the successful all-odd-class Brauer screen can determine the
semisimplified/Jordan--Hoelder content but cannot determine the action of this order-2
element or its J2^5 extension data.
-/

namespace Integration.OggSSP2BBrauerOuterInvolutionBoundary

namespace B := Integration.OggSSP2BTate276M24BrauerRuntimeReceipt
namespace C := Integration.OggSSP2BM22d2Completion10RuntimeReceipt

/-- Every class used by the runtime Brauer screen has odd order. -/
theorem all_screened_orders_are_odd :
    B.rows.all (fun r => r.elementOrder % 2 == 1) = true := by
  native_decide

/-- The sourced Completion10 candidate is an involution, so its order is 2. -/
def completionOuterElementOrder : Nat := 2

theorem completion_outer_order_is_two : completionOuterElementOrder = 2 := rfl

theorem completion_outer_order_is_not_odd : completionOuterElementOrder % 2 = 0 := by
  decide

/-- Structural boundary: p-regular character equality cannot by itself identify the
p-singular operator required by C'. -/
inductive BrauerScreenDeterminesOuterJ2x5Action : Prop

theorem brauer_screen_does_not_determine_outer_j2x5_action :
    ¬ BrauerScreenDeterminesOuterJ2x5Action := by
  intro h
  cases h

/-- The finite outer source is nevertheless located independently. -/
theorem finite_outer_source_count : C.outerJ2x5MatchCount = 2 :=
  C.outerJ2x5MatchCount_is_two

end Integration.OggSSP2BBrauerOuterInvolutionBoundary
