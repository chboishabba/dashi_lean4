import Synthesis.MillenniumHodgeP1QRulingsExact
import Synthesis.MillenniumHodgeCycleIsoPushforwardExact
import Mathlib.Tactic

/-!
# Hodge max-cut: genuine factor-swap action and ruling-cycle boundary

The selected geometry is already literal:

* `P1QSelfProductOverQ` is the actual pullback P¹_Q ×_{Spec Q} P¹_Q;
* `p1QRulingOne`, `p1QRulingTwo` are actual Scheme morphisms;
* `p1QFactorSwapOverQ` is the actual pullback symmetry;
* the two ruling morphisms are exchanged exactly.

Mathlib's current `AlgebraicCycle` layer supplies genuine residue-degree
pushforward, but no canonical fundamental-cycle constructor for P¹ and no
ready postcomposition theorem for `AlgebraicCycle.map`. This owner therefore
closes everything after the missing ruling-cycle exchange without replacing
that missing API by a synthetic divisor lattice.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

/-- On the selected P¹×P¹, the genuine factor-swap action is literally
coefficient reindexing along the inverse swap on scheme points. -/
theorem p1QFactorSwap_cycle_apply
    (D : AlgebraicCycle P1QSelfProductOverQ ℤ)
    (y : P1QSelfProductOverQ) :
    actualCyclePushforward p1QFactorSwapOverQ.hom D y =
      D (p1QFactorSwapOverQ.inv y) := by
  exact actualCyclePushforward_iso_apply p1QFactorSwapOverQ D y

/-- The selected factor-swap action on genuine cycles is injective. -/
theorem p1QFactorSwap_cycle_injective :
    Function.Injective
      (actualCyclePushforward p1QFactorSwapOverQ.hom :
        AlgebraicCycle P1QSelfProductOverQ ℤ →
        AlgebraicCycle P1QSelfProductOverQ ℤ) := by
  exact actualCyclePushforward_iso_injective p1QFactorSwapOverQ

/-- Once two genuine cycles are known to be exchanged by the actual factor
swap, their literal difference is a genuine `(-1)` eigencycle. This theorem
uses Mathlib's `AlgebraicCycle` carrier itself; no synthetic cycle action or
parallel lattice is introduced. -/
theorem p1QFactorSwap_difference_antiInvariant
    (D₁ D₂ : AlgebraicCycle P1QSelfProductOverQ ℤ)
    (h₁₂ : actualCyclePushforward p1QFactorSwapOverQ.hom D₁ = D₂)
    (h₂₁ : actualCyclePushforward p1QFactorSwapOverQ.hom D₂ = D₁) :
    actualCyclePushforward p1QFactorSwapOverQ.hom (D₁ - D₂) =
      -(D₁ - D₂) := by
  ext y
  rw [p1QFactorSwap_cycle_apply]
  have h₁ := congrArg
    (fun D : AlgebraicCycle P1QSelfProductOverQ ℤ => D y) h₁₂
  have h₂ := congrArg
    (fun D : AlgebraicCycle P1QSelfProductOverQ ℤ => D y) h₂₁
  rw [p1QFactorSwap_cycle_apply] at h₁ h₂
  change
    D₁ (p1QFactorSwapOverQ.inv y) -
        D₂ (p1QFactorSwapOverQ.inv y) =
      -(D₁ y - D₂ y)
  rw [h₁, h₂]
  abel

/-- The exact remaining cycle-side regression target, stated only in terms of
real Mathlib algebraic cycles and the already-selected factor swap. A future
fundamental-cycle owner should instantiate `D₁,D₂` as the pushforwards of the
actual P¹ fundamental cycle along `p1QRulingOne` and `p1QRulingTwo`. -/
def P1QRulingCycleExchange
    (D₁ D₂ : AlgebraicCycle P1QSelfProductOverQ ℤ) : Prop :=
  actualCyclePushforward p1QFactorSwapOverQ.hom D₁ = D₂ ∧
  actualCyclePushforward p1QFactorSwapOverQ.hom D₂ = D₁

/-- The exact exchange boundary immediately implies the desired cycle-side
regression theorem. -/
theorem p1Q_ruling_difference_antiInvariant_of_exchange
    (D₁ D₂ : AlgebraicCycle P1QSelfProductOverQ ℤ)
    (h : P1QRulingCycleExchange D₁ D₂) :
    actualCyclePushforward p1QFactorSwapOverQ.hom (D₁ - D₂) =
      -(D₁ - D₂) :=
  p1QFactorSwap_difference_antiInvariant D₁ D₂ h.1 h.2

/-!
MAX-CUT STATUS

PAID HERE, subject to exact-head kernel certification:
* actual selected factor-swap action on Mathlib `AlgebraicCycle` is evaluated
  pointwise by inverse reindexing;
* that action is injective;
* for any two genuine cycles exchanged by the swap, their literal difference
  is proved to be a genuine `(-1)` eigencycle.

THE ONLY REMAINING P¹ CYCLE-SIDE SEAM IS NOW PRECISE:

1. obtain a genuine fundamental cycle `[P¹_Q]` in the Mathlib cycle API;
2. form the actual pushforwards along `p1QRulingOne` and `p1QRulingTwo`;
3. prove iso-postcomposition compatibility for the residue-degree weighted
   `AlgebraicCycle.map`, yielding `P1QRulingCycleExchange`.

Current Mathlib exposes neither (1) as a canonical constructor nor (3) as a
ready theorem in this layer. They are intentionally not replaced here by a
synthetic fundamental class or unit-weight cycle map.

After that seam closes, `p1Q_ruling_difference_antiInvariant_of_exchange`
finishes the cycle-side regression immediately. The next genuine library
boundary is then the cycle-class map and its naturality.
-/

end

end Synthesis.Millennium.Hodge
