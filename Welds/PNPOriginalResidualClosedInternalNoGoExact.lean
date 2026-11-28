import Welds.PNPOriginalResidualFutureReadWeldExact
import Welds.PNPActualEventDemandExact

/-!
Original anchored F3 residual cannot be distinguished by a CLOSED
internal observer if it collided in the actual initial retained state.
This weld transfers the original legal Boolean reopen and source
retained-kernel equality to the true deterministic internal observer
model. It prevents charging internal state inspection as fresh
original input information.

No arbitrary SAT lower bound follows: non-closed implementations
must explicitly expose external reads, and such reads are separately
charged by PNPOriginalResidualFutureReadWeldExact.
-/
namespace PNPOriginalResidualClosedEventNoGo
open PNPResidualGeometryBridge PNPLinearConsumerCut
open PNPF3SyndromeBoundary
open PNPActualEventDemand

/-- An actual anchored signed F3 direction cannot yield a different
Boolean terminal observation solely through deterministic closed
internal state transport. The original linear retained state and the
original Boolean source are fixed throughout the argument. -/
theorem anchored_original_closed_internal_observer_no_split
    {n w m : Nat} {S I : Type*}
    (A : Syndrome n →ₗ[ZMod 3] Syndrome w)
    (B : Syndrome n →ₗ[ZMod 3] Syndrome m)
    (state : (Fin n → Bool) → Nat → S)
    (observe : Nat → (Fin n → Bool) → I)
    (step : Nat → S → I → S)
    (readout : Nat → S → I)
    (accept : S → Bool)
    (terminal : Syndrome m → Bool)
    (x : Fin n → Bool) (d : Syndrome n) (k : Nat)
    (hlegal : LegalAt x d)
    (hkernel : A d = 0)
    (hinit : ∀ u v : Fin n → Bool,
      A (boolEmbed u) = A (boolEmbed v) →
        state u 0 = state v 0)
    (hobs : ∀ j u, observe j u = readout j (state u j))
    (hstep : ∀ u j,
      state u (j+1) = step j (state u j) (observe j u))
    (hterminal : ∀ u,
      accept (state u k) = terminal (B (boolEmbed u))) :
    terminal (B (boolEmbed x)) =
      terminal (B (boolEmbed (reopen x d))) := by
  let y := reopen x d
  have he : boolEmbed x - boolEmbed y = d :=
    anchored_reopen x d hlegal
  have hA : A (boolEmbed x) = A (boolEmbed y) := by
    apply sub_eq_zero.mp
    rw [← map_sub, he, hkernel]
  have hzero : state x 0 = state y 0 := hinit x y hA
  have hfuture : state x (0+k) = state y (0+k) :=
    internal_observer_no_split state observe step readout
      hobs hstep x y 0 k hzero
  have haccept := congrArg accept hfuture
  simpa only [Nat.zero_add] using
    (hterminal x).symm.trans (haccept.trans (hterminal y))

/-- Reverse-solve obstruction: if an actual original legal residual
really DOES change the Boolean consumer, then no purported source
closed-internal-observer realization with those exact signatures
can exist. Such a model must pay a legitimate external input event
or abandon one of its claimed state/fidelity hypotheses. -/
theorem anchored_original_visible_requires_external_information
    {n w m : Nat} {S I : Type*}
    (A : Syndrome n →ₗ[ZMod 3] Syndrome w)
    (B : Syndrome n →ₗ[ZMod 3] Syndrome m)
    (state : (Fin n → Bool) → Nat → S)
    (observe : Nat → (Fin n → Bool) → I)
    (step : Nat → S → I → S)
    (readout : Nat → S → I)
    (accept : S → Bool) (terminal : Syndrome m → Bool)
    (x : Fin n → Bool) (d : Syndrome n) (k : Nat)
    (hlegal : LegalAt x d) (hkernel : A d = 0)
    (hinit : ∀ u v : Fin n → Bool,
      A (boolEmbed u) = A (boolEmbed v) →
        state u 0 = state v 0)
    (hobs : ∀ j u, observe j u = readout j (state u j))
    (hstep : ∀ u j,
      state u (j+1) = step j (state u j) (observe j u))
    (hterminal : ∀ u,
      accept (state u k) = terminal (B (boolEmbed u)))
    (hvisible : terminal (B (boolEmbed x)) ≠
      terminal (B (boolEmbed (reopen x d)))) :
    False :=
  hvisible (anchored_original_closed_internal_observer_no_split
    A B state observe step readout accept terminal x d k
    hlegal hkernel hinit hobs hstep hterminal)

end PNPOriginalResidualClosedEventNoGo
