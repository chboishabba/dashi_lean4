import Welds.PNPOriginalResidualClosedInternalNoGoExact

/-!
Section37 reverse solve from original anchored F3 residual visibility.

The original closed-internal-observer no-split theorem already proves
that two legal Boolean sources with the SAME retained F3 syndrome
cannot diverge under closed deterministic internal observation.

This file extracts the CONSTRUCTIVE SPECIFICATION of the remaining
physical resource: for any faithful implementation that actually
distinguishes the original consumer, a particular step and source
MUST have an observation not obtained from the retained state.
This is a witness to an external-information dependency, NOT yet a
lower bound on the number of actual machine reads, and never a
superpolynomial lower bound for arbitrary SAT solvers.
-/
namespace PNPOriginalResidualClosedEventNoGo
open PNPResidualGeometryBridge PNPLinearConsumerCut
open PNPF3SyndromeBoundary

/-- Reverse-solve the original contradiction into an EXISTENTIAL
real observation not explainable by a closed retained-state
readout. Every argument is the SAME original signed F3 input,
retained syndrome, and actual Boolean terminal consumer. -/
theorem anchored_original_visible_has_external_observation_witness
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
    (hstep : ∀ u j,
      state u (j+1) = step j (state u j) (observe j u))
    (hterminal : ∀ u,
      accept (state u k) = terminal (B (boolEmbed u)))
    (hvisible : terminal (B (boolEmbed x)) ≠
      terminal (B (boolEmbed (reopen x d)))) :
    ∃ (j : Nat) (u : Fin n → Bool),
      observe j u ≠ readout j (state u j) := by
  classical
  by_contra hnone
  have hclosed : ∀ j u,
      observe j u = readout j (state u j) := by
    intro j u
    by_contra hneq
    exact hnone ⟨j,u,hneq⟩
  exact anchored_original_visible_requires_external_information
    A B state observe step readout accept terminal x d k
    hlegal hkernel hinit hclosed hstep hterminal hvisible

end PNPOriginalResidualClosedEventNoGo
