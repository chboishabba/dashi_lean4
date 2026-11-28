import Welds.PNPOriginalAnchoredPairedPreterminalObservationSplitExact

/-!
Section40: indexed clock receipt for the actual original F3
paired-observation disagreement.

Section39 already produced a natural step j<k. The exact machine
consumer now receives a Fin k index, making an out-of-range witness
unrepresentable in the original finite execution transcript. The
receipt also exposes the actual two-source observation inequality,
not merely a generic external oracle. This is a genuine bounded
dependency; no claim of more than one unavoidable internal read
or superpolynomial SAT complexity is made.
-/
namespace PNPOriginalResidualClosedEventNoGo
open PNPResidualGeometryBridge PNPLinearConsumerCut
open PNPF3SyndromeBoundary

theorem anchored_original_visible_has_finite_clock_observation_witness
    {n w m : Nat} {S I : Type*}
    (A : Syndrome n →ₗ[ZMod 3] Syndrome w)
    (B : Syndrome n →ₗ[ZMod 3] Syndrome m)
    (state : (Fin n → Bool) → Nat → S)
    (observe : Nat → (Fin n → Bool) → I)
    (step : Nat → S → I → S)
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
    ∃ j : Fin k,
      observe j.val x ≠ observe j.val (reopen x d) := by
  obtain ⟨j,hjk,hsplit⟩ :=
    anchored_original_visible_has_paired_observation_split_before_terminal
      A B state observe step accept terminal x d k
      hlegal hkernel hinit hstep hterminal hvisible
  exact ⟨⟨j,hjk⟩,hsplit⟩

/-- The actual bounded witness forbids an apparent faithful source
split at terminal time zero: Fin 0 has no inhabitants. -/
theorem anchored_original_no_zero_clock_visible_witness
    {n w m : Nat} {S I : Type*}
    (A : Syndrome n →ₗ[ZMod 3] Syndrome w)
    (B : Syndrome n →ₗ[ZMod 3] Syndrome m)
    (state : (Fin n → Bool) → Nat → S)
    (observe : Nat → (Fin n → Bool) → I)
    (step : Nat → S → I → S)
    (accept : S → Bool)
    (terminal : Syndrome m → Bool)
    (x : Fin n → Bool) (d : Syndrome n)
    (hlegal : LegalAt x d) (hkernel : A d = 0)
    (hinit : ∀ u v : Fin n → Bool,
      A (boolEmbed u) = A (boolEmbed v) →
        state u 0 = state v 0)
    (hstep : ∀ u j,
      state u (j+1) = step j (state u j) (observe j u))
    (hterminal : ∀ u,
      accept (state u 0) = terminal (B (boolEmbed u))) :
    terminal (B (boolEmbed x)) =
      terminal (B (boolEmbed (reopen x d))) := by
  by_contra hvisible
  obtain ⟨j,_⟩ :=
    anchored_original_visible_has_finite_clock_observation_witness
      A B state observe step accept terminal x d 0
      hlegal hkernel hinit hstep hterminal hvisible
  exact Fin.elim0 j

end PNPOriginalResidualClosedEventNoGo
