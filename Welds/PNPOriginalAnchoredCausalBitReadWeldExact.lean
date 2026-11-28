import Welds.PNPOriginalAnchoredFinClockObservationReceiptExact

/-!
Section41 original anchored F3 Boolean pair: weld finite-clock
information necessity to a CONCRETE ORIGINAL INPUT COORDINATE.

This is a restricted but honest original-machine interface:
at physical clock j the real observation is an explicitly
addressed Bool read probe(j, u(address(j))) on the same source u.
The original paired observation split in Fin k then forces an
actual divergent input bit at the chosen original address.

The input-address/read factorization remains an EXPLICIT machine
hypothesis; unrestricted algorithm computations may use different
observations, read blocks, compress inputs or share computations.
This is one unavoidable read under this stated ABI, not a
superpolynomial P-vs-NP theorem. Native Lean verification pending.
-/
namespace PNPOriginalResidualClosedEventNoGo
open PNPResidualGeometryBridge PNPLinearConsumerCut
open PNPF3SyndromeBoundary

/-- From the original same-run finite-clock observation witness,
extract a literal original Bool coordinate whose value must differ.
No extra oracle source is introduced: it is the real address used
by the concrete probe at the SAME physical step. -/
theorem anchored_original_visible_requires_divergent_bit_read
    {n w m : Nat} {S I : Type*}
    (A : Syndrome n →ₗ[ZMod 3] Syndrome w)
    (B : Syndrome n →ₗ[ZMod 3] Syndrome m)
    (state : (Fin n → Bool) → Nat → S)
    (observe : Nat → (Fin n → Bool) → I)
    (step : Nat → S → I → S)
    (accept : S → Bool)
    (terminal : Syndrome m → Bool)
    (address : Nat → Fin n)
    (probe : Nat → Bool → I)
    (hread : ∀ (j : Nat) (u : Fin n → Bool),
      observe j u = probe j (u (address j)))
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
      x (address j.val) ≠ (reopen x d) (address j.val) := by
  obtain ⟨j, hobs⟩ :=
    anchored_original_visible_has_finite_clock_observation_witness
      A B state observe step accept terminal x d k
      hlegal hkernel hinit hstep hterminal hvisible
  refine ⟨j, ?_⟩
  intro hbit
  apply hobs
  rw [hread j.val x, hread j.val (reopen x d), hbit]

/-- The result is explicitly an actual addressed read receipt in
the ORIGINAL k-step trace, and cannot select an unbounded future
input coordinate. -/
theorem anchored_original_divergent_bit_read_has_legal_clock
    {n w m : Nat} {S I : Type*}
    (A : Syndrome n →ₗ[ZMod 3] Syndrome w)
    (B : Syndrome n →ₗ[ZMod 3] Syndrome m)
    (state : (Fin n → Bool) → Nat → S)
    (observe : Nat → (Fin n → Bool) → I)
    (step : Nat → S → I → S)
    (accept : S → Bool)
    (terminal : Syndrome m → Bool)
    (address : Nat → Fin n)
    (probe : Nat → Bool → I)
    (hread : ∀ (j : Nat) (u : Fin n → Bool),
      observe j u = probe j (u (address j)))
    (x : Fin n → Bool) (d : Syndrome n) (k : Nat)
    (hlegal : LegalAt x d) (hkernel : A d = 0)
    (hinit : ∀ u v : Fin n → Bool,
      A (boolEmbed u) = A (boolEmbed v) →
        state u 0 = state v 0)
    (hstep : ∀ u j,
      state u (j+1) = step j (state u j) (observe j u))
    (hterminal : ∀ u,
      accept (state u k) = terminal (B (boolEmbed u)))
    (hvisible : terminal (B (boolEmbed x)) ≠
      terminal (B (boolEmbed (reopen x d)))) :
    ∃ j : Nat, j < k ∧
      x (address j) ≠ (reopen x d) (address j) := by
  obtain ⟨j, hbit⟩ :=
    anchored_original_visible_requires_divergent_bit_read
      A B state observe step accept terminal address probe hread
      x d k hlegal hkernel hinit hstep hterminal hvisible
  exact ⟨j.val, j.isLt, hbit⟩

end PNPOriginalResidualClosedEventNoGo
