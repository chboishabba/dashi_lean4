import Welds.PNPOriginalAnchoredPackedResidualPaymentExact

/-!
Physical query-fuel closure for the SAME original anchored legal F3
residual family. The previous payment is in actual read count; this
consumer attaches the original run's reads_le_fuel, so the right
side is the real machine's query horizon, not a virtual tableau size.

This is a conditional cost theorem. It does not manufacture a SAT
candidate family satisfying superpolynomial demand, and total time is
at least queries only in computational models charging these reads.
-/
namespace PNPOriginalResidualFutureReadWeld
open PNPResidualGeometryBridge PNPLinearConsumerCut
open PNPF3SyndromeBoundary PNPSameRunReadFootprint

theorem original_anchored_packed_residual_fuel_payment
    {n w m : Nat} {S J : Type*} [DecidableEq J]
    (A : Syndrome n →ₗ[ZMod 3] Syndrome w)
    (B : Syndrome n →ₗ[ZMod 3] Syndrome m)
    (ask : S → Option (Fin n × (Bool → S)))
    (accept : S → Bool)
    (prefix : (Fin n → Bool) → S)
    (observe : Syndrome m → Bool)
    (x : Fin n → Bool) (k C : Nat)
    (obligations : Finset J) (direction : J → Syndrome n)
    (weight : J → Nat)
    (hprefix : ∀ u v : Fin n → Bool,
      A (boolEmbed u) = A (boolEmbed v) → prefix u = prefix v)
    (haccept : ∀ u : Fin n → Bool,
      accept (run ask u k (prefix u)).1 = observe (B (boolEmbed u)))
    (hlegal : ∀ j ∈ obligations, LegalAt x (direction j))
    (hkernel : ∀ j ∈ obligations, A (direction j) = 0)
    (hvisible : ∀ j ∈ obligations,
      observe (B (boolEmbed x)) ≠
        observe (B (boolEmbed (reopen x (direction j)))))
    (hcapacity : ∀ i : Fin n,
      (∑ j ∈ obligations,
        if x i ≠ reopen x (direction j) i then weight j else 0) ≤ C) :
    (∑ j ∈ obligations, weight j) ≤ C * k := by
  have hreads := original_anchored_packed_residual_read_payment
    A B ask accept prefix observe x k C obligations direction weight
    hprefix haccept hlegal hkernel hvisible hcapacity
  have hclock := PNPSameRunReadFootprint.reads_le_fuel
    ask x k (prefix x)
  exact hreads.trans (Nat.mul_le_mul_left C hclock)

end PNPOriginalResidualFutureReadWeld
