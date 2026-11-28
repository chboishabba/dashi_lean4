import Welds.PNPResidualGeometryBridgeExact
import Welds.PNPFutureResidualChargeExact

/-!
Original F3 signed residual -> ACTUAL same-run input-read event.

Consumes the real anchored Boolean lift/reopen proof, the original
linear retained-state and consumer maps, and the deterministic adaptive
query machine. No counterfactual reads are billed as actual time.
No claim that all SAT candidates admit high-demand collisions.
-/
namespace PNPOriginalResidualFutureReadWeld
open PNPResidualGeometryBridge
open PNPLinearConsumerCut
open PNPF3SyndromeBoundary
open PNPSameRunReadFootprint

/-- A retained ternary kernel direction with legal signed support,
when a real single-bit terminal consumer distinguishes the original
source from its reopened source, forces a PHYSICAL read from their
different coordinates on the original execution.

The actual prefix state must be identified with the original linear
retained state, and the terminal observer with the original consumer.
Neither identification is inferred from purely algebraic rank. -/
theorem anchored_original_residual_forces_actual_future_read
    {n w m : Nat} {S : Type*}
    (A : Syndrome n →ₗ[ZMod 3] Syndrome w)
    (B : Syndrome n →ₗ[ZMod 3] Syndrome m)
    (ask : S → Option (Fin n × (Bool → S)))
    (accept : S → Bool)
    (prefix : (Fin n → Bool) → S)
    (observe : Syndrome m → Bool)
    (k : Nat)
    (hprefix : ∀ u v : Fin n → Bool,
      A (boolEmbed u) = A (boolEmbed v) → prefix u = prefix v)
    (haccept : ∀ u : Fin n → Bool,
      accept (run ask u k (prefix u)).1 = observe (B (boolEmbed u)))
    (x : Fin n → Bool) (d : Syndrome n)
    (hlegal : LegalAt x d) (hkernel : A d = 0)
    (hvisible :
      observe (B (boolEmbed x)) ≠
        observe (B (boolEmbed (reopen x d)))) :
    ∃ i ∈ (run ask x k (prefix x)).2, x i ≠ (reopen x d) i := by
  let y := reopen x d
  have hdifference : boolEmbed x - boolEmbed y = d :=
    anchored_reopen x d hlegal
  have hsame : A (boolEmbed x) = A (boolEmbed y) := by
    apply sub_eq_zero.mp
    rw [← map_sub, hdifference, hkernel]
  have hstate : prefix x = prefix y := hprefix x y hsame
  have hout :
      accept (run ask x k (prefix x)).1 ≠
        accept (run ask y k (prefix y)).1 := by
    rw [haccept x, haccept y]
    exact hvisible
  exact PNPFutureResidualCharge.collision_requires_read
    ask accept prefix x y k hstate hout

/-- The exact reverse-source identities remain visible to callers:
zero retained displacement and nonzero consumer displacement are
the algebraic obligations, while terminal observability remains an
additional original behavioural fact. -/
theorem anchored_original_consumer_displacement
    {n w m : Nat}
    (A : Syndrome n →ₗ[ZMod 3] Syndrome w)
    (B : Syndrome n →ₗ[ZMod 3] Syndrome m)
    (x : Fin n → Bool) (d : Syndrome n)
    (hlegal : LegalAt x d) (hA : A d = 0)
    (hB : B d ≠ 0) :
    A (boolEmbed x) = A (boolEmbed (reopen x d)) ∧
    B (boolEmbed x) ≠ B (boolEmbed (reopen x d)) := by
  have he := anchored_reopen x d hlegal
  constructor
  · apply sub_eq_zero.mp
    rw [← map_sub, he, hA]
  · intro h
    apply hB
    rw [← he, map_sub, h, sub_self]

end PNPOriginalResidualFutureReadWeld
