import Welds.PNPOriginalAnchoredInputOnlyCeilingNoGoExact
import Welds.PNPOriginalAnchoredPackedFuelClosureExact

/-!
Section 27 strongest exact input-only charge on the SAME original
anchored F3 source: number of source coordinates and physical query
fuel are TWO independent ceilings on the same weighted obligation.

This forbids bootstrapping the input-only residual hyperfabric into
a superlinear unrestricted SAT work proof by retagging the same
obligations as new events. True internal events require a new owner.
-/
namespace PNPOriginalResidualFutureReadWeld
open PNPResidualGeometryBridge PNPLinearConsumerCut
open PNPF3SyndromeBoundary PNPSameRunReadFootprint
open scoped BigOperators

theorem original_anchored_input_read_double_ceiling
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
    (hchange : ∀ j ∈ obligations,
      ∃ i : Fin n, x i ≠ reopen x (direction j) i)
    (hcapacity : ∀ i : Fin n,
      (∑ j ∈ obligations,
        if x i ≠ reopen x (direction j) i then weight j else 0) ≤ C) :
    (∑ j ∈ obligations, weight j) ≤ C * min n k := by
  have hn := original_anchored_input_only_capacity_ceiling
    x obligations direction weight C hchange hcapacity
  have hk := original_anchored_packed_residual_fuel_payment
    A B ask accept prefix observe x k C obligations direction weight
    hprefix haccept hlegal hkernel hvisible hcapacity
  rcases le_total n k with hnk | hkn
  · rw [min_eq_left hnk]
    simpa [Nat.mul_comm] using hn
  · rw [min_eq_right hkn]
    exact hk

end PNPOriginalResidualFutureReadWeld
