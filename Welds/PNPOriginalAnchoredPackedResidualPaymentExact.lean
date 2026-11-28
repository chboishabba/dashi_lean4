import Welds.PNPOriginalResidualFutureReadWeldExact

/-!
Same-run packed ORIGINAL signed residual cost. Retained F3 state, legal
Boolean reopen and observed original terminal event must all agree.
A many-rival family is charged only through actual source-coordinate
capacity, not counterfactual branches, ranks or trace enumeration.
-/
namespace PNPOriginalResidualFutureReadWeld
open PNPResidualGeometryBridge PNPLinearConsumerCut
open PNPF3SyndromeBoundary PNPSameRunReadFootprint

/-- Source-native signed residual family to physical same-run read
capacity. Here the alternatives are ALL legal anchored F3 directions
of the same original input, and the output observer is the actual
terminal Boolean predicate, not an arbitrary linear consumer value.

This theorem never assumes different consumer syndromes imply
different Boolean decision outputs; hvisible states the actual
required observation. The capacity bound is paid per input address,
not per counterfactual execution. -/
theorem original_anchored_packed_residual_read_payment
    {n w m : Nat} {S J : Type*} [DecidableEq J]
    (A : Syndrome n →ₗ[ZMod 3] Syndrome w)
    (B : Syndrome n →ₗ[ZMod 3] Syndrome m)
    (ask : S → Option (Fin n × (Bool → S)))
    (accept : S → Bool)
    (prefix : (Fin n → Bool) → S)
    (observe : Syndrome m → Bool)
    (x : Fin n → Bool) (k C : Nat)
    (obligations : Finset J) (direction : J → Syndrome n) (weight : J → Nat)
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
    (∑ j ∈ obligations, weight j) ≤
       C * (run ask x k (prefix x)).2.length := by
  classical
  let alt : J → Fin n → Bool := fun j => reopen x (direction j)
  have collision : ∀ j ∈ obligations, prefix x = prefix (alt j) := by
    intro j hj
    have he := anchored_reopen x (direction j) (hlegal j hj)
    apply hprefix
    apply sub_eq_zero.mp
    rw [← map_sub, he, hkernel j hj]
  have different : ∀ j ∈ obligations,
      accept (run ask x k (prefix x)).1 ≠
        accept (run ask (alt j) k (prefix (alt j))).1 := by
    intro j hj
    rw [haccept x, haccept (alt j)]
    exact hvisible j hj
  exact PNPFutureResidualCharge.packed_future_reads
    ask accept prefix x k C obligations alt weight
    collision different hcapacity

end PNPOriginalResidualFutureReadWeld
