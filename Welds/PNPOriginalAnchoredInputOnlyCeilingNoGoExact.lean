import Welds.PNPOriginalAnchoredPackedFuelClosureExact

/-!
Section 26 input-coordinate no-go on the SAME anchored original F3
residual family, with no unseen supports, machine states or alternative
original candidate. It identifies the exact ceiling of the current
input-only witness and so prevents mistaking it for a superlinear
arbitrary SAT lower bound. The new resource must be internal/shared
events or an entirely different original-semantic potential.
-/
namespace PNPOriginalResidualFutureReadWeld
open PNPResidualGeometryBridge PNPLinearConsumerCut
open PNPF3SyndromeBoundary PNPSameRunReadFootprint
open scoped BigOperators

/-- Original anchored signed residual witnesses, when each changes
at least one original input coordinate, have TOTAL weight at most
n*C under the same per-address sharing capacity used by the
physical read theorem. Repeated rivals do not create new capacity.

This is a true obstruction to using this input-only packing
certificate as a superlinear (let alone exponential) lower bound. -/
theorem original_anchored_input_only_capacity_ceiling
    {n : Nat} {J : Type*} [DecidableEq J]
    (x : Fin n → Bool)
    (obligations : Finset J) (direction : J → Syndrome n)
    (weight : J → Nat) (C : Nat)
    (hchange : ∀ j ∈ obligations,
      ∃ i : Fin n, x i ≠ reopen x (direction j) i)
    (hcapacity : ∀ i : Fin n,
      (∑ j ∈ obligations,
        if x i ≠ reopen x (direction j) i then weight j else 0) ≤ C) :
    (∑ j ∈ obligations, weight j) ≤ n * C := by
  classical
  have hpaid (j : J) (hj : j ∈ obligations) :
      weight j ≤
        ∑ i : Fin n,
          if x i ≠ reopen x (direction j) i then weight j else 0 := by
    obtain ⟨i, hi⟩ := hchange j hj
    have hsingle :
        (if x i ≠ reopen x (direction j) i then weight j else 0) ≤
          ∑ q : Fin n,
            if x q ≠ reopen x (direction j) q then weight j else 0 :=
      Finset.single_le_sum
        (fun q _ => Nat.zero_le _) (Finset.mem_univ i)
    simpa only [if_pos hi] using hsingle
  calc
    (∑ j ∈ obligations, weight j) ≤
        ∑ j ∈ obligations, ∑ i : Fin n,
          if x i ≠ reopen x (direction j) i then weight j else 0 :=
      Finset.sum_le_sum hpaid
    _ = ∑ i : Fin n, ∑ j ∈ obligations,
          if x i ≠ reopen x (direction j) i then weight j else 0 :=
      Finset.sum_comm
    _ ≤ ∑ _i : Fin n, C :=
      Finset.sum_le_sum (fun i _ => hcapacity i)
    _ = n * C := by simp

end PNPOriginalResidualFutureReadWeld
