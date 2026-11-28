import Welds.PNPFrontierResolutionExact

namespace PNPOriginalPartitionCapacity

-- The original selected incidence variables must meet every row,
-- while each column contains at most one selected variable.
-- Row and column maps are original source partitions, not coordinates
-- of a larger ambient relaxation.
theorem partition_capacity {V R C : Type*} [Fintype R] [Fintype C]
    (row : V → R) (col : V → C) (selected : V → Prop)
    (hrow : ∀ r, ∃ v, selected v ∧ row v=r)
    (hcol : ∀ u v, selected u → selected v → col u=col v → u=v) :
    Fintype.card R≤Fintype.card C := by
  classical
  choose v hv hvr using hrow
  have hinj : Function.Injective (fun r => col (v r)) := by
    intro r s h
    have e := hcol (v r) (v s) (hv r) (hv s) h
    exact (hvr r).symm.trans ((congrArg row e).trans (hvr s))
  exact Fintype.card_le_of_injective _ hinj

theorem partition_refutation {V R C : Type*} [Fintype R] [Fintype C]
    (row : V → R) (col : V → C) (selected : V → Prop)
    (hrow : ∀ r, ∃ v, selected v ∧ row v=r)
    (hcol : ∀ u v, selected u → selected v → col u=col v → u=v)
    (excess : Fintype.card C<Fintype.card R) : False :=
  (Nat.not_lt_of_ge (partition_capacity row col selected hrow hcol)) excess

-- This consumer bypasses resolution on an original recognized
-- pigeonhole incidence carrier. It does not prove that an arbitrary
-- original UNSAT source admits such a partition.

end PNPOriginalPartitionCapacity
