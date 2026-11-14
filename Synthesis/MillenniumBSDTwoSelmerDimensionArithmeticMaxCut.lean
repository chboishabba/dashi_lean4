import Mathlib.Tactic

/-!
# BSD two-Selmer numerical rank cut — no cohomological promotion

For an elliptic curve over Q, the **classical** Kummer exact sequence is

  0 → E(Q)/2E(Q) → Sel₂(E/Q) → Sha(E/Q)[2] → 0.

The cohomology on the middle term uses the Galois module E[2], while the
right-hand term is 2-torsion **inside Sha¹(Q,E)** (Weil–Châtelet
cohomology), not the everywhere-local-trivial subgroup of H¹(Q,E[2]).

The arithmetic statements below isolate only the finite-dimension
consequences.  The geometrically meaningful input is intentionally an
explicit equality; none of these declarations manufactures a Selmer
calculation or the missing long-exact-sequence comparison.

In particular, Sha(E)[2]=0 does NOT establish Sha(E)=0.
-/

namespace Synthesis.Millennium.BSD

/-- Numerical inputs from an *already established* same-curve two-Selmer
short exact sequence and weak Mordell–Weil.  Supplying this structure is a
genuine upstream arithmetic proof obligation, not a definition of Selmer. -/
structure TwoSelmerDimensionReceipt where
  algebraicRank : ℕ
  rationalTwoTorsionDimension : ℕ
  selmerDimension : ℕ
  shaTwoDimension : ℕ
  dimensionFromExactSequence :
    selmerDimension =
      algebraicRank + rationalTwoTorsionDimension + shaTwoDimension

/-- Dimension formula: the receipt explicitly exposes the Sha[2] defect. -/
theorem twoSelmer_rank_plus_torsion_plus_shaTwo
    (r : TwoSelmerDimensionReceipt) :
    r.selmerDimension =
      r.algebraicRank + r.rationalTwoTorsionDimension +
        r.shaTwoDimension :=
  r.dimensionFromExactSequence

/-- The exact 2-Selmer dimension always bounds the algebraic rank after
accounting for rational two-torsion. -/
theorem twoSelmer_rank_bound
    (r : TwoSelmerDimensionReceipt) :
    r.algebraicRank + r.rationalTwoTorsionDimension ≤
      r.selmerDimension := by
  omega

/-- Equality of Selmer and rational 2-torsion dimensions forces both rank
and the **two-torsion part only** of Sha to vanish. -/
theorem twoSelmer_minimal_forces_rank_zero_and_shaTwo_zero
    (r : TwoSelmerDimensionReceipt)
    (hmin : r.selmerDimension = r.rationalTwoTorsionDimension) :
    r.algebraicRank = 0 ∧ r.shaTwoDimension = 0 := by
  omega

/-- Conversely, rank zero and zero Sha[2] force minimal Selmer dimension. -/
theorem twoSelmer_minimal_of_rank_zero_and_shaTwo_zero
    (r : TwoSelmerDimensionReceipt)
    (hr : r.algebraicRank = 0)
    (hsha : r.shaTwoDimension = 0) :
    r.selmerDimension = r.rationalTwoTorsionDimension := by
  omega

/-- An all-rational two-torsion CM test-curve receipt remains conditional on
an *independent* actual Selmer computation, not the choice of a number 2. -/
theorem cmTwoSelmer_dimension_two_conditional
    (r : TwoSelmerDimensionReceipt)
    (htors : r.rationalTwoTorsionDimension = 2)
    (hsel : r.selmerDimension = 2) :
    r.algebraicRank = 0 ∧ r.shaTwoDimension = 0 := by
  exact twoSelmer_minimal_forces_rank_zero_and_shaTwo_zero r (hsel.trans htors.symm)

/-- A one-sided Selmer upper-bound alone cannot imply exact rank: two
different algebraic ranks fit the same Selmer dimension and torsion data. -/
theorem twoSelmer_same_upper_bound_allows_different_ranks :
    (0 + 2 ≤ 3) ∧ (1 + 2 ≤ 3) ∧ (0 ≠ 1) := by
  omega

end Synthesis.Millennium.BSD
