import Mathlib

/-!
# Actual Monster 2B weight-two source dimension audit

External arithmetic source: decomposition of the real Griess module under
C_M(2B) = 2^(1+24).Co_1, with invariant constituents of dimensions
1, 299, 98280, 98304; the central involution acts + on the first
three and - on the last. See the actual 2B centralizer presentation,
not the unrelated binary-tetrahedral supersingular inertia carrier.

This module derives the numerical (+/-)-eigenspace and trace budget from
that source decomposition. It deliberately does not infer an integral
Z_2[C_2] lattice splitting from a characteristic-zero decomposition.

The genuine integral Tate cohomology depends on the choice of Monster-
stable integral form and its mod-2 gluing. A rank/trace identity cannot
supply composition lengths 3,3,2,1,1.
-/

namespace Integration.OggSSP2BActualWeightTwoSourceBudget

def fixedVacuumDim : ℕ := 1
def plus299Dim : ℕ := 299
def plus98280Dim : ℕ := 98280
def minus98304Dim : ℕ := 98304

theorem source_griess_rank :
    fixedVacuumDim + plus299Dim + plus98280Dim + minus98304Dim =
    196884 := by decide

theorem source_constituent_rank :
    plus299Dim + plus98280Dim + minus98304Dim = 196883 := by decide

theorem source_twoB_plus_rank :
    fixedVacuumDim + plus299Dim + plus98280Dim = 98580 := by decide

theorem source_twoB_minus_rank :
    minus98304Dim = 98304 := by decide

theorem source_twoB_trace_weight_two :
    (fixedVacuumDim : ℤ) + plus299Dim + plus98280Dim - minus98304Dim =
    276 := by decide

theorem five_defects_total_ten :
    (3:ℕ) + 3 + 2 + 1 + 1 = 10 := by decide

/-- A proposed five-piece direct sum with these lengths cannot by
itself exhaust the full fixed eigenspace at weight 2. This numerical
obstruction is about the rational eigenspace, NOT the integral Tate
module, which may have quite different composition length. -/
theorem defect_vector_not_plus_rational_rank :
    (3:ℕ) + 3 + 2 + 1 + 1 ≠
      fixedVacuumDim + plus299Dim + plus98280Dim := by decide

/-- The actual 2B centralizer has a four-summand characteristic-zero
decomposition, with THREE constituent summands after removing vacuum.
Any separate five-way decomposition must be derived from extra source
structure, not identified with these dimensions by renaming. -/
theorem defect_vector_not_minus_rational_rank :
    (3:ℕ) + 3 + 2 + 1 + 1 ≠ minus98304Dim := by decide

end Integration.OggSSP2BActualWeightTwoSourceBudget
