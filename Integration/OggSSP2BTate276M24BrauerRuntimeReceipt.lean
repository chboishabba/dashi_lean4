import Integration.OggSSP2BM22RuntimeReceipt

/-!
# 2B Tate-276 / M24 duad Brauer-character runtime receipt

This file records the executed CTblLib max-cut computation on the actual weight-two
2B Tate Brauer trace.  On every 2-regular M24 class, the Tate trace candidate agrees
with the genuine degree-276 duad permutation character; the lift through the
2B-centralizer fusion chain is independent of the compatible lift.

The receipt is deliberately weaker than a literal module isomorphism.  Equality of
Brauer characters pays the semisimplified/Jordan--Hoelder content only after applying
the standard Brauer-character uniqueness theorem.  It does not construct a canonical
submodule chain N <= S <= Tate276, and it does not identify a particular 10a/10b
quotient with the M22:2 outer action.
-/

namespace Integration.OggSSP2BTate276M24BrauerRuntimeReceipt

namespace M22 := Integration.OggSSP2BM22RuntimeReceipt

structure TwoRegularRow where
  m24Class : Nat
  elementOrder : Nat
  co1Class : Nat
  tateTrace : Int
  duadTrace : Int
  compatibleLiftCount : Nat
  deriving DecidableEq, Repr

abbrev rows : List TwoRegularRow :=
  [ ⟨1, 1, 1, 276, 276, 1⟩
  , ⟨4, 3, 6, 15, 15, 1⟩
  , ⟨5, 3, 8, 0, 0, 1⟩
  , ⟨9, 5, 16, 6, 6, 1⟩
  , ⟨12, 7, 28, 3, 3, 1⟩
  , ⟨13, 7, 28, 3, 3, 1⟩
  , ⟨16, 11, 44, 1, 1, 1⟩
  , ⟨21, 15, 64, 0, 0, 1⟩
  , ⟨22, 15, 64, 0, 0, 1⟩
  , ⟨23, 21, 76, 0, 0, 1⟩
  , ⟨24, 21, 76, 0, 0, 1⟩
  , ⟨25, 23, 78, 0, 0, 1⟩
  , ⟨26, 23, 79, 0, 0, 1⟩ ]

def rowMatches (r : TwoRegularRow) : Bool := r.tateTrace == r.duadTrace

theorem row_count_is_thirteen : rows.length = 13 := by native_decide

theorem every_two_regular_row_matches : rows.all rowMatches = true := by native_decide

theorem every_compatible_lift_is_unique_in_runtime_rows :
    rows.all (fun r => r.compatibleLiftCount == 1) = true := by native_decide

/-- Exact runtime/fusion provenance surface. -/
structure RuntimeReceipt where
  twoRegularClassCount : Nat
  allLiftTracesIndependent : Bool
  allBrauerRowsMatch : Bool
  actualTwoBTateWeightTwoTraceUsed : Bool
  m24DuadCharacterUsed : Bool
  explicitTateDuadModuleIsomorphismConstructed : Bool
  explicitActualTateTenSubquotientConstructed : Bool
  source : String

/-- The executed CTblLib result supplied by the repository runtime. -/
def canonicalRuntimeReceipt : RuntimeReceipt where
  twoRegularClassCount := 13
  allLiftTracesIndependent := true
  allBrauerRowsMatch := true
  actualTwoBTateWeightTwoTraceUsed := true
  m24DuadCharacterUsed := true
  explicitTateDuadModuleIsomorphismConstructed := false
  explicitActualTateTenSubquotientConstructed := false
  source := "DASHI CTblLib runtime: 2B Tate-276 / M24 duad 2-regular Brauer-character screen"

theorem runtime_class_count : canonicalRuntimeReceipt.twoRegularClassCount = 13 := rfl

theorem runtime_all_rows_match : canonicalRuntimeReceipt.allBrauerRowsMatch = true := rfl

theorem runtime_lift_independence : canonicalRuntimeReceipt.allLiftTracesIndependent = true := rfl

/-- The independently executed M24-duad -> M22 screen has ten ten-dimensional
composition factors, five of each Atlas kind.  Once Brauer semisimplification is
transported, this is the exact target Jordan--Hoelder content for the actual Tate head. -/
theorem target_ten_factor_multiplicity :
    M22.factorMultiplicity .tenA + M22.factorMultiplicity .tenB = 10 :=
  M22.total_ten_dimensional_factor_multiplicity

/-- Runtime equality is not a canonical module isomorphism. -/
theorem runtime_does_not_construct_literal_tate_duad_isomorphism :
    canonicalRuntimeReceipt.explicitTateDuadModuleIsomorphismConstructed = false := rfl

/-- Nor does the character computation pick a concrete composition-series subquotient. -/
theorem runtime_does_not_construct_explicit_q10 :
    canonicalRuntimeReceipt.explicitActualTateTenSubquotientConstructed = false := rfl

end Integration.OggSSP2BTate276M24BrauerRuntimeReceipt
