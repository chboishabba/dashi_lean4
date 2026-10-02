import Integration.OggSSP2BNormalizerFiveByTwoRecognition

/-!
# Full Co1 action cannot realize a nontrivial Completion10 module

Source facts:
* for a 2B Monster element, the centralizer has shape 2^(1+24).Co1;
* Co1 is simple;
* the smallest faithful characteristic-two representation of Co1 has
  dimension 24.

Because Co1 is simple, every nontrivial linear representation is faithful.
Therefore every nontrivial F2 Co1-module has dimension at least 24.
In particular a 10-dimensional Completion10 carrier cannot support a
nontrivial full-Co1 action.

This does NOT rule out:
* a 10-dimensional module for a proper local subgroup of Co1;
* a 10-dimensional subquotient after restricting the 276-dimensional Tate
  action to such a subgroup;
* a nontrivial action of the 2-local normal subgroup before quotienting.

It rules out only the strongest proposal "full Co1 acts nontrivially on Q10".
-/

namespace Integration.OggSSP2BCo1TenDimensionalNoGo

def sourcedCo1MinimalNontrivialChar2Dimension : ℕ := 24

theorem completionTen_lt_Co1_min_nontrivial :
    10 < sourcedCo1MinimalNontrivialChar2Dimension := by
  decide

structure SourcedCo1Char2ModuleDimension where
  dimension : ℕ
  nontrivial : Bool
  sourceLowerBound :
    nontrivial = true →
      sourcedCo1MinimalNontrivialChar2Dimension ≤ dimension

theorem no_nontrivial_full_Co1_dimension_ten
    (M : SourcedCo1Char2ModuleDimension)
    (hdim : M.dimension = 10) :
    M.nontrivial ≠ true := by
  intro h
  have h24 : 24 ≤ M.dimension := M.sourceLowerBound h
  omega

theorem any_dimension_ten_full_Co1_candidate_is_trivial
    (M : SourcedCo1Char2ModuleDimension)
    (hdim : M.dimension = 10) :
    M.nontrivial = false := by
  cases h : M.nontrivial with
  | false => exact h
  | true =>
      exact False.elim ((no_nontrivial_full_Co1_dimension_ten M hdim) h)

/-- The nontrivial pair-swap demanded by Completion10 therefore cannot be the
restriction of a full-Co1 action on a genuine 10-dimensional Co1 subquotient. -/
theorem full_Co1_cannot_supply_completion10_binary_flip
    (M : SourcedCo1Char2ModuleDimension)
    (hdim : M.dimension = 10)
    (hflipRequiresNontrivial : M.nontrivial = true) :
    False :=
  (no_nontrivial_full_Co1_dimension_ten M hdim) hflipRequiresNontrivial

end Integration.OggSSP2BCo1TenDimensionalNoGo
