import Integration.OggSSP2BActualStableCompletionSubquotient

/-!
# Co1 exterior-square candidate for the 2B Tate 276 head

The characteristic-two modular-moonshine object is acted on by `2^24.Co1`.
Historically the normal `2^24` action was expected to be trivial but was not
proved in the original construction.  Co1 has an actual 24-dimensional GF(2)
module, whose exterior square has dimension 276 and nontrivial modular extension
structure.

This owner makes the candidate executable while retaining both firewalls:
normal-`2^24` triviality and Tate↔exterior-square identity remain unpaid.
-/

namespace Integration.OggSSP2BCo1ExteriorSquareTateCandidate

abbrev co1NaturalDimension : Nat := 24
abbrev co1ExteriorSquareDimension : Nat := 276

theorem exterior_square_dimension_exact :
    co1NaturalDimension * (co1NaturalDimension - 1) / 2 = co1ExteriorSquareDimension := by
  norm_num

structure Status where
  modularMoonshineGroup2Pow24Co1Sourced : Bool
  normal2Pow24TrivialityHistoricallyUnproved : Bool
  co1Natural24GF2Sourced : Bool
  exteriorSquareRuntimeFingerprintScreenImplemented : Bool
  atlas2Pow24Co1Char2ProbeImplemented : Bool
  normal2Pow24ActsTriviallyOnWeightTwoTatePaid : Bool
  actualTate276IsCo1ExteriorSquarePaid : Bool

def canonicalStatus : Status where
  modularMoonshineGroup2Pow24Co1Sourced := true
  normal2Pow24TrivialityHistoricallyUnproved := true
  co1Natural24GF2Sourced := true
  exteriorSquareRuntimeFingerprintScreenImplemented := true
  atlas2Pow24Co1Char2ProbeImplemented := true
  normal2Pow24ActsTriviallyOnWeightTwoTatePaid := false
  actualTate276IsCo1ExteriorSquarePaid := false

inductive Normal2Pow24TrivialityPaid : Prop
inductive TateIsCo1ExteriorSquarePaid : Prop

theorem normal2pow24_triviality_still_open : ¬ Normal2Pow24TrivialityPaid := by
  intro h; cases h

theorem same_object_exterior_square_still_open : ¬ TateIsCo1ExteriorSquarePaid := by
  intro h; cases h

end Integration.OggSSP2BCo1ExteriorSquareTateCandidate
