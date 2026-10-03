import Integration.OggSSP2BM22CompletionTenCandidate

/-!
# Runtime receipt: M24-duad restriction to M22 and bare-involution no-go

This file records the finite calculations produced by the repository's GAP /
AtlasRep / MeatAxe screens.  It is intentionally a runtime receipt, not a
replacement for a source-level same-object identification with the actual 2B
Tate module.

Observed on the M24 degree-276 duad permutation module restricted to M22:

  1^10 + 10a^5 + 10b^5 + 34^2 + 98

and both ten-dimensional factors are identified against the actual AtlasRep
modules `M22G1-f2r10aB0` and `M22G1-f2r10bB0`.

Observed on the unique M22 involution class in both 10a and 10b:

  rank(g-I) = 4,
  dim Fix(g) = 6,

so the Jordan type is J2^4 + J1^2, not the J2^5 action required by the old
Completion10 five-pair criterion.

The positive result is therefore existence of ten-dimensional M22 factors in
the finite duad model; the negative result kills only the *bare M22 involution*
as BinaryPhase.  Neither statement identifies a ten-dimensional subquotient
of the Carnahan--Urano Tate module.
-/

namespace Integration.OggSSP2BM22RuntimeReceipt

namespace C := Integration.OggSSP2BM22CompletionTenCandidate

inductive RuntimeFactorKind
  | trivialOne
  | tenA
  | tenB
  | thirtyFour
  | ninetyEight
  deriving DecidableEq, Repr, Fintype

def factorDimension : RuntimeFactorKind → ℕ
  | .trivialOne => 1
  | .tenA => 10
  | .tenB => 10
  | .thirtyFour => 34
  | .ninetyEight => 98

def factorMultiplicity : RuntimeFactorKind → ℕ
  | .trivialOne => 10
  | .tenA => 5
  | .tenB => 5
  | .thirtyFour => 2
  | .ninetyEight => 1

def weightedDimension (k : RuntimeFactorKind) : ℕ :=
  factorDimension k * factorMultiplicity k

theorem restricted_duad_dimension_closes_276 :
    weightedDimension .trivialOne
      + weightedDimension .tenA
      + weightedDimension .tenB
      + weightedDimension .thirtyFour
      + weightedDimension .ninetyEight
    = 276 := by
  decide

theorem tenA_multiplicity_is_five :
    factorMultiplicity .tenA = 5 := rfl

theorem tenB_multiplicity_is_five :
    factorMultiplicity .tenB = 5 := rfl

theorem total_ten_dimensional_factor_multiplicity :
    factorMultiplicity .tenA + factorMultiplicity .tenB = 10 := by
  decide

/-- The runtime AtlasRep identifications for the two ten-dimensional factors.
`none` for the other composition-factor dimensions is deliberate. -/
def atlasCandidateKind : RuntimeFactorKind → Option C.M22TenModuleKind
  | .tenA => some .golayCode
  | .tenB => some .golayCocode
  | _ => none

theorem tenA_identified_with_golayCode :
    atlasCandidateKind .tenA = some .golayCode := rfl

theorem tenB_identified_with_golayCocode :
    atlasCandidateKind .tenB = some .golayCocode := rfl

/-- Runtime involution fingerprint shared by 10a and 10b. -/
def runtimeBareM22InvolutionRank : ℕ := 4

def runtimeBareM22FixedDimension : ℕ := 6

def completionTenFivePairTargetRank : ℕ := 5

def completionTenFivePairTargetFixedDimension : ℕ := 5

theorem bare_m22_rank_misses_completion10 :
    runtimeBareM22InvolutionRank ≠ completionTenFivePairTargetRank := by
  decide

theorem bare_m22_fixed_dimension_misses_completion10 :
    runtimeBareM22FixedDimension ≠ completionTenFivePairTargetFixedDimension := by
  decide

theorem bare_m22_involution_cannot_meet_old_five_pair_fingerprint :
    ¬ (runtimeBareM22InvolutionRank = completionTenFivePairTargetRank
       ∧ runtimeBareM22FixedDimension = completionTenFivePairTargetFixedDimension) := by
  decide

/-- Dimension accounting for J2^4 + J1^2. -/
theorem runtime_jordan_dimension :
    2 * 4 + 1 * 2 = 10 := by
  decide

/-- The negative runtime result kills only the old bare-M22-involution
realization.  It does not kill ten-dimensional M22 subquotients themselves. -/
structure RuntimeBoundary where
  tenAObserved : Bool
  tenBObserved : Bool
  tenAAtlasRepIdentified : Bool
  tenBAtlasRepIdentified : Bool
  bareM22FivePairCompletionObserved : Bool
  actualTwoBTateSubquotientIdentified : Bool
  largerCompletionActionIdentified : Bool

def canonicalRuntimeBoundary : RuntimeBoundary where
  tenAObserved := true
  tenBObserved := true
  tenAAtlasRepIdentified := true
  tenBAtlasRepIdentified := true
  bareM22FivePairCompletionObserved := false
  actualTwoBTateSubquotientIdentified := false
  largerCompletionActionIdentified := false

end Integration.OggSSP2BM22RuntimeReceipt
