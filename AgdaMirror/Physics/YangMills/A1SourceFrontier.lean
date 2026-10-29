import AgdaMirror.Physics.YangMills.ProofTargetSurface

/-!
# Yang-Mills Row A1 golden-Agda frontier mirror

This module mirrors the canonical Agda owner
`DASHI.Unified.YMA1SourceFrontierExact`.

Agda remains theorem authority.
This file adds no Clay promotion.
The Lean mirror records status and source identity only.
-/

namespace AgdaMirror.Physics.YangMills.A1SourceFrontier

open YMSourceAuthoritySurface
open ProofTargetSurface

def goldenAgdaModule : String :=
  "DASHI.Unified.YMA1SourceFrontierExact"

def gaussianObject : String :=
  "Ahat(U) = C(U)^* A(U) C(U)"

def gaussianFirstVariation : String :=
  "D Ahat = C'^* A C + C^* A' C + C^* A C'"

def finiteGLowerBound : String :=
  "beta >= b_fixed - C_beta * gamma^4"

def gate4FormalGapCount : Nat := 58

theorem gate4FormalGapCount_eq_fiftyEight : gate4FormalGapCount = 58 := rfl

def frozenResearchCount : Nat := 4

theorem frozenResearchCount_eq_four : frozenResearchCount = 4 := rfl

def rowAPromoted : Bool := false

theorem rowAPromoted_false : rowAPromoted = false := rfl

def qPrimeTarget : ProofTargetSurface :=
  mkProofTargetSurfaceWithAuthority
    "literal CMP98 one-step Q prime"
    "Bałaban CMP98, DOI 10.1007/BF01211042"
    "differentiate the literal one-step averaging operator on the selected source carrier"
    "same source convention and selected eliminated-coordinate pivot"
    "literal Q' data for Q C' = - Q' C"
    "Row A1 fixed-coordinate Gaussian"
    "C' remains source-conditional"
    .openTarget
    .balabanCmp099
    "DASHI.Unified.YMA1SourceFrontierExact.literalCMP98QPrime"
    .postulateImport
    .openTarget

def fixedGaussianPatchTarget : ProofTargetSurface :=
  mkProofTargetSurfaceWithAuthority
    "literal fixed-coordinate positive Gaussian patch"
    "Bałaban CMP99/CMP109, DOIs 10.1007/BF01240355 and 10.1007/BF01215223"
    "identify the source C*AC operator and prove a positive-measure lower patch"
    "mixed Wilson 64-atom compiler, coordinate embedding derivative, and source normalization"
    "b_fixed > 0 on the same RG family"
    "Row A1 beta positivity"
    "Row A remains non-promoted"
    .openTarget
    .balabanCmp109
    "DASHI.Unified.YMA1SourceFrontierExact.literalFixedCoordinatePositivePatch"
    .postulateImport
    .openTarget

def fiveChannelHistoryTarget : ProofTargetSurface :=
  mkProofTargetSurfaceWithAuthority
    "history-uniform five-channel finite-g remainder"
    "Bałaban CMP109/CMP116"
    "betaInt >= -C_beta*g^4 uniformly over admissible preceding-coupling history"
    "literal five-channel source identification"
    "finite nonnegative C_beta on the same RG family"
    "Row A1 small-coupling absorption"
    "history must not be subtracted twice"
    .openTarget
    .balabanCmp109
    "DASHI.Unified.YMA1SourceFrontierExact.literalFiveChannelUniformOverHistory"
    .postulateImport
    .openTarget

def cumulativeSensitivityTarget : ProofTargetSurface :=
  mkProofTargetSurfaceWithAuthority
    "literal cumulative beta sensitivity below one"
    "parallel Lean cross-prover lane; Agda authority remains conditional"
    "|B_K(u)-B_K(v)| <= q*|u-v| with q < 1"
    "explicit marginal coordinate plus contracting irrelevant history"
    "shooting contraction for the tuned bare coupling"
    "Row A terminal tuning"
    "cross-prover evidence cannot promote Agda"
    .openTarget
    .dashiInternalProof
    "DASHI.Physics.YangMills.BalabanRowARecentLeanCrossProverProgressExact.literalCumulativeBetaSensitivityQStrictlyBelowOneCurrentLevel"
    .consequenceProof
    .openTarget

def canonicalTargets : List ProofTargetSurface :=
  [qPrimeTarget, fixedGaussianPatchTarget, fiveChannelHistoryTarget,
   cumulativeSensitivityTarget]

theorem noClayPromotion : clayYangMillsPromoted = false :=
  clayYangMillsPromoted_false

end AgdaMirror.Physics.YangMills.A1SourceFrontier
