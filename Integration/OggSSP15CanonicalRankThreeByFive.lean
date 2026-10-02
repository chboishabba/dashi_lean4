import Integration.MoonshineSSP15SignedFRACTRANBranch
import Mathlib

/-!
# Canonical Ogg rank -> 5 × 3 SSP15 presentation

The existing prime/internal table groups the increasing Ogg-prime order into
five consecutive blocks of three.  This module makes that factorisation exact:

  rank = 3 * block5 + phaseResidue3.

Thus the current 5×3 presentation is reproducible from the repository's
canonical ordered Ogg carrier.  This does not make block/phase an intrinsic
modular invariant or a local formula of the nonary Ogg address.
-/

namespace Integration.OggSSP15CanonicalRankThreeByFive

open Integration.MoonshineSSP15SignedFRACTRANBranch
open Integration.MoonshineNeutralCuspRelationCrossPollination

inductive Rank15
  | r00 | r01 | r02 | r03 | r04
  | r05 | r06 | r07 | r08 | r09
  | r10 | r11 | r12 | r13 | r14
  deriving DecidableEq, Repr, Fintype

def canonicalRankOrder : List Rank15 :=
  [.r00,.r01,.r02,.r03,.r04,.r05,.r06,.r07,.r08,.r09,.r10,.r11,.r12,.r13,.r14]

def rankToPrime : Rank15 → SSPPrime
  | .r00 => .p2
  | .r01 => .p3
  | .r02 => .p5
  | .r03 => .p7
  | .r04 => .p11
  | .r05 => .p13
  | .r06 => .p17
  | .r07 => .p19
  | .r08 => .p23
  | .r09 => .p29
  | .r10 => .p31
  | .r11 => .p41
  | .r12 => .p47
  | .r13 => .p59
  | .r14 => .p71

def primeToRank : SSPPrime → Rank15
  | .p2 => .r00
  | .p3 => .r01
  | .p5 => .r02
  | .p7 => .r03
  | .p11 => .r04
  | .p13 => .r05
  | .p17 => .r06
  | .p19 => .r07
  | .p23 => .r08
  | .p29 => .r09
  | .p31 => .r10
  | .p41 => .r11
  | .p47 => .r12
  | .p59 => .r13
  | .p71 => .r14

theorem prime_rank_roundtrip (p : SSPPrime) :
    rankToPrime (primeToRank p) = p := by
  cases p <;> rfl

theorem rank_prime_roundtrip (r : Rank15) :
    primeToRank (rankToPrime r) = r := by
  cases r <;> rfl

def canonicalOggOrder : List SSPPrime :=
  [.p2,.p3,.p5,.p7,.p11,.p13,.p17,.p19,.p23,.p29,.p31,.p41,.p47,.p59,.p71]

theorem rank_order_maps_to_canonical_ogg_order :
    canonicalRankOrder.map rankToPrime = canonicalOggOrder := by
  rfl

def rankNat : Rank15 → Nat
  | .r00 => 0 | .r01 => 1 | .r02 => 2 | .r03 => 3 | .r04 => 4
  | .r05 => 5 | .r06 => 6 | .r07 => 7 | .r08 => 8 | .r09 => 9
  | .r10 => 10 | .r11 => 11 | .r12 => 12 | .r13 => 13 | .r14 => 14

def block5Nat : Rank15 → Nat
  | .r00 | .r01 | .r02 => 0
  | .r03 | .r04 | .r05 => 1
  | .r06 | .r07 | .r08 => 2
  | .r09 | .r10 | .r11 => 3
  | .r12 | .r13 | .r14 => 4

def phaseResidueNat : Rank15 → Nat
  | .r00 | .r03 | .r06 | .r09 | .r12 => 0
  | .r01 | .r04 | .r07 | .r10 | .r13 => 1
  | .r02 | .r05 | .r08 | .r11 | .r14 => 2

theorem rank_three_by_five_arithmetic (r : Rank15) :
    rankNat r = 3 * block5Nat r + phaseResidueNat r := by
  cases r <;> rfl

def rankMode : Rank15 → Mode5
  | .r00 | .r01 | .r02 => .m09
  | .r03 | .r04 | .r05 => .m18
  | .r06 | .r07 | .r08 => .m27
  | .r09 | .r10 | .r11 => .m36
  | .r12 | .r13 | .r14 => .m45

def rankPhase : Rank15 → BalancedPhase
  | .r00 | .r03 | .r06 | .r09 | .r12 => .negative
  | .r01 | .r04 | .r07 | .r10 | .r13 => .zero
  | .r02 | .r05 | .r08 | .r11 | .r14 => .positive

def rankToInternal (r : Rank15) : InternalLane :=
  (rankMode r, rankPhase r)

theorem existing_prime_to_internal_factors_through_rank (p : SSPPrime) :
    primeToInternal p = rankToInternal (primeToRank p) := by
  cases p <;> rfl

def modeBlockNat : Mode5 → Nat
  | .m09 => 0 | .m18 => 1 | .m27 => 2 | .m36 => 3 | .m45 => 4

def phaseToResidue : BalancedPhase → Nat
  | .negative => 0 | .zero => 1 | .positive => 2

theorem rank_mode_block_agrees (r : Rank15) :
    modeBlockNat (rankMode r) = block5Nat r := by
  cases r <;> rfl

theorem rank_phase_residue_agrees (r : Rank15) :
    phaseToResidue (rankPhase r) = phaseResidueNat r := by
  cases r <;> rfl

inductive CanonicalRankChartIsIntrinsicModularInvariant : Prop
inductive CanonicalRankChartIsLocalAddressFormula : Prop

theorem rank_chart_not_intrinsic_modular :
    ¬ CanonicalRankChartIsIntrinsicModularInvariant := by
  intro h; cases h

theorem rank_chart_not_local_address_formula :
    ¬ CanonicalRankChartIsLocalAddressFormula := by
  intro h; cases h

structure Boundary where
  rankPrimeBidiPaid : Bool
  rankOrderMatchesCanonicalOggOrder : Bool
  rankSplitsThreeTimesBlockPlusResidue : Bool
  existingPrimeInternalFactorsThroughRank : Bool
  fiveBlocksOfThreeRecovered : Bool
  canonicalRelativeToRepositoryOrder : Bool
  intrinsicModularInvariantClaimed : Bool
  localAddressFormulaClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  rankPrimeBidiPaid := true
  rankOrderMatchesCanonicalOggOrder := true
  rankSplitsThreeTimesBlockPlusResidue := true
  existingPrimeInternalFactorsThroughRank := true
  fiveBlocksOfThreeRecovered := true
  canonicalRelativeToRepositoryOrder := true
  intrinsicModularInvariantClaimed := false
  localAddressFormulaClaimed := false

end Integration.OggSSP15CanonicalRankThreeByFive
