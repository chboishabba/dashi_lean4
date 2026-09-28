import Mathlib
import Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource
import Integration.OggSSPP2Gamma0FourTwoIsogenyChainSource

/-!
# Gamma_0(4) finite-flat subgroup data <-> two-isogeny-chain bidi contract

The subgroup presentation and the two-step degree-2 isogeny presentation may be
called the same arithmetic object only after exact maps both ways, two-sided
recovery, and explicit compatibility of the first kernel/subflag and composite
kernel/order-4 subgroup.

No arithmetic inhabitant is constructed here.
-/

namespace Integration.OggSSPP2Gamma0FourSubgroupIsogenyChainBidi

open Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource
open Integration.OggSSPP2Gamma0FourTwoIsogenyChainSource

structure Bidi where
  SubgroupState : Type
  ChainState : Type

  subgroupDatum :
    SubgroupState → Gamma0FourFiniteFlatDatum

  chainDatum :
    ChainState → Gamma0FourTwoIsogenyChain

  subgroupToChain :
    SubgroupState → ChainState

  chainToSubgroup :
    ChainState → SubgroupState

  subgroupRoundTrip :
    ∀ s, chainToSubgroup (subgroupToChain s) = s

  chainRoundTrip :
    ∀ s, subgroupToChain (chainToSubgroup s) = s

  firstKernelMatchesSelectedOrderTwoSubflag :
    ChainState → Prop

  firstKernelMatchesSelectedOrderTwoSubflagProof :
    ∀ state, firstKernelMatchesSelectedOrderTwoSubflag state

  compositeKernelMatchesSelectedOrderFourSubgroup :
    ChainState → Prop

  compositeKernelMatchesSelectedOrderFourSubgroupProof :
    ∀ state, compositeKernelMatchesSelectedOrderFourSubgroup state

  finiteFlatBadPrimeSemanticsPreserved :
    ChainState → Prop

  finiteFlatBadPrimeSemanticsPreservedProof :
    ∀ state, finiteFlatBadPrimeSemanticsPreserved state

theorem subgroupToChain_injective
    (b : Bidi) :
    Function.Injective b.subgroupToChain := by
  intro x y h
  calc
    x = b.chainToSubgroup (b.subgroupToChain x) :=
      (b.subgroupRoundTrip x).symm
    _ = b.chainToSubgroup (b.subgroupToChain y) := by rw [h]
    _ = y := b.subgroupRoundTrip y

theorem chainToSubgroup_injective
    (b : Bidi) :
    Function.Injective b.chainToSubgroup := by
  intro x y h
  calc
    x = b.subgroupToChain (b.chainToSubgroup x) :=
      (b.chainRoundTrip x).symm
    _ = b.subgroupToChain (b.chainToSubgroup y) := by rw [h]
    _ = y := b.chainRoundTrip y

structure Boundary where
  subgroupToChainMapRequired : Bool
  chainToSubgroupMapRequired : Bool
  twoSidedRecoveryRequired : Bool
  subflagCompatibilityRequired : Bool
  compositeKernelCompatibilityRequired : Bool
  finiteFlatSemanticsRequired : Bool
  arithmeticBidiConstructed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  subgroupToChainMapRequired := true
  chainToSubgroupMapRequired := true
  twoSidedRecoveryRequired := true
  subflagCompatibilityRequired := true
  compositeKernelCompatibilityRequired := true
  finiteFlatSemanticsRequired := true
  arithmeticBidiConstructed := false

end Integration.OggSSPP2Gamma0FourSubgroupIsogenyChainBidi
