import Mathlib
import Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource

/-!
# p=2 Gamma_0(4) source as two degree-2 isogeny steps

A rank-4 cyclic subgroup with rank-2 subflag is exposed source-facing as a
length-two degree-2 isogeny chain, with explicit witnesses that the first
kernel is the subflag and the composite kernel is the Gamma_0(4) subgroup.

This is only an acquisition interface; no arithmetic chain is constructed.
-/

namespace Integration.OggSSPP2Gamma0FourTwoIsogenyChainSource

open Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource

structure DegreeTwoIsogenyStep where
  SourceCurve : Type
  TargetCurve : Type
  Kernel : Type
  degree : Nat
  degreeIsTwo : degree = 2
  kernelRank : Nat
  kernelRankIsTwo : kernelRank = 2
  finiteFlatKernel : Prop

structure Gamma0FourTwoIsogenyChain where
  E0 : Type
  E1 : Type
  E2 : Type
  K1 : Type
  K2 : Type
  KComposite : Type
  firstStep : DegreeTwoIsogenyStep
  secondStep : DegreeTwoIsogenyStep
  middleCurveMatches :
    firstStep.TargetCurve = secondStep.SourceCurve
  compositeKernelRank : Nat
  compositeKernelRankIsFour :
    compositeKernelRank = 4
  firstKernelIsOrderTwoSubflag : Prop
  compositeKernelIsGamma0FourCyclic : Prop
  characteristicTwoBadPrimeSemantics : Prop
  sourceReference : String

structure ChainToSubgroupDatumRecognition
    (chain : Gamma0FourTwoIsogenyChain) where
  subgroupDatum : Gamma0FourFiniteFlatDatum
  firstStepKernelMatchesSubflag : Prop
  compositeKernelMatchesOrderFourSubgroup : Prop

inductive Residual
  | missingFirstFiniteFlatDegreeTwoStep
  | missingSecondFiniteFlatDegreeTwoStep
  | missingCompositeCyclicityWitness
  | missingSubflagCompatibility
  | missingFrobeniusTransportOnChain
  deriving DecidableEq, Repr

structure Boundary where
  twoStepPresentationTyped : Bool
  eachStepDegreeTwoRequired : Bool
  compositeRankFourRequired : Bool
  compositeCyclicityStillExplicitWitness : Bool
  orderTwoSubflagStillExplicitWitness : Bool
  arithmeticChainConstructed : Bool
  firstResidual : Residual
  deriving Repr

def canonicalBoundary : Boundary where
  twoStepPresentationTyped := true
  eachStepDegreeTwoRequired := true
  compositeRankFourRequired := true
  compositeCyclicityStillExplicitWitness := true
  orderTwoSubflagStillExplicitWitness := true
  arithmeticChainConstructed := false
  firstResidual := .missingFirstFiniteFlatDegreeTwoStep

end Integration.OggSSPP2Gamma0FourTwoIsogenyChainSource
