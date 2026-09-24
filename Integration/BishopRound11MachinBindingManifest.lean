import Integration.BishopRound11MachinSourceBinding
import Integration.BishopVendoredArithmeticConcrete
import Integration.BishopRound11MachinConcreteBinding
import Integration.BishopRound11MachinCanonicalBinding
import Integration.MoonshineEisensteinRound11CanonicalRouteB
import Integration.MoonshineEisensteinRound11RouteB

/-!
# Content-addressed Agda/Lean route-B binding manifest

This module pins the Lean route-B mirror to the exact Agda source blobs that
define the vendored-Bishop/Round11/Machin/Eisenstein lane.

It is a provenance contract, not an Agda elaboration claim.

The blob IDs are Git object IDs returned for the current Agda branch. The
vendored Bishop source is a git submodule; the semantic mirror is pinned to
upstream commit

  240e38c7f6938f20f865b1f956c5f084da48bd54

whose Real.agda / Sequence.agda definitions are the representation mirrored by
Integration.BishopVendored*.

A future generated importer/replay only has to establish that the source
objects named below come from these pinned blobs and instantiate the already
proved Lean binding structures. All downstream analytic consequences then
compile through existing route-B theorems.
-/

namespace Integration.BishopRound11MachinBindingManifest

structure SourceBlob where
  path : String
  gitBlob : String

deriving Repr, DecidableEq

def bishopSubmoduleRepository : String :=
  "https://github.com/viktorcsimma/bishop.git"

def bishopSubmoduleCommit : String :=
  "240e38c7f6938f20f865b1f956c5f084da48bd54"

def sourceInstanceBlob : SourceBlob :=
  ⟨"DASHI/Moonshine/BishopRound11MachinSetoidComplexInstanceExact.agda",
    "ec132e001eeb7836078561e88fe2b3f54438facb"⟩

def machinConstructionBlob : SourceBlob :=
  ⟨"DASHI/Foundations/BishopMachinArctanConstructionExact.agda",
    "be11dee1db4eb6856346267134dcd85fed96fc2a"⟩

def exponentialConvergenceBlob : SourceBlob :=
  ⟨"DASHI/Foundations/BishopExponentialSeriesConvergenceExact.agda",
    "b62d767e74c6473e31bdf86458d93445656f6978"⟩

def trigConvergenceBlob : SourceBlob :=
  ⟨"DASHI/Foundations/BishopConcreteTrigSeriesConvergenceExact.agda",
    "75b8b72ea4e240bfde706272beb5ff5e5fba9af5"⟩

def setoidComplexBlob : SourceBlob :=
  ⟨"DASHI/Analysis/BishopSetoidComplexExact.agda",
    "739af368ced4b730225db4177529b281f4e8c493"⟩

def finiteQSeriesBlob : SourceBlob :=
  ⟨"DASHI/Moonshine/JInvariantEisensteinBishopSetoidFiniteQSeriesExact.agda",
    "4787feafbd9630dc439556543c42c6b75bf7fdbd"⟩

def extractionBlob : SourceBlob :=
  ⟨"DASHI/Moonshine/JInvariantEisensteinBishopSetoidExtractionExact.agda",
    "baee86e7085c9193227142eb9713df9d2e4a546e"⟩

def loadBearingBlobs : List SourceBlob :=
  [ sourceInstanceBlob
  , machinConstructionBlob
  , exponentialConvergenceBlob
  , trigConvergenceBlob
  , setoidComplexBlob
  , finiteQSeriesBlob
  , extractionBlob
  ]

structure SourceTheoremBinding where
  agdaOwner : String
  agdaDeclaration : String
  leanOwner : String
  leanDeclaration : String

deriving Repr, DecidableEq

def expBinding : SourceTheoremBinding :=
  ⟨sourceInstanceBlob.path,
   "round11MachinExpConverges",
   "Integration.BishopRound11MachinSourceBinding",
   "Round11MachinSourceBinding.expConverges"⟩

def sineBinding : SourceTheoremBinding :=
  ⟨sourceInstanceBlob.path,
   "round11MachinSineConverges",
   "Integration.BishopRound11MachinSourceBinding",
   "Round11MachinSourceBinding.sinConverges"⟩

def cosineBinding : SourceTheoremBinding :=
  ⟨sourceInstanceBlob.path,
   "round11MachinCosineConverges",
   "Integration.BishopRound11MachinSourceBinding",
   "Round11MachinSourceBinding.cosConverges"⟩

def atanFifthBinding : SourceTheoremBinding :=
  ⟨sourceInstanceBlob.path,
   "round11MachinAtanOneFifthConverges",
   "Integration.BishopRound11MachinSourceBinding",
   "Round11MachinSourceBinding.atanOneFifthConverges"⟩

def atan239Binding : SourceTheoremBinding :=
  ⟨sourceInstanceBlob.path,
   "round11MachinAtanOneTwoHundredThirtyNinthConverges",
   "Integration.BishopRound11MachinSourceBinding",
   "Round11MachinSourceBinding.atanOneTwoHundredThirtyNinthConverges"⟩

def machinPiBinding : SourceTheoremBinding :=
  ⟨machinConstructionBlob.path,
   "bishopMachinPi",
   "Integration.BishopVendoredMachinPiSemantics",
   "machinPiB"⟩

def theoremBindings : List SourceTheoremBinding :=
  [ expBinding
  , sineBinding
  , cosineBinding
  , atanFifthBinding
  , atan239Binding
  , machinPiBinding
  ]

/-- The manifest itself is fully concrete and contains no theorem-shaped
placeholder. -/
structure ManifestBoundary where
  bishopSubmoduleCommitPinned : Bool
  allAgdaLoadBearingFilesContentAddressed : Bool
  sourceToLeanDeclarationTableOwned : Bool
  primitiveExtractionCompilerAlreadyOwned : Bool
  endToEndEisensteinCompilerAlreadyOwned : Bool
  concretePinnedArithmeticMirrorOwned : Bool
  round11BindingSpecializedToPinnedArithmetic : Bool
  canonicalLeanBindingInhabited : Bool
  everyAdmissibleBindingSetoidEquivalentToCanonical : Bool
  hypothesisFreeCanonicalRouteBConstructed : Bool

  generatedAgdaReplayObserved : Bool
  leanKernelReceiptObserved : Bool

def manifestBoundary : ManifestBoundary where
  bishopSubmoduleCommitPinned := true
  allAgdaLoadBearingFilesContentAddressed := true
  sourceToLeanDeclarationTableOwned := true
  primitiveExtractionCompilerAlreadyOwned := true
  endToEndEisensteinCompilerAlreadyOwned := true
  concretePinnedArithmeticMirrorOwned := true
  round11BindingSpecializedToPinnedArithmetic := true
  canonicalLeanBindingInhabited := true
  everyAdmissibleBindingSetoidEquivalentToCanonical := true
  hypothesisFreeCanonicalRouteBConstructed := true

  generatedAgdaReplayObserved := false
  leanKernelReceiptObserved := false

end Integration.BishopRound11MachinBindingManifest
