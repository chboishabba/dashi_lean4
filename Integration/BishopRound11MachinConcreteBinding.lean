import Integration.BishopVendoredArithmeticConcrete
import Integration.BishopRound11MachinSourceBinding
import Integration.MoonshineEisensteinRound11RouteB

/-!
# Route-B binding specialized to the concrete pinned Bishop arithmetic mirror

Integration.BishopVendoredArithmeticConcrete reconstructs the exact arithmetic
definitions from the pinned vendored Bishop Real.agda. Therefore the
Round11/Machin source-binding surface no longer needs an arbitrary arithmetic
mirror parameter.

The sole remaining source replay object is now the convergence/transcendental
binding itself.

This specialization still does not claim generated Agda replay.
-/

namespace Integration.BishopRound11MachinConcreteBinding

open Filter
open Complex
open UpperHalfPlane

open Integration.BishopVendoredArithmeticConcrete
open Integration.BishopVendoredRealEvaluation
open Integration.BishopRound11MachinSourceBinding
open Integration.MoonshineEisensteinRound11RouteB

noncomputable section

abbrev Arithmetic : VendoredArithmeticMirror :=
  concreteVendoredArithmeticMirror

abbrev SourceBinding :=
  Round11MachinSourceBinding Arithmetic

/-- One concrete source binding now immediately yields the faithful primitive
real extraction; the source arithmetic no longer appears as an input. -/
def primitiveExtraction
    (B : SourceBinding) :=
  Integration.BishopRound11MachinSourceBinding.primitiveExtraction
    Arithmetic B

def faithfulPrimitiveExtraction
    (B : SourceBinding) :=
  Integration.BishopRound11MachinSourceBinding.faithfulPrimitiveExtraction
    Arithmetic B

/-- End-to-end route-B source complex carrier specialized to the pinned
arithmetic mirror. -/
abbrev RouteComplex
    (B : SourceBinding) :=
  Integration.MoonshineEisensteinRound11RouteB.RouteComplex Arithmetic B

def mapRouteComplex
    {B : SourceBinding}
    (z : RouteComplex B) : ℂ :=
  Integration.MoonshineEisensteinRound11RouteB.mapRouteComplex z

theorem mapped_sourceE4_tendsto_mathlib_E4
    {B : SourceBinding}
    (τs : RouteComplex B)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ)) :
    Tendsto
      (fun N =>
        Integration.MoonshineEisensteinRound11RouteB.mapRouteComplex
          (Integration.MoonshineEisensteinRound11RouteB.sourceE4
            (A := Arithmetic) (B := B) N
            (Integration.MoonshineEisensteinRound11RouteB.sourceQ τs)))
      atTop
      (𝓝 (Integration.MoonshineEisensteinAnalytic.E4 τ)) :=
  Integration.MoonshineEisensteinRound11RouteB
    .mapped_sourceE4_tendsto_mathlib_E4 τs τ hτ

theorem mapped_sourceE6_tendsto_mathlib_E6
    {B : SourceBinding}
    (τs : RouteComplex B)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ)) :
    Tendsto
      (fun N =>
        Integration.MoonshineEisensteinRound11RouteB.mapRouteComplex
          (Integration.MoonshineEisensteinRound11RouteB.sourceE6
            (A := Arithmetic) (B := B) N
            (Integration.MoonshineEisensteinRound11RouteB.sourceQ τs)))
      atTop
      (𝓝 (Integration.MoonshineEisensteinAnalytic.E6 τ)) :=
  Integration.MoonshineEisensteinRound11RouteB
    .mapped_sourceE6_tendsto_mathlib_E6 τs τ hτ

structure Boundary where
  concretePinnedArithmeticMirrorOwned : Bool
  arbitraryArithmeticMirrorInputRemoved : Bool
  faithfulExtractionCompilerSpecialized : Bool
  endToEndEisensteinCompilerSpecialized : Bool
  canonicalCompletionBindingInhabited : Bool
  canonicalBindingUniqueUpToBishopEquivalence : Bool

  generatedAgdaReplayObserved : Bool
  exactHeadLeanKernelReceiptObserved : Bool

def boundary : Boundary where
  concretePinnedArithmeticMirrorOwned := true
  arbitraryArithmeticMirrorInputRemoved := true
  faithfulExtractionCompilerSpecialized := true
  endToEndEisensteinCompilerSpecialized := true
  canonicalCompletionBindingInhabited := true
  canonicalBindingUniqueUpToBishopEquivalence := true

  generatedAgdaReplayObserved := false
  exactHeadLeanKernelReceiptObserved := false

end

end Integration.BishopRound11MachinConcreteBinding
