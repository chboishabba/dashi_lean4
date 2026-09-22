import Integration.BishopRound11MachinSourceBinding
import Integration.MoonshineEisensteinAgdaTarget

/-!
# End-to-end Round11/Machin route-B compiler

This module composes the route-B pieces already proved:

1. one Round11/Machin source binding;
2. vendored Bishop evaluation into Lean Real;
3. source exp/sin/cos/Machin-pi semantic identification;
4. componentwise complex extraction;
5. literal source q/E4/E6 recurrence transport;
6. convergence of the mapped finite recurrences to Mathlib E4/E6.

No additional analytic hypothesis is introduced here.
-/

namespace Integration.MoonshineEisensteinRound11RouteB

open Filter
open Complex Real
open UpperHalfPlane hiding I
open scoped Topology

open Integration.BishopVendoredRealEvaluation
open Integration.BishopRound11MachinSourceBinding
open Integration.BishopVendoredTranscendentalExtraction
open Integration.MoonshineEisensteinPrimitiveExtraction
open Integration.MoonshineEisensteinAgdaTarget
open Integration.MoonshineEisensteinAnalytic

noncomputable section

def sourceReal
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    SourceRealTranscendental :=
  bishopSourceReal A (semanticMirror A B)

def sourcePackage
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    SourceComplexPackage where
  real := sourceReal A B
  expC := SourceComplex.expCartesian
  expCartesian := fun _ => rfl

def routeExtraction
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    PrimitiveRealExtraction (sourceReal A B) :=
  primitiveExtractionDirect A B

abbrev RouteComplex
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :=
  SourceComplex (sourceReal A B)

def mapRouteComplex
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (z : RouteComplex A B) : ℂ :=
  mapComplex (P := sourcePackage A B) (routeExtraction A B) z

def sourceQ
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (τ : RouteComplex A B) :
    RouteComplex A B :=
  Integration.MoonshineEisensteinPrimitiveExtraction.sourceQ
    (sourcePackage A B) τ

def sourceE4
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (N : ℕ) (q : RouteComplex A B) :
    RouteComplex A B :=
  Integration.MoonshineEisensteinPrimitiveExtraction.sourceE4
    (P := sourcePackage A B) N q

def sourceE6
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (N : ℕ) (q : RouteComplex A B) :
    RouteComplex A B :=
  Integration.MoonshineEisensteinPrimitiveExtraction.sourceE6
    (P := sourcePackage A B) N q

theorem map_sourceQ_eq_qOfTarget
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (τs : RouteComplex A B)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ)) :
    mapRouteComplex (sourceQ τs) = qOfTarget τ := by
  rw [mapRouteComplex, sourceQ,
    Integration.MoonshineEisensteinPrimitiveExtraction.map_sourceQ]
  simp only [qOfTarget, hτ]

theorem map_sourceE4_eq_e4At
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (τs : RouteComplex A B)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ))
    (N : ℕ) :
    mapRouteComplex (sourceE4 N (sourceQ τs)) = e4At N τ := by
  rw [mapRouteComplex, sourceE4,
    Integration.MoonshineEisensteinPrimitiveExtraction.map_sourceE4]
  simp only [e4At, map_sourceQ_eq_qOfTarget τs τ hτ]

theorem map_sourceE6_eq_e6At
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (τs : RouteComplex A B)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ))
    (N : ℕ) :
    mapRouteComplex (sourceE6 N (sourceQ τs)) = e6At N τ := by
  rw [mapRouteComplex, sourceE6,
    Integration.MoonshineEisensteinPrimitiveExtraction.map_sourceE6]
  simp only [e6At, map_sourceQ_eq_qOfTarget τs τ hτ]

theorem mapped_sourceE4_tendsto_mathlib_E4
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (τs : RouteComplex A B)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ)) :
    Tendsto
      (fun N => mapRouteComplex (sourceE4 N (sourceQ τs)))
      atTop
      (𝓝 (E4 τ)) := by
  simpa only [map_sourceE4_eq_e4At τs τ hτ] using
    e4At_tendsto_mathlib_E4 τ

theorem mapped_sourceE6_tendsto_mathlib_E6
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (τs : RouteComplex A B)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ)) :
    Tendsto
      (fun N => mapRouteComplex (sourceE6 N (sourceQ τs)))
      atTop
      (𝓝 (E6 τ)) := by
  simpa only [map_sourceE6_eq_e6At τs τ hτ] using
    e6At_tendsto_mathlib_E6 τ

def sourceSquare
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (z : RouteComplex A B) :
    RouteComplex A B :=
  SourceComplex.mul z z

def sourceCube
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (z : RouteComplex A B) :
    RouteComplex A B :=
  SourceComplex.mul (sourceSquare z) z

def sourceDiscriminantNumerator
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (N : ℕ)
    (τs : RouteComplex A B) :
    RouteComplex A B :=
  SourceComplex.sub
    (sourceCube (sourceE4 N (sourceQ τs)))
    (sourceSquare (sourceE6 N (sourceQ τs)))

theorem map_sourceDiscriminantNumerator
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (τs : RouteComplex A B)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ))
    (N : ℕ) :
    mapRouteComplex (sourceDiscriminantNumerator N τs) =
      discriminantNumeratorAt N τ := by
  unfold sourceDiscriminantNumerator sourceCube sourceSquare
  rw [mapRouteComplex,
    mapComplex_sub,
    mapComplex_mul,
    mapComplex_mul,
    mapComplex_mul,
    map_sourceE4_eq_e4At τs τ hτ,
    map_sourceE6_eq_e6At τs τ hτ]
  rfl

theorem mapped_sourceDiscriminantNumerator_tendsto
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (τs : RouteComplex A B)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ)) :
    Tendsto
      (fun N => mapRouteComplex (sourceDiscriminantNumerator N τs))
      atTop
      (𝓝 (discriminantNumeratorLimit τ)) := by
  simpa only [map_sourceDiscriminantNumerator τs τ hτ] using
    discriminantNumeratorAt_tendsto τ

structure Round11RouteBBoundary where
  oneSourceBindingBuildsPrimitiveExtraction : Bool
  sourceQTransportOwned : Bool
  sourceE4TransportOwned : Bool
  sourceE6TransportOwned : Bool
  mappedSourceE4ConvergesToMathlibE4 : Bool
  mappedSourceE6ConvergesToMathlibE6 : Bool
  mappedSourceDiscriminantNumeratorConverges : Bool

  actualAgdaRound11MachinBindingInhabited : Bool
  sourceNormalizedDeltaObjectBound : Bool
  eta24SameObjectWithNormalizedE4E6Delta : Bool

def round11RouteBBoundary : Round11RouteBBoundary where
  oneSourceBindingBuildsPrimitiveExtraction := true
  sourceQTransportOwned := true
  sourceE4TransportOwned := true
  sourceE6TransportOwned := true
  mappedSourceE4ConvergesToMathlibE4 := true
  mappedSourceE6ConvergesToMathlibE6 := true
  mappedSourceDiscriminantNumeratorConverges := true

  actualAgdaRound11MachinBindingInhabited := false
  sourceNormalizedDeltaObjectBound := false
  eta24SameObjectWithNormalizedE4E6Delta := false

end

end Integration.MoonshineEisensteinRound11RouteB
