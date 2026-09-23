import Integration.BishopRound11MachinSourceBinding
import Integration.MoonshineEisensteinAgdaTarget
import Integration.MoonshineDeltaFinalMinCut

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
open Integration.BishopVendoredOrderConvergenceEvaluation
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

/-- Exact Bishop rational coefficient used by the Agda normalized finite Delta. -/
def sourceOneOver1728
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A} :
    RouteComplex A B :=
  ⟨rational (1 / 1728 : ℚ), A.zero⟩

theorem map_sourceOneOver1728
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A} :
    mapRouteComplex (sourceOneOver1728 (A := A) (B := B)) =
      (1 / 1728 : ℂ) := by
  change
    (⟨eval (rational (1 / 1728 : ℚ)), eval A.zero⟩ : ℂ) =
      (1 / 1728 : ℂ)
  rw [eval_rational, A.eval_zero]
  norm_num

/-- Literal source normalized finite Delta, matching the Bishop rational
embedding used in Agda. -/
def sourceNormalizedDelta
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (N : ℕ)
    (τs : RouteComplex A B) :
    RouteComplex A B :=
  SourceComplex.mul
    sourceOneOver1728
    (sourceDiscriminantNumerator N τs)

theorem map_sourceNormalizedDelta
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (τs : RouteComplex A B)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ))
    (N : ℕ) :
    mapRouteComplex (sourceNormalizedDelta N τs) =
      normalizedDeltaAt N τ := by
  unfold sourceNormalizedDelta
  rw [mapRouteComplex, mapComplex_mul,
      map_sourceOneOver1728,
      map_sourceDiscriminantNumerator τs τ hτ]
  simp [normalizedDeltaAt, div_eq_mul_inv]
  ring

theorem mapped_sourceNormalizedDelta_tendsto
    {A : VendoredArithmeticMirror}
    {B : Round11MachinSourceBinding A}
    (τs : RouteComplex A B)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ)) :
    Tendsto
      (fun N => mapRouteComplex (sourceNormalizedDelta N τs))
      atTop
      (𝓝 (normalizedDeltaLimit τ)) := by
  simpa only [map_sourceNormalizedDelta τs τ hτ] using
    normalizedDeltaAt_tendsto τ

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

/-- The formerly independent classical same-object seam is closed on the
Lean target by the pin-local theorem; this does not depend on inhabiting the
Agda source binding. -/
theorem eta24_eq_normalizedDelta_target
    (τ : ℍ) :
    Integration.MoonshineEta24Pinned.eta24 τ =
      normalizedDeltaLimit τ :=
  Integration.MoonshineDeltaFinalMinCut
    .canonicalEta24NormalizedDeltaSameObject τ

/-- Hence normalized-Delta nonvanishing and sixfold phase are already
hypothesis-free on the target side before the cross-language replay is paid. -/
theorem normalizedDelta_target_ne_zero
    (τ : ℍ) :
    normalizedDeltaLimit τ ≠ 0 :=
  Integration.MoonshineDeltaFinalMinCut
    .normalizedDelta_ne_zero_canonical τ

structure Round11RouteBBoundary where
  oneSourceBindingBuildsPrimitiveExtraction : Bool
  sourceQTransportOwned : Bool
  sourceE4TransportOwned : Bool
  sourceE6TransportOwned : Bool
  mappedSourceE4ConvergesToMathlibE4 : Bool
  mappedSourceE6ConvergesToMathlibE6 : Bool
  mappedSourceDiscriminantNumeratorConverges : Bool
  sourceNormalizedDeltaObjectBound : Bool
  mappedSourceNormalizedDeltaConverges : Bool

  actualAgdaRound11MachinBindingInhabited : Bool
  eta24SameObjectWithNormalizedE4E6Delta : Bool

def round11RouteBBoundary : Round11RouteBBoundary where
  oneSourceBindingBuildsPrimitiveExtraction := true
  sourceQTransportOwned := true
  sourceE4TransportOwned := true
  sourceE6TransportOwned := true
  mappedSourceE4ConvergesToMathlibE4 := true
  mappedSourceE6ConvergesToMathlibE6 := true
  mappedSourceDiscriminantNumeratorConverges := true
  sourceNormalizedDeltaObjectBound := true
  mappedSourceNormalizedDeltaConverges := true

  actualAgdaRound11MachinBindingInhabited := false
  eta24SameObjectWithNormalizedE4E6Delta := true

end

end Integration.MoonshineEisensteinRound11RouteB
