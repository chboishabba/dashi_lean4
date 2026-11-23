import Integration.BishopMachinCanonicalBinding
import Integration.MoonshineEisensteinRouteB

/-!
# Hypothesis-free canonical Round11/Machin route B

This module specializes the generic route-B compiler to:

* the concrete source-faithful mirror of vendored Bishop arithmetic;
* the canonical Round11/Machin binding constructed from the Bishop completion
  equivalence and the classical power-series limits.

No source-binding parameter remains.

This is a mathematical same-object closure at Bishop setoid level.  It does not
claim that a generated importer has replayed the named Agda declarations or
that an exact-head Lean CI receipt has been observed.
-/

namespace Integration.MoonshineEisensteinCanonicalRouteB

open Filter
open Complex Real
open UpperHalfPlane hiding I
open scoped Topology

open Integration.BishopVendoredRealEvaluation
open Integration.BishopMachinCanonicalBinding
open Integration.MoonshineEisensteinRouteB
open Integration.MoonshineEisensteinAgdaTarget
open Integration.MoonshineEisensteinAnalytic

noncomputable section

abbrev Arithmetic :=
  Integration.BishopMachinCanonicalBinding.Arithmetic

abbrev Binding :=
  Integration.BishopMachinCanonicalBinding.canonicalBinding

abbrev RouteComplex :=
  Integration.MoonshineEisensteinRouteB.RouteComplex Arithmetic Binding

def mapRouteComplex (z : RouteComplex) : ℂ :=
  Integration.MoonshineEisensteinRouteB.mapRouteComplex z

def sourceQ (τ : RouteComplex) : RouteComplex :=
  Integration.MoonshineEisensteinRouteB.sourceQ τ

def sourceE4 (N : ℕ) (q : RouteComplex) : RouteComplex :=
  Integration.MoonshineEisensteinRouteB.sourceE4 N q

def sourceE6 (N : ℕ) (q : RouteComplex) : RouteComplex :=
  Integration.MoonshineEisensteinRouteB.sourceE6 N q

def sourceDiscriminantNumerator
    (N : ℕ) (τ : RouteComplex) : RouteComplex :=
  Integration.MoonshineEisensteinRouteB.sourceDiscriminantNumerator N τ

def sourceNormalizedDelta
    (N : ℕ) (τ : RouteComplex) : RouteComplex :=
  Integration.MoonshineEisensteinRouteB.sourceNormalizedDelta N τ

theorem map_sourceQ_eq_qOfTarget
    (τs : RouteComplex)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ)) :
    mapRouteComplex (sourceQ τs) = qOfTarget τ :=
  Integration.MoonshineEisensteinRouteB
    .map_sourceQ_eq_qOfTarget τs τ hτ

theorem mapped_sourceE4_tendsto_mathlib_E4
    (τs : RouteComplex)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ)) :
    Tendsto
      (fun N => mapRouteComplex (sourceE4 N (sourceQ τs)))
      atTop
      (𝓝 (E4 τ)) :=
  Integration.MoonshineEisensteinRouteB
    .mapped_sourceE4_tendsto_mathlib_E4 τs τ hτ

theorem mapped_sourceE6_tendsto_mathlib_E6
    (τs : RouteComplex)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ)) :
    Tendsto
      (fun N => mapRouteComplex (sourceE6 N (sourceQ τs)))
      atTop
      (𝓝 (E6 τ)) :=
  Integration.MoonshineEisensteinRouteB
    .mapped_sourceE6_tendsto_mathlib_E6 τs τ hτ

theorem mapped_sourceDiscriminantNumerator_tendsto
    (τs : RouteComplex)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ)) :
    Tendsto
      (fun N => mapRouteComplex (sourceDiscriminantNumerator N τs))
      atTop
      (𝓝 (discriminantNumeratorLimit τ)) :=
  Integration.MoonshineEisensteinRouteB
    .mapped_sourceDiscriminantNumerator_tendsto τs τ hτ

theorem mapped_sourceNormalizedDelta_tendsto
    (τs : RouteComplex)
    (τ : ℍ)
    (hτ : mapRouteComplex τs = (τ : ℂ)) :
    Tendsto
      (fun N => mapRouteComplex (sourceNormalizedDelta N τs))
      atTop
      (𝓝 (normalizedDeltaLimit τ)) :=
  Integration.MoonshineEisensteinRouteB
    .mapped_sourceNormalizedDelta_tendsto τs τ hτ

/-- The target of the hypothesis-free canonical source route is already the
same normalized Delta as eta^24 by the local pinned Lean theorem. -/
theorem eta24_eq_canonical_route_delta
    (τ : ℍ) :
    Integration.MoonshineEta24Pinned.eta24 τ =
      normalizedDeltaLimit τ :=
  Integration.MoonshineEisensteinRouteB
    .eta24_eq_normalizedDelta_target τ

/-- Consequently the target-side reflection/fixed-locus theorem is immediately
available after the canonical source route converges. -/
theorem canonical_target_inv_conj
    (τ : ℍ) :
    normalizedDeltaLimit (ModularGroup.S • negConj τ) =
      conj ((τ : ℂ) ^ 12 * normalizedDeltaLimit τ) :=
  normalizedDelta_inv_conj τ

structure Boundary where
  concreteVendoredArithmeticFixed : Bool
  canonicalBindingInhabited : Bool
  noSourceBindingParameterRemains : Bool
  sourceQCompilerHypothesisFree : Bool
  sourceE4E6ConvergenceHypothesisFree : Bool
  sourceDeltaConvergenceHypothesisFree : Bool
  eta24SameObjectTargetOwned : Bool
  targetReflectionOwned : Bool

  generatedAgdaReplayObserved : Bool
  exactHeadLeanKernelReceiptObserved : Bool

def boundary : Boundary where
  concreteVendoredArithmeticFixed := true
  canonicalBindingInhabited := true
  noSourceBindingParameterRemains := true
  sourceQCompilerHypothesisFree := true
  sourceE4E6ConvergenceHypothesisFree := true
  sourceDeltaConvergenceHypothesisFree := true
  eta24SameObjectTargetOwned := true
  targetReflectionOwned := true

  generatedAgdaReplayObserved := false
  exactHeadLeanKernelReceiptObserved := false

end

end Integration.MoonshineEisensteinCanonicalRouteB
