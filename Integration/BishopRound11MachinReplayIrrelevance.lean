import Integration.BishopRound11MachinCanonicalBinding
import Integration.MoonshineEisensteinRound11RouteB

/-!
# Replay irrelevance for the Round11/Machin route-B semantics

A generated Agda replay is still required as provenance evidence that named
source declarations were imported/replayed.  It is no longer required to
determine the mathematical value of the route.

Every admissible binding is Bishop-equivalent to the canonical binding, and
the route compiler maps every admissible binding to the same canonical Lean
q/E4/E6/Delta targets.

This module proves that two arbitrary admissible bindings cannot change the
mapped finite Eisenstein or normalized-Delta values once their source points
map to the same upper-half-plane point.
-/

namespace Integration.BishopRound11MachinReplayIrrelevance

open Complex
open UpperHalfPlane
open Integration.BishopVendoredRealEvaluation
open Integration.BishopRound11MachinCanonicalBinding
open Integration.BishopRound11MachinSourceBinding
open Integration.MoonshineEisensteinRound11RouteB

noncomputable section

abbrev Arithmetic :=
  Integration.BishopRound11MachinCanonicalBinding.Arithmetic

theorem mapped_q_independent_of_binding
    {B₁ B₂ : Round11MachinSourceBinding Arithmetic}
    (τ₁ : RouteComplex Arithmetic B₁)
    (τ₂ : RouteComplex Arithmetic B₂)
    (τ : ℍ)
    (h₁ : mapRouteComplex τ₁ = (τ : ℂ))
    (h₂ : mapRouteComplex τ₂ = (τ : ℂ)) :
    mapRouteComplex (sourceQ τ₁) =
      mapRouteComplex (sourceQ τ₂) := by
  rw [map_sourceQ_eq_qOfTarget τ₁ τ h₁,
      map_sourceQ_eq_qOfTarget τ₂ τ h₂]

theorem mapped_e4_independent_of_binding
    {B₁ B₂ : Round11MachinSourceBinding Arithmetic}
    (τ₁ : RouteComplex Arithmetic B₁)
    (τ₂ : RouteComplex Arithmetic B₂)
    (τ : ℍ)
    (h₁ : mapRouteComplex τ₁ = (τ : ℂ))
    (h₂ : mapRouteComplex τ₂ = (τ : ℂ))
    (N : ℕ) :
    mapRouteComplex (sourceE4 N (sourceQ τ₁)) =
      mapRouteComplex (sourceE4 N (sourceQ τ₂)) := by
  rw [map_sourceE4_eq_e4At τ₁ τ h₁ N,
      map_sourceE4_eq_e4At τ₂ τ h₂ N]

theorem mapped_e6_independent_of_binding
    {B₁ B₂ : Round11MachinSourceBinding Arithmetic}
    (τ₁ : RouteComplex Arithmetic B₁)
    (τ₂ : RouteComplex Arithmetic B₂)
    (τ : ℍ)
    (h₁ : mapRouteComplex τ₁ = (τ : ℂ))
    (h₂ : mapRouteComplex τ₂ = (τ : ℂ))
    (N : ℕ) :
    mapRouteComplex (sourceE6 N (sourceQ τ₁)) =
      mapRouteComplex (sourceE6 N (sourceQ τ₂)) := by
  rw [map_sourceE6_eq_e6At τ₁ τ h₁ N,
      map_sourceE6_eq_e6At τ₂ τ h₂ N]

theorem mapped_deltaNumerator_independent_of_binding
    {B₁ B₂ : Round11MachinSourceBinding Arithmetic}
    (τ₁ : RouteComplex Arithmetic B₁)
    (τ₂ : RouteComplex Arithmetic B₂)
    (τ : ℍ)
    (h₁ : mapRouteComplex τ₁ = (τ : ℂ))
    (h₂ : mapRouteComplex τ₂ = (τ : ℂ))
    (N : ℕ) :
    mapRouteComplex (sourceDiscriminantNumerator N τ₁) =
      mapRouteComplex (sourceDiscriminantNumerator N τ₂) := by
  rw [map_sourceDiscriminantNumerator τ₁ τ h₁ N,
      map_sourceDiscriminantNumerator τ₂ τ h₂ N]

theorem mapped_normalizedDelta_independent_of_binding
    {B₁ B₂ : Round11MachinSourceBinding Arithmetic}
    (τ₁ : RouteComplex Arithmetic B₁)
    (τ₂ : RouteComplex Arithmetic B₂)
    (τ : ℍ)
    (h₁ : mapRouteComplex τ₁ = (τ : ℂ))
    (h₂ : mapRouteComplex τ₂ = (τ : ℂ))
    (N : ℕ) :
    mapRouteComplex (sourceNormalizedDelta N τ₁) =
      mapRouteComplex (sourceNormalizedDelta N τ₂) := by
  rw [map_sourceNormalizedDelta τ₁ τ h₁ N,
      map_sourceNormalizedDelta τ₂ τ h₂ N]

/-- In particular, every admissible replay has the same mapped finite route as
the canonical completion binding. -/
theorem mapped_normalizedDelta_eq_canonical
    {B : Round11MachinSourceBinding Arithmetic}
    (τB : RouteComplex Arithmetic B)
    (τC : RouteComplex Arithmetic canonicalBinding)
    (τ : ℍ)
    (hB : mapRouteComplex τB = (τ : ℂ))
    (hC : mapRouteComplex τC = (τ : ℂ))
    (N : ℕ) :
    mapRouteComplex (sourceNormalizedDelta N τB) =
      mapRouteComplex (sourceNormalizedDelta N τC) :=
  mapped_normalizedDelta_independent_of_binding
    τB τC τ hB hC N

structure Boundary where
  qReplayIndependent : Bool
  e4ReplayIndependent : Bool
  e6ReplayIndependent : Bool
  discriminantNumeratorReplayIndependent : Bool
  normalizedDeltaReplayIndependent : Bool
  canonicalBindingDeterminesMappedSemantics : Bool

  generatedAgdaReplayObserved : Bool

def boundary : Boundary where
  qReplayIndependent := true
  e4ReplayIndependent := true
  e6ReplayIndependent := true
  discriminantNumeratorReplayIndependent := true
  normalizedDeltaReplayIndependent := true
  canonicalBindingDeterminesMappedSemantics := true

  generatedAgdaReplayObserved := false

end

end Integration.BishopRound11MachinReplayIrrelevance
