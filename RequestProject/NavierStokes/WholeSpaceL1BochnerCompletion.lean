import Mathlib

/-!
# Whole-space Navier–Stokes L¹-to-Bochner cubature completion

Mathlib already contains the concrete Bochner/Lebesgue continuity theorem that
the Agda A-lane deliberately leaves abstract.  This file packages exactly the
two same-object convergence obligations now exposed by the finite Agda
compilers:

* scalar Fourier-energy approximants;
* coherent C³-valued nonlinear-convolution approximants.

The theorem used is `MeasureTheory.tendsto_setIntegral_of_L1'`: L¹ convergence
of integrable approximants implies convergence of their Bochner integrals.
No Fubini theorem and no pairwise Gram majorisation is required.
-/

open Filter MeasureTheory
open scoped Topology

namespace RequestProject.NavierStokes

/-- The whole-space frequency carrier used by the Lean analytic producer. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/--
A generic whole-space Bochner approximation theorem specialized to sequences.

This is the concrete Mathlib producer for the Agda statement
"coherent vector quadrature convergence": once the finite/simple approximants
are shown to converge in L¹ to the literal C³-valued convolution integrand,
their integrals converge automatically.
-/
theorem bochnerIntegral_tendsto_of_L1
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : R3 → E)
    (F : ℕ → R3 → E)
    (hF_integrable : ∀ᶠ n in atTop, Integrable (F n) volume)
    (hL1 :
      Tendsto
        (fun n => eLpNorm (F n - f) 1 volume)
        atTop (nhds 0)) :
    Tendsto
      (fun n => ∫ x : R3, F n x)
      atTop
      (nhds (∫ x : R3, f x)) := by
  simpa only [MeasureTheory.integral_univ] using
    (MeasureTheory.tendsto_setIntegral_of_L1'
      f hF_integrable hL1 (Set.univ : Set R3))

/--
Scalar specialization for the physical Fourier kinetic-energy density.
Thus the remaining A-side energy weld is reduced to an L¹ approximation
statement for the actual density `ξ ↦ |û(ξ)|²`.
-/
theorem energyIntegral_tendsto_of_L1
    (energyDensity : R3 → ℝ)
    (energyApprox : ℕ → R3 → ℝ)
    (h_integrable :
      ∀ᶠ n in atTop, Integrable (energyApprox n) volume)
    (hL1 :
      Tendsto
        (fun n => eLpNorm (energyApprox n - energyDensity) 1 volume)
        atTop (nhds 0)) :
    Tendsto
      (fun n => ∫ ξ : R3, energyApprox n ξ)
      atTop
      (nhds (∫ ξ : R3, energyDensity ξ)) :=
  bochnerIntegral_tendsto_of_L1
    energyDensity energyApprox h_integrable hL1

/--
Vector specialization for a real six-coordinate representation of C³.

Using `Fin 6 → ℝ` keeps this theorem directly consumable by the current Agda
Bishop-complex-three coordinate compiler: once the six real coordinates of
the projected nonlinear convolution are approximated in L¹, the coherent
vector integral converges as one Bochner object.
-/
abbrev Complex3RealCoordinates := EuclideanSpace ℝ (Fin 6)

theorem coherentVectorIntegral_tendsto_of_L1
    (integrand : R3 → Complex3RealCoordinates)
    (approx : ℕ → R3 → Complex3RealCoordinates)
    (h_integrable :
      ∀ᶠ n in atTop, Integrable (approx n) volume)
    (hL1 :
      Tendsto
        (fun n => eLpNorm (approx n - integrand) 1 volume)
        atTop (nhds 0)) :
    Tendsto
      (fun n => ∫ η : R3, approx n η)
      atTop
      (nhds (∫ η : R3, integrand η)) :=
  bochnerIntegral_tendsto_of_L1
    integrand approx h_integrable hL1

end RequestProject.NavierStokes
