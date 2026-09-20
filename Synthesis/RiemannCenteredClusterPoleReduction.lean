import Synthesis.RiemannFinalLiteralComplementCenteredExact
import Synthesis.RiemannRadiusZeroPoleCorrection
import Zeta23Bridge.LiteralWeilPrimeEvenCone

/-!
# Exact centered-taper cluster/pole reduction

Let

  h_r(u) = g(u) (cos(r u) - 1).

The prize-facing centered complement is

  S_h(t,0) = Off_h(t,0) + Gamma_h(t,0).

At radius zero, once the short support kills the prime channel, the literal
explicit formula gives exactly

  -S_h(t,0) = Cluster_h(t,0) + Pole_h(t,0).

The pole response of h_r is itself an exact radius difference:

  PoleEven(h_r,t,0)
    = PoleEven(g,t,r) - PoleEven(g,t,0).

Therefore, when r is the canonical pole-killing radius for g,

  PoleEven(g,t,r)=0,

the centered taper has

  PoleEven(h_r,t,0) = -PoleEven(g,t,0),

and the even-cone pole vector becomes

  ell(Pole_h) = 4 PoleEven(g,t,0).

So the final centered-sign problem is exactly

  S_h(t,0) <= 0
    <-> -Cluster_h(t,0) <= 4 PoleEven(g,t,0).

This file pays only the same-object algebra.  It does not assert the remaining
cluster-versus-pole inequality.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilPrimeEvenCone

theorem poleEvenResp_gammaCenteredTaper_zero
    {g : ℝ -> ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (t r : ℝ) :
    poleEvenResp (gammaCenteredTaper g r) t 0
      =
    poleEvenResp g t r - poleEvenResp g t 0 := by
  unfold poleEvenResp gammaCenteredTaper
  have h1 : Integrable
      (fun u : ℝ =>
        g u * Real.cos (r * u)
          * (Real.cosh (u / 2) * Real.cos (t * u) * Real.cos (0 * u))) := by
    exact
      ((hg.mul (by fun_prop)).mul (by fun_prop)).integrable_of_hasCompactSupport
        (hgc.mul_right.mul_right)
  have h0 : Integrable
      (fun u : ℝ =>
        g u
          * (Real.cosh (u / 2) * Real.cos (t * u) * Real.cos (0 * u))) := by
    exact
      (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  simp only [Real.cos_zero, mul_one]
  rw [show
      (fun u : ℝ =>
        g u * (Real.cos (r * u) - 1)
          * (Real.cosh (u / 2) * Real.cos (t * u)))
      =
      fun u : ℝ =>
        (g u * Real.cos (r * u))
          * (Real.cosh (u / 2) * Real.cos (t * u))
        -
        g u * (Real.cosh (u / 2) * Real.cos (t * u)) by
      funext u
      ring]
  rw [integral_sub]
  · unfold poleEvenResp
    simp only [Real.cos_zero, mul_one]
    congr 1 <;> funext u <;> ring
  · exact h1
  · exact h0

theorem evenCone_pole_centered_eq_radius_difference
    {g : ℝ -> ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t r : ℝ) :
    evenConeFunctional
      (poleVec (sampleFam (gammaCenteredTaper g r) t 0))
      =
    -4 * (poleEvenResp g t r - poleEvenResp g t 0) := by
  have hc :=
    gammaCenteredTaper_contDiff hgs r
  have hk :=
    gammaCenteredTaper_hasCompactSupport hgc r
  have he : ∀ u,
      gammaCenteredTaper g r (-u)
        = gammaCenteredTaper g r u := by
    intro u
    unfold gammaCenteredTaper
    rw [heven]
    simp [Real.cos_neg]
  rw [evenConeFunctional_poleVec_radiusZero
    hc.continuous hk he t]
  rw [poleEvenResp_gammaCenteredTaper_zero
    hgs.continuous hgc t r]

theorem evenCone_pole_centered_of_pole_killing
    {g : ℝ -> ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    {t r : ℝ}
    (hkill : poleEvenResp g t r = 0) :
    evenConeFunctional
      (poleVec (sampleFam (gammaCenteredTaper g r) t 0))
      =
    4 * poleEvenResp g t 0 := by
  rw [evenCone_pole_centered_eq_radius_difference
    hgs hgc heven t r, hkill]
  ring

/--
Exact final centered-complement reduction to the same-ordinate cluster and the
unweighted pole response of the original taper.
-/
theorem centeredLiteralComplement_eq_neg_cluster_minus_four_pole
    {g : ℝ -> ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hshortCentered :
      ∀ u, gammaCenteredTaper g r u ≠ 0 -> |u| < Real.log 2)
    {t r : ℝ}
    (hkill : poleEvenResp g t r = 0) :
    finalLiteralComplement (gammaCenteredTaper g r) t 0
      =
    - evenConeFunctional
        (clusterVec
          (sampleFam (gammaCenteredTaper g r) t 0) t)
      - 4 * poleEvenResp g t 0 := by
  have hc := gammaCenteredTaper_contDiff hgs r
  have hk := gammaCenteredTaper_hasCompactSupport hgc r
  have hbal :=
    radiusZero_literal_complement_with_pole
      hc hk hshortCentered t
  have hpole :=
    evenCone_pole_centered_of_pole_killing
      hgs hgc heven hkill
  rw [hpole] at hbal
  linarith

/--
Consumer-facing equivalence: proving the centered complement nonpositive is
exactly proving that the negative cluster does not exceed the positive
four-pole scale.
-/
theorem centeredLiteralComplement_nonpos_iff_clusterPole
    {g : ℝ -> ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hshortCentered :
      ∀ u, gammaCenteredTaper g r u ≠ 0 -> |u| < Real.log 2)
    {t r : ℝ}
    (hkill : poleEvenResp g t r = 0) :
    finalLiteralComplement (gammaCenteredTaper g r) t 0 <= 0
      ↔
    - evenConeFunctional
        (clusterVec
          (sampleFam (gammaCenteredTaper g r) t 0) t)
      <=
    4 * poleEvenResp g t 0 := by
  rw [centeredLiteralComplement_eq_neg_cluster_minus_four_pole
    hgs hgc heven hshortCentered hkill]
  constructor <;> intro h <;> linarith

end Synthesis
