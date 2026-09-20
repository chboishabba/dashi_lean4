import Synthesis.RiemannCenteredOffCanonicalHighUpper
import Synthesis.RiemannFinalLiteralComplementCenteredExact

/-!
# Canonical high-ordinate reduction for the centered literal complement

For the actual final literal complement at the centered taper

  h_r(u) = g(u) (cos(r u) - 1),

the finite near reflection-pair core is nonpositive on the canonical signed
window.  Therefore the only positive Off contribution is the explicit far
remainder already bounded by `centeredOffHighEnvelope`.

This file pushes that one-sided Off theorem through the *literal signed
complement* rather than taking separate absolute channel budgets.  It exposes
the remaining centered-sign leaf as one Gamma-vs-far inequality:

  GammaCone(h_r,t,0) <= - centeredOffHighEnvelope
  -------------------------------------------------
              S_{h_r}(t,0) <= 0.

No projective balance and no final explicit-formula balance are used.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

theorem exists_centeredLiteralComplement_canonicalHigh_upper
    {g : ℝ → ℝ} {Lambda t r : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hnn : ∀ u, 0 <= g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| <= Lambda)
    (hLambda : 0 <= Lambda)
    (ht : 18 <= |t|)
    (hcanonical : Lambda <= 9 * Real.pi / (4 * |t|)) :
    ∃ A : ℝ, 1 <= A ∧
      finalLiteralComplement (gammaCenteredTaper g r) t 0
        <=
      centeredOffHighEnvelope A g Lambda r t
        + evenConeFunctional
            (gammaVec (sampleFam (gammaCenteredTaper g r) t 0)) := by
  obtain ⟨A, hA, hOff⟩ :=
    exists_centeredOff_canonicalHigh_upper
      hgs hgc heven hnn hsupp hLambda ht hcanonical
      (r := r)
  refine ⟨A, hA, ?_⟩
  unfold finalLiteralComplement
  linarith

theorem centeredLiteralComplement_nonpos_of_gamma_le_neg_far
    {g : ℝ → ℝ} {Lambda t r A : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hnn : ∀ u, 0 <= g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| <= Lambda)
    (hLambda : 0 <= Lambda)
    (ht : 18 <= |t|)
    (hcanonical : Lambda <= 9 * Real.pi / (4 * |t|))
    (hA : 1 <= A)
    (hOff :
      evenConeFunctional
          (offOrdVec (sampleFam (gammaCenteredTaper g r) t 0) t)
        <= centeredOffHighEnvelope A g Lambda r t)
    (hGamma :
      evenConeFunctional
          (gammaVec (sampleFam (gammaCenteredTaper g r) t 0))
        <= - centeredOffHighEnvelope A g Lambda r t) :
    finalLiteralComplement (gammaCenteredTaper g r) t 0 <= 0 := by
  unfold finalLiteralComplement
  linarith

theorem exists_centeredLiteralComplement_sign_reduction
    {g : ℝ → ℝ} {Lambda t r : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hnn : ∀ u, 0 <= g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| <= Lambda)
    (hLambda : 0 <= Lambda)
    (ht : 18 <= |t|)
    (hcanonical : Lambda <= 9 * Real.pi / (4 * |t|)) :
    ∃ A : ℝ, 1 <= A ∧
      (evenConeFunctional
          (gammaVec (sampleFam (gammaCenteredTaper g r) t 0))
        <= - centeredOffHighEnvelope A g Lambda r t
       →
       finalLiteralComplement (gammaCenteredTaper g r) t 0 <= 0) := by
  obtain ⟨A, hA, hJoint⟩ :=
    exists_centeredLiteralComplement_canonicalHigh_upper
      hgs hgc heven hnn hsupp hLambda ht hcanonical
      (r := r)
  refine ⟨A, hA, ?_⟩
  intro hGamma
  linarith

end Synthesis
