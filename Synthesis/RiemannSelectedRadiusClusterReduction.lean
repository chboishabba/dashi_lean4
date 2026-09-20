import Synthesis.RiemannFinalLiteralComplementSignedReduction
import Synthesis.RiemannQuantitativeCanonicalTaper
import Synthesis.RiemannCanonicalCenteredClusterPoleReduction
import Synthesis.RiemannCanonicalTaperRadiusZeroPoleSign
import Zeta23Bridge.LiteralWeilPrimeEvenCone

/-!
# Selected-radius pole annihilation and direct cluster reduction

The older radius-zero reduction retained a pole correction because the canonical
taper is constructed to kill the pole at the selected sample radius r, not at
r=0.

For an even taper g, however, the final even-cone functional annihilates the
odd pole pattern at every radius.  Hence

  ell(poleVec(sampleFam g t r)) = -4 * poleEvenResp g t r.

Therefore any pole-killing radius makes the complete pole channel vanish under
the exact consumer.  If the taper is also short enough to kill the prime
channel, the literal explicit formula gives the exact selected-radius identity

  finalLiteralComplement g t r
    = - ell(clusterVec(sampleFam g t r,t)).

This removes Gamma/RvM bookkeeping entirely from the sign reduction at the
selected radius.  The only remaining analytic sign input is positivity of the
same-ordinate cluster.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilPrimeEvenCone

theorem evenConeFunctional_poleVec
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t r : ℝ) :
    evenConeFunctional (poleVec (sampleFam g t r))
      = -4 * poleEvenResp g t r := by
  rw [poleVec_sampleFam hg hgc heven t r]
  rw [map_smul]
  simp only [smul_eq_mul, poleParityVec,
    evenConeFunctional_oddPattern,
    evenConeFunctional_evenPattern]
  ring

theorem evenConeFunctional_poleVec_eq_zero_of_poleEven_zero
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    {t r : ℝ}
    (hkill : poleEvenResp g t r = 0) :
    evenConeFunctional (poleVec (sampleFam g t r)) = 0 := by
  rw [evenConeFunctional_poleVec hg hgc heven t r, hkill]
  ring

/--
Exact selected-radius reduction.  Prime invisibility plus pole annihilation
turns the signed literal complement into minus the same-ordinate cluster.
-/
theorem selectedRadius_literalComplement_eq_neg_cluster
    {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2)
    {t r : ℝ}
    (hkill : poleEvenResp g t r = 0) :
    finalLiteralComplement g t r
      =
    - evenConeFunctional
        (clusterVec (sampleFam g t r) t) := by
  have hprime : primeVec (sampleFam g t r) = 0 :=
    primeVec_eq_zero_of_short_taper hshort t r
  have hpole :
      evenConeFunctional (poleVec (sampleFam g t r)) = 0 :=
    evenConeFunctional_poleVec_eq_zero_of_poleEven_zero
      hgs.continuous hgc heven hkill
  have hkd := fun i => sampleFam_contDiff hgs t r i
  have hkc := fun i => sampleFam_hasCompactSupport hgc t r i
  have hbal := literalWeilOrdinateFibreBalance hkd hkc t
  have hlin :
      evenConeFunctional (clusterVec (sampleFam g t r) t)
        + evenConeFunctional (offOrdVec (sampleFam g t r) t)
        + evenConeFunctional (primeVec (sampleFam g t r))
        + evenConeFunctional (gammaVec (sampleFam g t r))
        + evenConeFunctional (poleVec (sampleFam g t r)) = 0 := by
    rw [← map_add, ← map_add, ← map_add, ← map_add, hbal, map_zero]
  rw [hprime, map_zero, add_zero, hpole, add_zero] at hlin
  unfold finalLiteralComplement
  linarith

theorem selectedRadius_literalComplement_lt_zero_of_cluster_pos
    {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2)
    {t r : ℝ}
    (hkill : poleEvenResp g t r = 0)
    (hcluster :
      0 <
      evenConeFunctional
        (clusterVec (sampleFam g t r) t)) :
    finalLiteralComplement g t r < 0 := by
  rw [selectedRadius_literalComplement_eq_neg_cluster
    hgs hgc heven hshort hkill]
  linarith

/--
The literal quantitative canonical taper is itself prime-invisible once the
high-height support criterion is met.
-/
theorem quantitativeCanonicalTaper_short
    {t : ℝ}
    (ht : 18 <= t)
    (hheight : 9 * Real.pi <= 4 * t * Real.log 2) :
    ∀ u, quantitativeCanonicalTaper t u ≠ 0 -> |u| < Real.log 2 := by
  intro u hu
  have ht0 : 0 < t := by linarith
  have hs := quantitativeCanonicalTaper_support_abs_lt ht hu
  have hupper :
      9 * Real.pi / (4 * t) <= Real.log 2 := by
    rw [div_le_iff₀ (by positivity : 0 < 4 * t)]
    exact hheight
  exact lt_of_lt_of_le hs hupper

/--
Fully instantiated selected-radius identity for the actual quantitative
canonical taper.  All prime/pole/support plumbing is discharged.
-/
theorem quantitativeCanonical_selectedRadius_complement_eq_neg_cluster
    {t : ℝ}
    (ht : 18 <= t)
    (hheight : 9 * Real.pi <= 4 * t * Real.log 2) :
    finalLiteralComplement
        (quantitativeCanonicalTaper t)
        t
        (quantitativeSampleRadius t)
      =
    - evenConeFunctional
        (clusterVec
          (sampleFam
            (quantitativeCanonicalTaper t)
            t
            (quantitativeSampleRadius t))
          t) := by
  exact selectedRadius_literalComplement_eq_neg_cluster
    (quantitativeCanonicalTaper_contDiff ht)
    (quantitativeCanonicalTaper_compact ht)
    (quantitativeCanonicalTaper_even (t := t))
    (quantitativeCanonicalTaper_short ht hheight)
    (quantitativeCanonicalTaper_pole_zero ht)

/--
Canonical terminal sign compiler: after the exact selected-radius reduction,
strict negativity is equivalent to the single same-ordinate cluster positivity
leaf.
-/
theorem quantitativeCanonical_selectedRadius_complement_neg_of_cluster_pos
    {t : ℝ}
    (ht : 18 <= t)
    (hheight : 9 * Real.pi <= 4 * t * Real.log 2)
    (hcluster :
      0 <
      evenConeFunctional
        (clusterVec
          (sampleFam
            (quantitativeCanonicalTaper t)
            t
            (quantitativeSampleRadius t))
          t)) :
    finalLiteralComplement
        (quantitativeCanonicalTaper t)
        t
        (quantitativeSampleRadius t) < 0 := by
  rw [quantitativeCanonical_selectedRadius_complement_eq_neg_cluster
    ht hheight]
  linarith


/--
Existential high-side closure on the already-proved positive pole-killing taper
family.

For an actual zero rhoStar at ordinate t, sufficiently large |t| makes the
constructor's support prime-invisible.  The same-ordinate cluster is strictly
positive by the literal Zeta23 cone theorem, while the selected pole channel is
zero by construction.  Hence the literal complement is strictly negative.
-/
theorem exists_selectedRadius_literalComplement_neg_at_zero
    {rhoStar : Zeta23.Zeros} {t : ℝ}
    (him : (rhoStar : ℂ).im = t)
    (ht : t ≠ 0)
    (hhigh : 9 * Real.pi < 4 * |t| * Real.log 2) :
    ∃ (g : ℝ → ℝ) (r : ℝ),
      ContDiff ℝ 2 g
      ∧ HasCompactSupport g
      ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r
      ∧ poleEvenResp g t r = 0
      ∧ (∀ a : ℝ, 0 < evenResp g a r)
      ∧ finalLiteralComplement g t r < 0 := by
  obtain ⟨g, r, hgs, hgc, heven, hr, hnn, hrad,
      hkill, hpole0, hpoleVec0, hA, hsupp⟩ :=
    exists_canonical_taper_with_negative_radiusZero_pole ht
  have habst0 : 0 < |t| := abs_pos.mpr ht
  have hshort : ∀ u, g u ≠ 0 -> |u| < Real.log 2 := by
    intro u hu
    have hs := hsupp u hu
    have hupper : 9 * Real.pi / (4 * |t|) < Real.log 2 := by
      rw [div_lt_iff₀ (by positivity : 0 < 4 * |t|)]
      exact hhigh
    exact lt_trans hs hupper
  have hcluster :
      0 <
      evenConeFunctional
        (clusterVec (sampleFam g t r) t) := by
    exact sameOrdinateClusterConePositive
      hgs hgc heven hA ⟨rhoStar, him⟩
  have hneg :
      finalLiteralComplement g t r < 0 :=
    selectedRadius_literalComplement_lt_zero_of_cluster_pos
      hgs hgc heven hshort hkill hcluster
  exact ⟨g, r, hgs, hgc, heven, hr, hkill, hA, hneg⟩


end Synthesis
