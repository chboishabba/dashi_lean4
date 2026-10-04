import Synthesis.RiemannSelectedPrimeSensitiveThreeTapTwoPrime

/-!
# One-prime completed response of the physical translated four-window detector

The source-native Zeta23 even-cone arithmetic prime channel is explicit.
For t>=200, the physical width excludes n=3, so it is a SINGLE-prime
response with exact oscillatory factor cos(t log2), which can vanish.
The completed formula remains the SAME detector g_eps in every channel.

The projective determinant also uses the changed online profile of g_eps.
No claim of linearity of the projective margin in eps is made here.
-/

noncomputable section
namespace Synthesis
open scoped Real

/-- Symmetric sample-phase identity; the important t-dependence survives
the two signed radii of the even cone. -/
theorem threeTap_prime_cosine_pair (s t L : ℝ) :
    Real.cos ((s-t)*L) + Real.cos ((-s-t)*L)
      = 2 * Real.cos (s*L) * Real.cos (t*L) := by
  rw [show (s-t)*L=s*L-t*L by ring,
    show (-s-t)*L = -(s*L+t*L) by ring, Real.cos_neg]
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- The selected translated detector's actual Zeta23 prime EVEN CONE
has exactly one arithmetic frequency. In particular it is zero at
each sample radius whenever cos(t log2)=0, regardless of eps. -/
theorem quarticFourPhysicalDetector_threeTap_primeChannel_eq
    {R lam mu t eps : ℝ}
    (hR : 0 < R)
    (hRone : R < 1)
    (ht : 200 ≤ t)
    (s : ℝ) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeChannel
      (detectorThreeTap (quarticFourPhysicalDetector R lam mu t)
        eps (Real.log 2)) t s
      =
    4 * eps *
      (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
      * quarticFourPhysicalDetector R lam mu t 0
      * Real.cos (s*Real.log 2)
      * Real.cos (t*Real.log 2) := by
  let g := quarticFourPhysicalDetector R lam mu t
  have hsample (v : ℝ) :
      Zeta23Bridge.LiteralWeilParityBalance.primeTerm
        (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          (detectorThreeTap g eps (Real.log 2)) t v)
      =
      (((ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
          * (2*(eps*g 0)*Real.cos ((v-t)*Real.log 2))) : ℝ) :=
    quarticFourPhysicalDetector_threeTap_primeTerm_eq_first
      hR hRone ht
  change
    Zeta23Bridge.LiteralWeilParityBalance.reim
      (Zeta23Bridge.LiteralWeilParityBalance.primeTerm
        (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          (detectorThreeTap g eps (Real.log 2)) t s))
    +
    Zeta23Bridge.LiteralWeilParityBalance.reim
      (Zeta23Bridge.LiteralWeilParityBalance.primeTerm
        (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          (detectorThreeTap g eps (Real.log 2)) t (-s)))
    = _
  rw [hsample s, hsample (-s)]
  simp only [Zeta23Bridge.LiteralWeilParityBalance.reim,
    Complex.ofReal_re, Complex.ofReal_im, add_zero]
  rw [threeTap_prime_cosine_pair]
  dsimp [g]
  ring

theorem quarticFourPhysicalDetector_threeTap_primeChannel_eq_zero_at_resonance
    {R lam mu t eps : ℝ}
    (hR : 0 < R)
    (hRone : R < 1)
    (ht : 200 ≤ t)
    (hphase : Real.cos (t*Real.log 2)=0)
    (s : ℝ) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeChannel
      (detectorThreeTap (quarticFourPhysicalDetector R lam mu t)
        eps (Real.log 2)) t s = 0 := by
  rw [quarticFourPhysicalDetector_threeTap_primeChannel_eq hR hRone ht]
  rw [hphase]
  ring

/-- Actual projective prime determinant, with the transformed online
column still present, exactly as required by the completed formula. -/
theorem quarticFourPhysicalDetector_threeTap_primeProjectiveDefect_eq
    {R lam mu t eps r : ℝ}
    (hR : 0 < R)
    (hRone : R < 1)
    (ht : 200 ≤ t) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      (detectorThreeTap (quarticFourPhysicalDetector R lam mu t)
        eps (Real.log 2)) t r
      =
    (4*eps*(ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
        * quarticFourPhysicalDetector R lam mu t 0
        * Real.cos (t*Real.log 2))
      *
      (Real.cos (2*r*Real.log 2)
        * Zeta23Bridge.LiteralWeilParityBalance.evenResp
            (detectorThreeTap (quarticFourPhysicalDetector R lam mu t)
               eps (Real.log 2)) 0 r
      - Real.cos (r*Real.log 2)
        * Zeta23Bridge.LiteralWeilParityBalance.evenResp
            (detectorThreeTap (quarticFourPhysicalDetector R lam mu t)
              eps (Real.log 2)) 0 (2*r)) := by
  unfold Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.channelProjectiveDefect
  rw [quarticFourPhysicalDetector_threeTap_primeChannel_eq hR hRone ht,
    quarticFourPhysicalDetector_threeTap_primeChannel_eq hR hRone ht]
  ring

/-- Even the transformed PRIME PROJECTIVE channel vanishes at a phase
resonance; activating its source support alone is not an estimate. -/
theorem quarticFourPhysicalDetector_threeTap_primeProjectiveDefect_eq_zero_at_resonance
    {R lam mu t eps r : ℝ}
    (hR : 0 < R)
    (hRone : R < 1)
    (ht : 200 ≤ t)
    (hphase : Real.cos (t*Real.log 2)=0) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      (detectorThreeTap (quarticFourPhysicalDetector R lam mu t)
        eps (Real.log 2)) t r = 0 := by
  unfold Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.channelProjectiveDefect
  rw [quarticFourPhysicalDetector_threeTap_primeChannel_eq_zero_at_resonance
    hR hRone ht hphase,
    quarticFourPhysicalDetector_threeTap_primeChannel_eq_zero_at_resonance
    hR hRone ht hphase]
  ring

/-- Regularity and compact support of the EXACT transformed physical taper;
the two translation copies do not preserve the old support, but remain
compactly supported and C². -/
theorem detectorThreeTap_contDiff
    {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (eps L : ℝ) :
    ContDiff ℝ 2 (detectorThreeTap g eps L) := by
  unfold detectorThreeTap
  fun_prop

theorem detectorThreeTap_compact
    {g : ℝ → ℝ}
    (hg : HasCompactSupport g) (eps L : ℝ) :
    HasCompactSupport (detectorThreeTap g eps L) := by
  have hminus : HasCompactSupport (fun u : ℝ => g (u-L)) := by
    have heq : (fun u : ℝ => g (u-L))
        = g ∘ (Homeomorph.addRight (-L) : ℝ ≃ₜ ℝ) := by
      funext u
      simp [Function.comp_def, sub_eq_add_neg]
    rw [heq]
    exact hg.comp_homeomorph _
  have hplus : HasCompactSupport (fun u : ℝ => g (u+L)) := by
    have heq : (fun u : ℝ => g (u+L))
        = g ∘ (Homeomorph.addRight L : ℝ ≃ₜ ℝ) := by
      rfl
    rw [heq]
    exact hg.comp_homeomorph _
  exact (hg.add hminus.mul_left).add hplus.mul_left

/-- Completed four-channel source for each actual translated physical
detector; zero, gamma and pole channels are recomputed on g_eps,
not borrowed from the original g. -/
theorem quarticFourPhysicalDetector_threeTap_completedBalance
    {R lam mu t eps : ℝ}
    (hR : 0 < R)
    (hRone : R < 1)
    (ht : 200 ≤ t) (r : ℝ) :
    let gε := detectorThreeTap
      (quarticFourPhysicalDetector R lam mu t) eps (Real.log 2)
    Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect
        gε t r
      =
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
        gε t r
      +
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
        gε t r
      +
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
        gε t r
      +
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
        gε t r := by
  dsimp
  apply Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.clusterHeightDefect_eq_fourProjectiveChannels
  · exact detectorThreeTap_contDiff
      (quarticFourPhysicalDetector_contDiff hR) eps (Real.log 2)
  · exact detectorThreeTap_compact
      (quarticFourPhysicalDetector_compact hR (by linarith)) eps (Real.log 2)
  · exact detectorThreeTap_even
      (quarticFourPhysicalDetector_even R lam mu t) eps (Real.log 2)


/-!
## Genuine two-detector projective assembly on the SAME selected W

The two quartic physical detectors carry different shape parameters and
literal pole weights. The perturbation changes all four completed
channels. In particular the old pole cancellation theorem is NOT applied
to the translated detector without a new proof.
-/

def QuarticFourSignedPolePair.threeTapHalf
    {t : ℝ} (W : QuarticFourSignedPolePair t) (eps : ℝ) : ℝ → ℝ :=
  detectorThreeTap
    (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
    eps (Real.log 2)

def QuarticFourSignedPolePair.threeTapTwo
    {t : ℝ} (W : QuarticFourSignedPolePair t) (eps : ℝ) : ℝ → ℝ :=
  detectorThreeTap
    (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
    eps (Real.log 2)

def QuarticFourSignedPolePair.threeTapPrimeShape
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  Real.cos (2*r*Real.log 2)
    * Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 r
  - Real.cos (r*Real.log 2)
    * Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 (2*r)

def QuarticFourSignedPolePair.threeTapSignedPrimeCombination
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.poleTwo *
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      (W.threeTapHalf eps) t (t/16)
    -
  W.poleHalf *
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      (W.threeTapTwo eps) t (t/16)

/-- Exact actual POLE-WEIGHTED projective prime response.
Dependence on eps is not merely linear: its on-line column also changes. -/
theorem QuarticFourSignedPolePair.threeTapSignedPrimeCombination_eq
    {t eps : ℝ}
    (ht : 200 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSignedPrimeCombination eps
      =
    (4*eps*
      (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
      * Real.cos (t*Real.log 2))
      *
      (
        W.poleTwo
          * quarticFourPhysicalDetector W.R (1/2) W.muHalf t 0
          * W.threeTapPrimeShape (W.threeTapHalf eps) (t/16)
        -
        W.poleHalf
          * quarticFourPhysicalDetector W.R (2/3) W.muTwo t 0
          * W.threeTapPrimeShape (W.threeTapTwo eps) (t/16)
      ) := by
  unfold QuarticFourSignedPolePair.threeTapSignedPrimeCombination
    QuarticFourSignedPolePair.threeTapPrimeShape
    QuarticFourSignedPolePair.threeTapHalf
    QuarticFourSignedPolePair.threeTapTwo
  rw [quarticFourPhysicalDetector_threeTap_primeProjectiveDefect_eq
      W.Rpos W.RltOne ht,
      quarticFourPhysicalDetector_threeTap_primeProjectiveDefect_eq
      W.Rpos W.RltOne ht]
  ring

theorem QuarticFourSignedPolePair.threeTapSignedPrime_eq_zero_at_resonance
    {t eps : ℝ}
    (ht : 200 ≤ t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t*Real.log 2)=0) :
    W.threeTapSignedPrimeCombination eps = 0 := by
  rw [W.threeTapSignedPrimeCombination_eq ht, hphase]
  ring

theorem QuarticFourSignedPolePair.threeTapSignedPrime_eq_zero_at_zeroStrength
    {t : ℝ}
    (ht : 200 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSignedPrimeCombination 0 = 0 := by
  rw [W.threeTapSignedPrimeCombination_eq ht]
  ring

def QuarticFourSignedPolePair.threeTapChannelCombination
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ)
    (C : (ℝ → ℝ) → ℝ → ℝ → ℝ) : ℝ :=
  W.poleTwo*(C (W.threeTapHalf eps) t (t/16))
    - W.poleHalf*(C (W.threeTapTwo eps) t (t/16))

def QuarticFourSignedPolePair.threeTapCompletedArithmetic
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapSignedPrimeCombination eps
    + W.threeTapChannelCombination eps
        Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
    + W.threeTapChannelCombination eps
        Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect

/-- Exact transformed Zeta23 completed formula: recompute all channels
on the shifted detector. -/
theorem QuarticFourSignedPolePair.threeTapCompletedCluster_eq_off_add_arithmetic
    {t eps : ℝ}
    (ht : 200 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapChannelCombination eps
        Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect
      =
    W.threeTapChannelCombination eps
        Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
      + W.threeTapCompletedArithmetic eps := by
  have hhalf :=
    quarticFourPhysicalDetector_threeTap_completedBalance
      (R := W.R) (lam := (1/2)) (mu := W.muHalf)
      (t := t) (eps := eps) W.Rpos W.RltOne ht (t/16)
  have htwo :=
    quarticFourPhysicalDetector_threeTap_completedBalance
      (R := W.R) (lam := (2/3)) (mu := W.muTwo)
      (t := t) (eps := eps) W.Rpos W.RltOne ht (t/16)
  dsimp [QuarticFourSignedPolePair.threeTapChannelCombination,
    QuarticFourSignedPolePair.threeTapCompletedArithmetic,
    QuarticFourSignedPolePair.threeTapSignedPrimeCombination,
    QuarticFourSignedPolePair.threeTapHalf,
    QuarticFourSignedPolePair.threeTapTwo] at *
  rw [hhalf,htwo]
  ring

/-- The new prime response balances the simultaneously changed zero,
Gamma, pole and on-line responses. Source activation alone proves no
positive completed margin. -/
theorem QuarticFourSignedPolePair.threeTap_completed_prime_not_independent
    {t eps : ℝ}
    (ht : 200 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSignedPrimeCombination eps
      =
    W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect
    - W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
    - W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
    - W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect := by
  have h := W.threeTapCompletedCluster_eq_off_add_arithmetic ht
  unfold QuarticFourSignedPolePair.threeTapCompletedArithmetic at h
  linarith


/-!
## Actual physical origin: both endpoint detectors have the same centre

For 0<R<1 the three noncentral bumps centered at pi/3, pi/2, pi
are disjoint from the origin; the central symmetrized unit bump equals 2.
The normalized source thus has g(0)=2/m_R >0 independently of lambda,mu,t.
-/

private theorem fourWindow_noncentral_bump_zero
    {R c : ℝ} (hR : 0 < R) (hc : R ≤ c) :
    quantitativeSymBump c R 0 = 0 := by
  have hscaled : scaledUnitBump c R 0 = 0 := by
    by_contra hne
    have hs := scaledUnitBump_support hR hne
    have hc0 : 0 ≤ c := hR.le.trans hc
    simp only [zero_sub, abs_neg, abs_of_nonneg hc0] at hs
    linarith
  change scaledUnitBump c R 0 + scaledUnitBump c R (-0) = 0
  simp [hscaled]

theorem quarticFourPhysicalDetector_centre_eq
    {R lam mu t : ℝ}
    (hR : 0 < R) (hRone : R < 1) :
    quarticFourPhysicalDetector R lam mu t 0
      = 2 * (quarticWindowMass R)⁻¹ := by
  have hp : (3:ℝ) < Real.pi := Real.pi_gt_three
  have h1 : R ≤ Real.pi/3 := by linarith
  have h2 : R ≤ Real.pi/2 := by linarith
  have h3 : R ≤ Real.pi := by linarith
  have hb0 : quantitativeSymBump 0 R 0 = 2 := by
    change scaledUnitBump 0 R 0 + scaledUnitBump 0 R (-0) = 2
    rw [scaledUnitBump_at_center hR.ne']
    simp [scaledUnitBump_at_center hR.ne']
  have hb1 := fourWindow_noncentral_bump_zero hR h1
  have hb2 := fourWindow_noncentral_bump_zero hR h2
  have hb3 := fourWindow_noncentral_bump_zero hR h3
  unfold quarticFourPhysicalDetector projectiveRescaleProfile
    quarticFourWindowProfile quarticFourWindowRaw
  simp [hb0, hb1, hb2, hb3]
  ring

theorem quarticFourPhysicalDetector_centre_pos
    {R lam mu t : ℝ}
    (hR : 0 < R) (hRone : R < 1) :
    0 < quarticFourPhysicalDetector R lam mu t 0 := by
  rw [quarticFourPhysicalDetector_centre_eq hR hRone]
  exact mul_pos (by norm_num) (inv_pos.mpr (quarticWindowMass_pos hR))

theorem QuarticFourSignedPolePair.threeTapSignedPrimeCombination_eq_commonCentre
    {t eps : ℝ}
    (ht : 200 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSignedPrimeCombination eps
      =
    (8*eps*(ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
      * (quarticWindowMass W.R)⁻¹
      * Real.cos (t*Real.log 2))
      *
      (
        W.poleTwo * W.threeTapPrimeShape (W.threeTapHalf eps) (t/16)
        -
        W.poleHalf * W.threeTapPrimeShape (W.threeTapTwo eps) (t/16)
      ) := by
  rw [W.threeTapSignedPrimeCombination_eq ht,
    quarticFourPhysicalDetector_centre_eq W.Rpos W.RltOne,
    quarticFourPhysicalDetector_centre_eq W.Rpos W.RltOne]
  ring

/-- The literal first prime sample is actually nonzero when eps is nonzero,
though the completed even cone can still vanish at phase resonance. -/
theorem quarticFourPhysicalDetector_threeTap_firstPrime_nonzero
    {R lam mu t eps : ℝ}
    (hR : 0 < R) (hRone : R < 1) (ht : 200 ≤ t)
    (heps : eps ≠ 0) :
    detectorThreeTap
      (quarticFourPhysicalDetector R lam mu t)
      eps (Real.log 2) (Real.log 2) ≠ 0 := by
  rw [quarticFourPhysicalDetector_threeTap_firstPrime hR hRone ht]
  exact mul_ne_zero heps
    (ne_of_gt (quarticFourPhysicalDetector_centre_pos hR hRone))

end Synthesis
