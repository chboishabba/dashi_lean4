import Synthesis.RiemannSelectedPrimeSensitiveTwoScale

/-!
# RH P0: the original two-prime Weil source on a frozen-online aperture carrier

The selected four-window source is short of log 2 and therefore prime-blind.
The already source-checked TwoScale file proves the literal prime-2/prime-3
weights and the full four-channel balance, but its shifted profile changes
the on-line projective column (quadratic in amplitudes).

This module isolates the exact *conditional* carrier needed by the
eight-invariant projection: a replacement even smooth physical detector
for each endpoint, with the SAME two on-line responses, SAME signed even
moments through 8, and SAME original pole response. Unlike TwoScale, its
projective prime term is linear in its independently controlled *point*
values at log 2 and log 3.

This file does NOT prove that the carrier is inhabited by a smooth projected
aperture. That finite-codimension construction, quantitative absolute
derivative bounds and the independent RH strict estimate are separate P0
obligations. No RH/GRH assertion is made.
-/

noncomputable section

namespace Synthesis

open MeasureTheory
open scoped Real

/-- The exact contribution of each genuine prime in the even cone.
The factor FOUR is essential: the single sample has factor 2 and the
two ±s sampling radii provide another factor 2. -/
theorem primeAperture_literalPrimeSummand_zero_of_four_le
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (hfar : ∀ n : ℕ, 4 ≤ n → g (Real.log n) = 0)
    (t s : ℝ) (n : ℕ) (hn : 4 ≤ n) :
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          g t s (Real.log n)
        + Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          g t s (-Real.log n)) = 0 := by
  have hp := hfar n hn
  have hm : g (-Real.log n) = 0 := by
    rw [heven (Real.log n)]
    exact hp
  simp [Zeta23Bridge.LiteralWeilParityBalance.sampleTest, hp, hm]

theorem primeAperture_primeTerm_eq_two_summands
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (hfar : ∀ n : ℕ, 4 ≤ n → g (Real.log n) = 0)
    (t s : ℝ) :
    Zeta23Bridge.LiteralWeilParityBalance.primeTerm
      (Zeta23Bridge.LiteralWeilParityBalance.sampleTest g t s) =
    ∑ n ∈ ({2,3} : Finset ℕ),
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
        * (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
            g t s (Real.log n)
          + Zeta23Bridge.LiteralWeilParityBalance.sampleTest
            g t s (-Real.log n)) := by
  unfold Zeta23Bridge.LiteralWeilParityBalance.primeTerm
  apply tsum_eq_sum
  intro n hn
  have hne2 : n ≠ 2 := by
    intro h
    exact hn (by simp [h])
  have hne3 : n ≠ 3 := by
    intro h
    exact hn (by simp [h])
  by_cases h4 : 4 ≤ n
  · exact primeAperture_literalPrimeSummand_zero_of_four_le
      heven hfar t s n h4
  · have hn4 : n < 4 := Nat.lt_of_not_ge h4
    interval_cases n <;>
      simp [hne2, hne3, ArithmeticFunction.vonMangoldt]

/-- Exact Zeta23 prime term for an arbitrary original-compatible even
two-port aperture; it is not a hand-written replacement arithmetic sum. -/
theorem primeAperture_primeTerm_eq_two_real_terms
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (hfar : ∀ n : ℕ, 4 ≤ n → g (Real.log n) = 0)
    (t s : ℝ) :
    Zeta23Bridge.LiteralWeilParityBalance.primeTerm
      (Zeta23Bridge.LiteralWeilParityBalance.sampleTest g t s) =
    (((2 : ℝ) *
      ((ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
         * g (Real.log 2) * Real.cos ((s-t)*Real.log 2)
       + (ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
         * g (Real.log 3) * Real.cos ((s-t)*Real.log 3))) : ℝ) := by
  rw [primeAperture_primeTerm_eq_two_summands heven hfar t s]
  simp only [Finset.sum_insert (by simp : (2:ℕ) ∉ ({3}:Finset ℕ)),
    Finset.sum_singleton]
  rw [Zeta23Bridge.LiteralWeilPrimeEvenCone.primeSummand_sampleTest
      heven t s 2,
    Zeta23Bridge.LiteralWeilPrimeEvenCone.primeSummand_sampleTest
      heven t s 3]
  push_cast
  ring

/-- EXACT prime-2/prime-3 even channel. In particular the output is not
an arbitrary sign: both original t-phases are retained. -/
theorem primeAperture_primeChannel_eq
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (hfar : ∀ n : ℕ, 4 ≤ n → g (Real.log n) = 0)
    (t s : ℝ) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeChannel
      g t s =
    4 * (
      (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
        * g (Real.log 2) * Real.cos (s*Real.log 2)
        * Real.cos (t*Real.log 2)
      + (ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
        * g (Real.log 3) * Real.cos (s*Real.log 3)
        * Real.cos (t*Real.log 3)) := by
  change
    Zeta23Bridge.LiteralWeilParityBalance.reim
      (Zeta23Bridge.LiteralWeilParityBalance.primeTerm
        (Zeta23Bridge.LiteralWeilParityBalance.sampleTest g t s))
    +
    Zeta23Bridge.LiteralWeilParityBalance.reim
      (Zeta23Bridge.LiteralWeilParityBalance.primeTerm
        (Zeta23Bridge.LiteralWeilParityBalance.sampleTest g t (-s))) = _
  rw [primeAperture_primeTerm_eq_two_real_terms heven hfar t s,
      primeAperture_primeTerm_eq_two_real_terms heven hfar t (-s)]
  simp only [Zeta23Bridge.LiteralWeilParityBalance.reim,
    Complex.ofReal_re, Complex.ofReal_im, add_zero]
  calc
    _ =
      (2 : ℝ) *
        ((ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
          * g (Real.log 2) *
          (Real.cos ((s-t)*Real.log 2)
            + Real.cos ((-s-t)*Real.log 2))
         + (ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
          * g (Real.log 3) *
          (Real.cos ((s-t)*Real.log 3)
            + Real.cos ((-s-t)*Real.log 3))) := by ring
    _ = _ := by
      rw [threeTap_prime_cosine_pair s t (Real.log 2),
          threeTap_prime_cosine_pair s t (Real.log 3)]
      ring

/-- Literal projective prime source. The two online responses must be
sampled on the SAME detector (not a replacement normalized fixture). -/
theorem primeAperture_primeProjective_eq
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (hfar : ∀ n : ℕ, 4 ≤ n → g (Real.log n) = 0)
    (t r : ℝ) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      g t r =
    4 * (
      (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
        * g (Real.log 2) * Real.cos (t*Real.log 2)
        * twoScalePrimeShape g r (Real.log 2)
      + (ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
        * g (Real.log 3) * Real.cos (t*Real.log 3)
        * twoScalePrimeShape g r (Real.log 3)) := by
  unfold Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.channelProjectiveDefect
    twoScalePrimeShape
  rw [primeAperture_primeChannel_eq heven hfar t (2*r),
      primeAperture_primeChannel_eq heven hfar t r]
  ring

/-- The original four-window *atomic* Fourier-response determinant.
This is used only as a source-local small-R nondegeneracy seed; the
small-R transfer for the smooth selected witness is a separate theorem. -/
def quarticFourPrimeApertureAtomicResponseDet
    (muHalf muTwo : ℝ) : ℝ :=
  ((1/2 : ℝ) - muHalf) * ((5/6 : ℝ) + muTwo)
    - ((1 : ℝ) + muHalf) * ((1/2 : ℝ) - muTwo)

theorem quarticFourPrimeApertureAtomicResponseDet_eq
    (muHalf muTwo : ℝ) :
    quarticFourPrimeApertureAtomicResponseDet muHalf muTwo
      = -(1/12 : ℝ) - (4/3 : ℝ)*muHalf + (3/2 : ℝ)*muTwo := by
  unfold quarticFourPrimeApertureAtomicResponseDet
  ring

/-- Exact source corridor: the two atomic endpoint on-line vectors are
nonproportional throughout the FULL original mu corridors. -/
theorem quarticFourPrimeApertureAtomicResponseDet_neg
    {muHalf muTwo : ℝ}
    (hHalf :
      |muHalf - quarticFourAtomicMu (1/2)| <=
        quarticFourAtomicMuRadius)
    (hTwo :
      |muTwo - quarticFourAtomicMu (2/3)| <=
        quarticFourAtomicMuRadius) :
    quarticFourPrimeApertureAtomicResponseDet muHalf muTwo < 0 := by
  have hmuHalf : quarticFourAtomicMu (1/2) = -(1/78 : ℝ) := by
    norm_num [quarticFourAtomicMu]
  have hmuTwo : quarticFourAtomicMu (2/3) = (1/162 : ℝ) := by
    norm_num [quarticFourAtomicMu]
  rw [hmuHalf] at hHalf
  rw [hmuTwo] at hTwo
  unfold quarticFourAtomicMuRadius at hHalf hTwo
  obtain ⟨hHL, hHU⟩ := abs_le.mp hHalf
  obtain ⟨hTL, hTU⟩ := abs_le.mp hTwo
  rw [quarticFourPrimeApertureAtomicResponseDet_eq]
  linarith

/-- The actual physical projective moment, not a stand-in atomic moment. -/
def primeAperturePhysicalMoment
    (g : ℝ → ℝ) (r : ℝ) (k : ℕ) : ℝ :=
  ∫ u : ℝ,
    (4*g u *
      (Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 r
         * Real.cos (2*r*u)
       - Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 (2*r)
         * Real.cos (r*u))) * u^k

/-- P0 E0 carrier: exactly which source facts the finite-codimension
projection must produce. Inhabitation is NOT claimed here. -/
structure QuarticFourFrozenPrimeAperture (t : ℝ) where
  W : QuarticFourSignedPolePair t
  half : ℝ → ℝ
  two : ℝ → ℝ
  halfSmooth : ContDiff ℝ 2 half
  twoSmooth : ContDiff ℝ 2 two
  halfCompact : HasCompactSupport half
  twoCompact : HasCompactSupport two
  halfEven : ∀ u, half (-u) = half u
  twoEven : ∀ u, two (-u) = two u
  halfPrimeTail : ∀ n : ℕ, 4 ≤ n → half (Real.log n) = 0
  twoPrimeTail : ∀ n : ℕ, 4 ≤ n → two (Real.log n) = 0
  halfResp1 :
    Zeta23Bridge.LiteralWeilParityBalance.evenResp half 0 (t/16) =
    Zeta23Bridge.LiteralWeilParityBalance.evenResp
      (quarticFourPhysicalDetector W.R (1/2) W.muHalf t) 0 (t/16)
  halfResp2 :
    Zeta23Bridge.LiteralWeilParityBalance.evenResp half 0 (2*(t/16)) =
    Zeta23Bridge.LiteralWeilParityBalance.evenResp
      (quarticFourPhysicalDetector W.R (1/2) W.muHalf t) 0 (2*(t/16))
  twoResp1 :
    Zeta23Bridge.LiteralWeilParityBalance.evenResp two 0 (t/16) =
    Zeta23Bridge.LiteralWeilParityBalance.evenResp
      (quarticFourPhysicalDetector W.R (2/3) W.muTwo t) 0 (t/16)
  twoResp2 :
    Zeta23Bridge.LiteralWeilParityBalance.evenResp two 0 (2*(t/16)) =
    Zeta23Bridge.LiteralWeilParityBalance.evenResp
      (quarticFourPhysicalDetector W.R (2/3) W.muTwo t) 0 (2*(t/16))
  halfMoments :
    ∀ k : ℕ, (k=2 ∨ k=4 ∨ k=6 ∨ k=8) →
      primeAperturePhysicalMoment half (t/16) k =
      primeAperturePhysicalMoment
        (quarticFourPhysicalDetector W.R (1/2) W.muHalf t) (t/16) k
  twoMoments :
    ∀ k : ℕ, (k=2 ∨ k=4 ∨ k=6 ∨ k=8) →
      primeAperturePhysicalMoment two (t/16) k =
      primeAperturePhysicalMoment
        (quarticFourPhysicalDetector W.R (2/3) W.muTwo t) (t/16) k
  halfPole :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
      half t (t/16) =
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
      (quarticFourPhysicalDetector W.R (1/2) W.muHalf t) t (t/16)
  twoPole :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
      two t (t/16) =
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
      (quarticFourPhysicalDetector W.R (2/3) W.muTwo t) t (t/16)

/-- Reuse the original signed-pole coefficients. The source of EVERY channel
below is the SAME pair of extended detectors. -/
def QuarticFourFrozenPrimeAperture.channel
    {t : ℝ} (A : QuarticFourFrozenPrimeAperture t)
    (C : (ℝ → ℝ) → ℝ → ℝ → ℝ) : ℝ :=
  A.W.poleTwo * C A.half t (t/16)
    - A.W.poleHalf * C A.two t (t/16)

/-- Frozen original pole weights still cancel *exactly*, without assuming
the extended detectors satisfy the old short-support theorem. -/
theorem QuarticFourFrozenPrimeAperture.poleChannel_zero
    {t : ℝ} (ht : 0 < t)
    (A : QuarticFourFrozenPrimeAperture t) :
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
      = 0 := by
  unfold QuarticFourFrozenPrimeAperture.channel
  rw [A.halfPole, A.twoPole]
  convert A.W.literalPole_cancel ht using 1 <;> ring

/-- The source-exact signed two-prime term, with no eps² projective error
because both original on-line Fourier responses are frozen. -/
theorem QuarticFourFrozenPrimeAperture.signedPrime_eq_frozen
    {t : ℝ} (A : QuarticFourFrozenPrimeAperture t) :
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
    =
    4 * (
      (ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
        * Real.cos (t*Real.log 2)
        * (A.W.poleTwo * A.half (Real.log 2)
             * twoScalePrimeShape
                 (quarticFourPhysicalDetector A.W.R (1/2) A.W.muHalf t)
                 (t/16) (Real.log 2)
           - A.W.poleHalf * A.two (Real.log 2)
             * twoScalePrimeShape
                 (quarticFourPhysicalDetector A.W.R (2/3) A.W.muTwo t)
                 (t/16) (Real.log 2))
      + (ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
        * Real.cos (t*Real.log 3)
        * (A.W.poleTwo * A.half (Real.log 3)
             * twoScalePrimeShape
                 (quarticFourPhysicalDetector A.W.R (1/2) A.W.muHalf t)
                 (t/16) (Real.log 3)
           - A.W.poleHalf * A.two (Real.log 3)
             * twoScalePrimeShape
                 (quarticFourPhysicalDetector A.W.R (2/3) A.W.muTwo t)
                 (t/16) (Real.log 3))) := by
  unfold QuarticFourFrozenPrimeAperture.channel
  rw [primeAperture_primeProjective_eq A.halfEven A.halfPrimeTail t (t/16),
      primeAperture_primeProjective_eq A.twoEven A.twoPrimeTail t (t/16)]
  unfold twoScalePrimeShape
  rw [A.halfResp1, A.halfResp2, A.twoResp1, A.twoResp2]
  ring

/-- The full ORIGINAL Zeta23 four-channel explicit formula transports to
the extended pair, while the prime term is now explicitly present. This
is only a completed SOURCE IDENTITY, not the missing independent strict
upper estimate. -/
theorem QuarticFourFrozenPrimeAperture.completedCluster_eq_fourChannels
    {t : ℝ} (A : QuarticFourFrozenPrimeAperture t) :
    A.channel
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect
      =
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
      +
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      +
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
      +
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect := by
  have hhalf :=
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.clusterHeightDefect_eq_fourProjectiveChannels
      A.halfSmooth A.halfCompact A.halfEven t (t/16)
  have htwo :=
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.clusterHeightDefect_eq_fourProjectiveChannels
      A.twoSmooth A.twoCompact A.twoEven t (t/16)
  unfold QuarticFourFrozenPrimeAperture.channel
  rw [hhalf, htwo]
  ring

theorem QuarticFourFrozenPrimeAperture.completedCluster_eq_off_prime_gamma
    {t : ℝ} (ht : 0 < t) (A : QuarticFourFrozenPrimeAperture t) :
    A.channel
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect
      =
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
      +
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      +
    A.channel
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect := by
  have hs := A.completedCluster_eq_fourChannels
  have hp := A.poleChannel_zero ht
  linarith

end Synthesis
