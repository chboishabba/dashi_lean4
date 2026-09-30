import Synthesis.RiemannSelectedPrimeSensitiveThreeTapCompleted

/-!
# Two independent arithmetic shifts on the actual high four-window source

At t>=300, |supp g| < 16*(pi+1)/t < 1/4.
The inequalities log(3/2) >= 1/3 and log(4/3) >= 1/4
then prove exact frequency isolation:

   g + e2*(tau_{±log2} g) + e3*(tau_{±log3} g)

has, among von-Mangoldt frequencies n>=2, ONLY
   n=2: e2*g(0),
   n=3: e3*g(0),
   n>=4: zero.

The distinct coefficients arise from two distinct physical translations.
No sign or RH-terminal margin is inferred by the support argument alone.
-/

noncomputable section
namespace Synthesis
open scoped Real

def detectorTwoScale
    (g : ℝ → ℝ) (e2 e3 : ℝ) (u : ℝ) : ℝ :=
  g u
    + e2*(g (u-Real.log 2)+g (u+Real.log 2))
    + e3*(g (u-Real.log 3)+g (u+Real.log 3))

theorem fourWindowRadius_lt_quarter_of_threeHundred
    {t : ℝ} (ht : 300 ≤ t) :
    quarticFourCompletedRadius t < (1/4 : ℝ) := by
  have htpos : 0 < t := by linarith
  have hpi : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
  unfold quarticFourCompletedRadius
  rw [div_lt_iff₀ htpos]
  nlinarith

private theorem log_two_ge_half :
    (1/2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos
    (show (0:ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

private theorem log_three_ge_twoThird :
    (2/3 : ℝ) ≤ Real.log 3 := by
  have h := Real.one_sub_inv_le_log_of_pos
    (show (0:ℝ) < 3 by norm_num)
  norm_num at h ⊢
  exact h

private theorem log_three_sub_log_two_ge_quarter :
    (1/4 : ℝ) ≤ Real.log 3 - Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos
    (show (0:ℝ) < (3/2:ℝ) by norm_num)
  have hdiv : Real.log (3/2 : ℝ)
      = Real.log 3 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  rw [hdiv] at h
  norm_num at h ⊢
  linarith

private theorem log_four_sub_log_three_ge_quarter :
    (1/4 : ℝ) ≤ Real.log 4 - Real.log 3 := by
  have h := Real.one_sub_inv_le_log_of_pos
    (show (0:ℝ) < (4/3:ℝ) by norm_num)
  have hdiv : Real.log (4/3 : ℝ)
      = Real.log 4 - Real.log 3 :=
    Real.log_div (by norm_num) (by norm_num)
  rw [hdiv] at h
  norm_num at h ⊢
  exact h

private theorem detector_twoScale_zero_of_large
    {g : ℝ → ℝ}
    (hshort : ∀ u : ℝ, g u ≠ 0 → |u| < (1/4:ℝ))
    (u : ℝ)
    (hu : (1/4:ℝ) ≤ |u|) : g u = 0 := by
  by_contra hne
  exact (not_lt_of_ge hu) (hshort u hne)

/-- For any source supported inside (-1/4,1/4), the log2 frequency
reads only the first independent coefficient. -/
theorem detectorTwoScale_at_log_two
    {g : ℝ → ℝ} (hshort : ∀ u : ℝ, g u ≠ 0 → |u| < (1/4:ℝ))
    (e2 e3 : ℝ) :
    detectorTwoScale g e2 e3 (Real.log 2) = e2*g 0 := by
  have h2 := log_two_ge_half
  have h3 := log_three_ge_twoThird
  have hd := log_three_sub_log_two_ge_quarter
  have hz := detector_twoScale_zero_of_large hshort
  have h0 : g (Real.log 2) = 0 :=
    hz _ (by rw [abs_of_nonneg (by linarith)]; linarith)
  have h22 : g (Real.log 2 + Real.log 2) = 0 :=
    hz _ (by rw [abs_of_nonneg (by linarith)]; linarith)
  have h23 : g (Real.log 2 + Real.log 3) = 0 :=
    hz _ (by rw [abs_of_nonneg (by linarith)]; linarith)
  have h32 : g (Real.log 2 - Real.log 3) = 0 :=
    hz _ (by rw [abs_of_nonpos (by linarith)]; linarith)
  unfold detectorTwoScale
  rw [h0,h22,h23,h32]
  simp only [sub_self]
  ring

/-- The log3 shift is independent on the same narrow support. -/
theorem detectorTwoScale_at_log_three
    {g : ℝ → ℝ} (hshort : ∀ u : ℝ, g u ≠ 0 → |u| < (1/4:ℝ))
    (e2 e3 : ℝ) :
    detectorTwoScale g e2 e3 (Real.log 3) = e3*g 0 := by
  have h2 := log_two_ge_half
  have h3 := log_three_ge_twoThird
  have hd := log_three_sub_log_two_ge_quarter
  have hz := detector_twoScale_zero_of_large hshort
  have h0 : g (Real.log 3) = 0 :=
    hz _ (by rw [abs_of_nonneg (by linarith)]; linarith)
  have h32 : g (Real.log 3 - Real.log 2) = 0 :=
    hz _ (by rw [abs_of_nonneg (by linarith)]; linarith)
  have h32plus : g (Real.log 3 + Real.log 2) = 0 :=
    hz _ (by rw [abs_of_nonneg (by linarith)]; linarith)
  have h33plus : g (Real.log 3 + Real.log 3) = 0 :=
    hz _ (by rw [abs_of_nonneg (by linarith)]; linarith)
  unfold detectorTwoScale
  rw [h0,h32,h32plus,h33plus]
  simp only [sub_self]
  ring

theorem detectorTwoScale_at_log_nat_eq_zero_of_four_le
    {g : ℝ → ℝ}
    (hshort : ∀ u : ℝ, g u ≠ 0 → |u| < (1/4:ℝ))
    (e2 e3 : ℝ) (n : ℕ) (hn : 4 ≤ n) :
    detectorTwoScale g e2 e3 (Real.log n) = 0 := by
  have h2 := log_two_ge_half
  have h3 := log_three_ge_twoThird
  have hd := log_four_sub_log_three_ge_quarter
  have hn4 : Real.log (4:ℝ) ≤ Real.log (n:ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlog : (1/4:ℝ) ≤ Real.log n - Real.log 3 := by
    linarith
  have hlog2 : (1/4:ℝ) ≤ Real.log n - Real.log 2 := by
    linarith
  have hz := detector_twoScale_zero_of_large hshort
  have hzero (x : ℝ) (hx : (1/4:ℝ) ≤ x) : g x=0 :=
    hz x (by rw [abs_of_nonneg (by linarith)]; exact hx)
  have h0 : g (Real.log n) = 0 := hzero _ (by linarith)
  have hm2 : g (Real.log n - Real.log 2) = 0 := hzero _ hlog2
  have hp2 : g (Real.log n + Real.log 2) = 0 := hzero _ (by linarith)
  have hm3 : g (Real.log n - Real.log 3) = 0 := hzero _ hlog
  have hp3 : g (Real.log n + Real.log 3) = 0 := hzero _ (by linarith)
  simp [detectorTwoScale,h0,hm2,hp2,hm3,hp3]

theorem detectorTwoScale_even
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (e2 e3 : ℝ) :
    ∀ u : ℝ,
      detectorTwoScale g e2 e3 (-u)
        = detectorTwoScale g e2 e3 u := by
  intro u
  unfold detectorTwoScale
  rw [heven u,
    show -u-Real.log 2=-(u+Real.log 2) by ring,
    show -u+Real.log 2=-(u-Real.log 2) by ring,
    show -u-Real.log 3=-(u+Real.log 3) by ring,
    show -u+Real.log 3=-(u-Real.log 3) by ring,
    heven (u+Real.log 2),heven (u-Real.log 2),
    heven (u+Real.log 3),heven (u-Real.log 3)]
  ring

theorem quarticFourPhysicalDetector_support_quarter
    {R lam mu t : ℝ}
    (hR : 0 < R) (hRone : R < 1) (ht : 300 ≤ t) :
    ∀ u, quarticFourPhysicalDetector R lam mu t u ≠ 0 ->
      |u| < (1/4:ℝ) := by
  intro u hu
  have hpos : 0 < t := by linarith
  exact (quarticFourPhysicalDetector_support_completedRadius
    hR hRone hpos u hu).trans_lt
      (fourWindowRadius_lt_quarter_of_threeHundred ht)

theorem quarticFourPhysicalDetector_twoScale_samples
    {R lam mu t e2 e3 : ℝ}
    (hR : 0 < R) (hRone : R < 1) (ht : 300 ≤ t) :
    detectorTwoScale (quarticFourPhysicalDetector R lam mu t)
      e2 e3 (Real.log 2)
      = e2*quarticFourPhysicalDetector R lam mu t 0
    ∧
    detectorTwoScale (quarticFourPhysicalDetector R lam mu t)
      e2 e3 (Real.log 3)
      = e3*quarticFourPhysicalDetector R lam mu t 0
    ∧
    (∀ n : ℕ, 4 ≤ n →
       detectorTwoScale (quarticFourPhysicalDetector R lam mu t)
         e2 e3 (Real.log n) = 0) := by
  have hs := quarticFourPhysicalDetector_support_quarter
    hR hRone ht
  exact ⟨detectorTwoScale_at_log_two hs e2 e3,
    detectorTwoScale_at_log_three hs e2 e3,
    detectorTwoScale_at_log_nat_eq_zero_of_four_le hs e2 e3⟩


/-!
## All two-scale prime powers: exact literal Zeta23 finite sum

The prime n=4 is included in the far cutoff; there is no accidental
prime-square term after the physical support becomes smaller than 1/4.
-/

theorem detectorTwoScale_literalPrimeSummand_eq_zero_of_four_le
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (hshort : ∀ u : ℝ, g u ≠ 0 → |u| < (1/4:ℝ))
    (e2 e3 t s : ℝ) (n : ℕ) (hn : 4 ≤ n) :
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          (detectorTwoScale g e2 e3) t s (Real.log n)
        + Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          (detectorTwoScale g e2 e3) t s (-Real.log n))
      = 0 := by
  have hp :=
    detectorTwoScale_at_log_nat_eq_zero_of_four_le hshort e2 e3 n hn
  have hm :
      detectorTwoScale g e2 e3 (-Real.log n) = 0 := by
    rw [detectorTwoScale_even heven e2 e3 (Real.log n)]
    exact hp
  simp [Zeta23Bridge.LiteralWeilParityBalance.sampleTest,hp,hm]

theorem detectorTwoScale_primeTerm_eq_two_summands
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (hshort : ∀ u : ℝ, g u ≠ 0 → |u| < (1/4:ℝ))
    (e2 e3 t s : ℝ) :
    Zeta23Bridge.LiteralWeilParityBalance.primeTerm
      (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
        (detectorTwoScale g e2 e3) t s)
      =
    ∑ n ∈ ({2,3} : Finset ℕ),
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          (detectorTwoScale g e2 e3) t s (Real.log n)
        + Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          (detectorTwoScale g e2 e3) t s (-Real.log n)) := by
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
  · exact detectorTwoScale_literalPrimeSummand_eq_zero_of_four_le
      heven hshort e2 e3 t s n h4
  · have hn4 : n < 4 := Nat.lt_of_not_ge h4
    interval_cases n <;>
      simp [hne2,hne3,ArithmeticFunction.vonMangoldt]

theorem detectorTwoScale_primeTerm_eq_two_real_terms
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (hshort : ∀ u : ℝ, g u ≠ 0 → |u| < (1/4:ℝ))
    (e2 e3 t s : ℝ) :
    Zeta23Bridge.LiteralWeilParityBalance.primeTerm
      (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
        (detectorTwoScale g e2 e3) t s)
      =
    (((2 : ℝ)*g 0 *
      (e2*(ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
        * Real.cos ((s-t)*Real.log 2)
       + e3*(ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
        * Real.cos ((s-t)*Real.log 3))) : ℝ) := by
  rw [detectorTwoScale_primeTerm_eq_two_summands
    heven hshort e2 e3 t s]
  simp only [Finset.sum_insert (by simp : (2:ℕ) ∉ ({3}:Finset ℕ)),
    Finset.sum_singleton]
  rw [Zeta23Bridge.LiteralWeilPrimeEvenCone.primeSummand_sampleTest
      (detectorTwoScale_even heven e2 e3) t s 2,
    Zeta23Bridge.LiteralWeilPrimeEvenCone.primeSummand_sampleTest
      (detectorTwoScale_even heven e2 e3) t s 3]
  rw [detectorTwoScale_at_log_two hshort,
    detectorTwoScale_at_log_three hshort]
  push_cast
  ring

theorem quarticFourPhysicalDetector_twoScale_primeTerm_exact
    {R lam mu t e2 e3 s : ℝ}
    (hR : 0 < R) (hRone : R < 1) (ht : 300 ≤ t) :
    Zeta23Bridge.LiteralWeilParityBalance.primeTerm
      (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
        (detectorTwoScale
          (quarticFourPhysicalDetector R lam mu t) e2 e3) t s)
      =
    (((4 : ℝ)*(quarticWindowMass R)⁻¹ *
      (e2*(ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
        * Real.cos ((s-t)*Real.log 2)
       + e3*(ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
        * Real.cos ((s-t)*Real.log 3))) : ℝ) := by
  have hg : ∀ u,
      quarticFourPhysicalDetector R lam mu t (-u)
        = quarticFourPhysicalDetector R lam mu t u :=
    quarticFourPhysicalDetector_even R lam mu t
  rw [detectorTwoScale_primeTerm_eq_two_real_terms hg
    (quarticFourPhysicalDetector_support_quarter hR hRone ht)]
  rw [quarticFourPhysicalDetector_centre_eq hR hRone]
  ring

/-- Full even-cone prime channel, including both time phases and their
independent eps_2,eps_3 coefficients. -/
theorem quarticFourPhysicalDetector_twoScale_primeChannel_eq
    {R lam mu t e2 e3 : ℝ}
    (hR : 0 < R) (hRone : R < 1) (ht : 300 ≤ t)
    (s : ℝ) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeChannel
      (detectorTwoScale (quarticFourPhysicalDetector R lam mu t)
        e2 e3) t s
      =
    8*(quarticWindowMass R)⁻¹
      * (
        e2*(ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
           * Real.cos (s*Real.log 2) * Real.cos (t*Real.log 2)
        +
        e3*(ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
           * Real.cos (s*Real.log 3) * Real.cos (t*Real.log 3)
      ) := by
  let g := quarticFourPhysicalDetector R lam mu t
  have hsample (v : ℝ) :=
    quarticFourPhysicalDetector_twoScale_primeTerm_exact
      (R:=R) (lam:=lam) (mu:=mu) (t:=t)
      (e2:=e2) (e3:=e3) hR hRone ht (s:=v)
  change
    Zeta23Bridge.LiteralWeilParityBalance.reim
      (Zeta23Bridge.LiteralWeilParityBalance.primeTerm
        (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          (detectorTwoScale g e2 e3) t s))
    +
    Zeta23Bridge.LiteralWeilParityBalance.reim
      (Zeta23Bridge.LiteralWeilParityBalance.primeTerm
        (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          (detectorTwoScale g e2 e3) t (-s)))
    = _
  rw [hsample s, hsample (-s)]
  simp only [Zeta23Bridge.LiteralWeilParityBalance.reim,
    Complex.ofReal_re,Complex.ofReal_im,add_zero]
  calc
    _ =
      4*(quarticWindowMass R)⁻¹ *
        (e2*(ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
          * (Real.cos ((s-t)*Real.log 2)
            + Real.cos ((-s-t)*Real.log 2))
         + e3*(ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
          * (Real.cos ((s-t)*Real.log 3)
            + Real.cos ((-s-t)*Real.log 3))) := by ring
    _ = _ := by
      rw [threeTap_prime_cosine_pair s t (Real.log 2),
        threeTap_prime_cosine_pair s t (Real.log 3)]
      ring

/-- Two independent shifts cannot be reduced to the single-prime
factor cos(t log2); however this is still an exact arithmetic response,
not a positivity or high-zero estimate. -/
theorem quarticFourPhysicalDetector_twoScale_primeChannel_at_logTwo_resonance
    {R lam mu t e2 e3 : ℝ}
    (hR : 0 < R) (hRone : R < 1) (ht : 300 ≤ t)
    (hphase : Real.cos (t*Real.log 2) = 0)
    (s : ℝ) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeChannel
      (detectorTwoScale (quarticFourPhysicalDetector R lam mu t)
        e2 e3) t s
      =
    8*(quarticWindowMass R)⁻¹
       * e3*(ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
       * Real.cos (s*Real.log 3)*Real.cos (t*Real.log 3) := by
  rw [quarticFourPhysicalDetector_twoScale_primeChannel_eq hR hRone ht,
      hphase]
  ring


/-!
## Completed two-scale projective source

All prime amplitudes below come from the ACTUAL von-Mangoldt terms.
The on-line responses are evaluated on the same translated detector.
Their coefficients depend on e2,e3, making the final projective
prime response generally quadratic in the two parameters.
-/

def twoScalePrimeShape (g : ℝ → ℝ) (r L : ℝ) : ℝ :=
  Real.cos (2*r*L)
      * Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 r
    - Real.cos (r*L)
      * Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 (2*r)

theorem quarticFourPhysicalDetector_twoScale_primeProjective_eq
    {R lam mu t e2 e3 r : ℝ}
    (hR : 0 < R) (hRone : R < 1) (ht : 300 ≤ t) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
      (detectorTwoScale (quarticFourPhysicalDetector R lam mu t)
        e2 e3) t r
    =
    8*(quarticWindowMass R)⁻¹
      * (
        e2*(ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
          * Real.cos (t*Real.log 2)
          * twoScalePrimeShape
              (detectorTwoScale (quarticFourPhysicalDetector R lam mu t)
                e2 e3) r (Real.log 2)
        +
        e3*(ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
          * Real.cos (t*Real.log 3)
          * twoScalePrimeShape
              (detectorTwoScale (quarticFourPhysicalDetector R lam mu t)
                e2 e3) r (Real.log 3)
      ) := by
  unfold Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.channelProjectiveDefect
    twoScalePrimeShape
  rw [quarticFourPhysicalDetector_twoScale_primeChannel_eq hR hRone ht (2*r),
    quarticFourPhysicalDetector_twoScale_primeChannel_eq hR hRone ht r]
  ring

def QuarticFourSignedPolePair.twoScaleHalf
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (e2 e3 : ℝ) : ℝ → ℝ :=
  detectorTwoScale
    (quarticFourPhysicalDetector W.R (1/2) W.muHalf t) e2 e3

def QuarticFourSignedPolePair.twoScaleTwo
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (e2 e3 : ℝ) : ℝ → ℝ :=
  detectorTwoScale
    (quarticFourPhysicalDetector W.R (2/3) W.muTwo t) e2 e3

def QuarticFourSignedPolePair.twoScaleChannelCombination
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (e2 e3 : ℝ)
    (C : (ℝ → ℝ) → ℝ → ℝ → ℝ) : ℝ :=
  W.poleTwo*C (W.twoScaleHalf e2 e3) t (t/16)
    - W.poleHalf*C (W.twoScaleTwo e2 e3) t (t/16)

def QuarticFourSignedPolePair.twoScaleSignedPrimeCombination
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (e2 e3 : ℝ) : ℝ :=
  W.twoScaleChannelCombination e2 e3
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.primeProjectiveDefect

/-- The selected W has independently tunable 2 and 3 arithmetic phases,
but both are paired against the updated on-line column. -/
theorem QuarticFourSignedPolePair.twoScaleSignedPrimeCombination_eq
    {t e2 e3 : ℝ}
    (ht : 300 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    W.twoScaleSignedPrimeCombination e2 e3
      =
    8*(quarticWindowMass W.R)⁻¹
      * (
        e2*(ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
          * Real.cos (t*Real.log 2)
          * (W.poleTwo*twoScalePrimeShape
                 (W.twoScaleHalf e2 e3) (t/16) (Real.log 2)
            - W.poleHalf*twoScalePrimeShape
                 (W.twoScaleTwo e2 e3) (t/16) (Real.log 2))
        +
        e3*(ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
          * Real.cos (t*Real.log 3)
          * (W.poleTwo*twoScalePrimeShape
                 (W.twoScaleHalf e2 e3) (t/16) (Real.log 3)
            - W.poleHalf*twoScalePrimeShape
                 (W.twoScaleTwo e2 e3) (t/16) (Real.log 3))
      ) := by
  unfold QuarticFourSignedPolePair.twoScaleSignedPrimeCombination
    QuarticFourSignedPolePair.twoScaleChannelCombination
    QuarticFourSignedPolePair.twoScaleHalf
    QuarticFourSignedPolePair.twoScaleTwo
  rw [quarticFourPhysicalDetector_twoScale_primeProjective_eq
      W.Rpos W.RltOne ht,
    quarticFourPhysicalDetector_twoScale_primeProjective_eq
      W.Rpos W.RltOne ht]
  ring

theorem detectorTwoScale_eq_twoThreeTaps_sub
    (g : ℝ → ℝ) (e2 e3 : ℝ) :
    detectorTwoScale g e2 e3
      = (fun u =>
          detectorThreeTap g e2 (Real.log 2) u
            + detectorThreeTap g e3 (Real.log 3) u - g u) := by
  funext u
  unfold detectorTwoScale detectorThreeTap
  ring

theorem detectorTwoScale_contDiff
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (e2 e3 : ℝ) :
    ContDiff ℝ 2 (detectorTwoScale g e2 e3) := by
  unfold detectorTwoScale
  fun_prop

theorem detectorTwoScale_compact
    {g : ℝ → ℝ} (hg : HasCompactSupport g) (e2 e3 : ℝ) :
    HasCompactSupport (detectorTwoScale g e2 e3) := by
  rw [detectorTwoScale_eq_twoThreeTaps_sub]
  exact ((detectorThreeTap_compact hg e2 (Real.log 2)).add
    (detectorThreeTap_compact hg e3 (Real.log 3))).sub hg

def QuarticFourSignedPolePair.twoScaleCompletedArithmetic
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (e2 e3 : ℝ) : ℝ :=
  W.twoScaleSignedPrimeCombination e2 e3
    + W.twoScaleChannelCombination e2 e3
        Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
    + W.twoScaleChannelCombination e2 e3
        Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect

/-- Exact Zeta23 completed equality on the independently shifted selected
physical detectors. No original pole cancellation or terminal sign
property is reused without re-establishment. -/
theorem QuarticFourSignedPolePair.twoScaleCompletedCluster_eq_off_add_arithmetic
    {t e2 e3 : ℝ}
    (ht : 300 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    W.twoScaleChannelCombination e2 e3
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect
      =
    W.twoScaleChannelCombination e2 e3
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
      + W.twoScaleCompletedArithmetic e2 e3 := by
  have hhalf :=
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.clusterHeightDefect_eq_fourProjectiveChannels
      (detectorTwoScale_contDiff
        (quarticFourPhysicalDetector_contDiff W.Rpos) e2 e3)
      (detectorTwoScale_compact
        (quarticFourPhysicalDetector_compact W.Rpos (by linarith)) e2 e3)
      (detectorTwoScale_even
        (quarticFourPhysicalDetector_even W.R (1/2) W.muHalf t) e2 e3)
      t (t/16)
  have htwo :=
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.clusterHeightDefect_eq_fourProjectiveChannels
      (detectorTwoScale_contDiff
        (quarticFourPhysicalDetector_contDiff W.Rpos) e2 e3)
      (detectorTwoScale_compact
        (quarticFourPhysicalDetector_compact W.Rpos (by linarith)) e2 e3)
      (detectorTwoScale_even
        (quarticFourPhysicalDetector_even W.R (2/3) W.muTwo t) e2 e3)
      t (t/16)
  dsimp [QuarticFourSignedPolePair.twoScaleCompletedArithmetic,
    QuarticFourSignedPolePair.twoScaleSignedPrimeCombination,
    QuarticFourSignedPolePair.twoScaleChannelCombination,
    QuarticFourSignedPolePair.twoScaleHalf,
    QuarticFourSignedPolePair.twoScaleTwo] at *
  rw [hhalf,htwo]
  ring


/-!
## Exact completed increment against the unshifted selected witness

This subtracts the literal four-channel projective formula at
(e2,e3)=(0,0) from the formula at (e2,e3). A nonzero finite
prime contribution is necessarily balanced by the corresponding changes
in the same-witness off-ordinate, gamma, pole, and cluster channels.
No original pole cancellation or positive cluster estimate is reused.
-/

theorem QuarticFourSignedPolePair.twoScaleSignedPrimeCombination_zero
    {t : ℝ}
    (ht : 300 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    W.twoScaleSignedPrimeCombination 0 0 = 0 := by
  rw [W.twoScaleSignedPrimeCombination_eq ht]
  ring

/-- The theorem retains every changed completed channel. The presence of
n=2 and n=3 is not independent arithmetic control of the selected zero
because the same explicit formula forces this equality. -/
theorem QuarticFourSignedPolePair.twoScaleCompletedIncrement
    {t e2 e3 : ℝ}
    (ht : 300 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    W.twoScaleChannelCombination e2 e3
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect
      -
    W.twoScaleChannelCombination 0 0
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect
    =
    (W.twoScaleChannelCombination e2 e3
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
      - W.twoScaleChannelCombination 0 0
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect)
    +
    (W.twoScaleSignedPrimeCombination e2 e3
      - W.twoScaleSignedPrimeCombination 0 0)
    +
    (W.twoScaleChannelCombination e2 e3
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
      - W.twoScaleChannelCombination 0 0
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect)
    +
    (W.twoScaleChannelCombination e2 e3
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
      - W.twoScaleChannelCombination 0 0
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect) := by
  have hnew :=
    W.twoScaleCompletedCluster_eq_off_add_arithmetic ht (e2 := e2) (e3 := e3)
  have hbase :=
    W.twoScaleCompletedCluster_eq_off_add_arithmetic ht (e2 := 0) (e3 := 0)
  unfold QuarticFourSignedPolePair.twoScaleCompletedArithmetic at hnew hbase
  linarith

/-- A user of the exact two-prime result may eliminate the old zero-prime
baseline from the increment, but NOT the altered Gamma/pole/zero terms. -/
theorem QuarticFourSignedPolePair.twoScaleCompletedIncrement_exactPrime
    {t e2 e3 : ℝ}
    (ht : 300 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    W.twoScaleChannelCombination e2 e3
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect
      -
    W.twoScaleChannelCombination 0 0
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect
    =
    (W.twoScaleChannelCombination e2 e3
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
      - W.twoScaleChannelCombination 0 0
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect)
    +
    W.twoScaleSignedPrimeCombination e2 e3
    +
    (W.twoScaleChannelCombination e2 e3
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
      - W.twoScaleChannelCombination 0 0
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect)
    +
    (W.twoScaleChannelCombination e2 e3
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
      - W.twoScaleChannelCombination 0 0
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect) := by
  have h := W.twoScaleCompletedIncrement ht (e2 := e2) (e3 := e3)
  rw [W.twoScaleSignedPrimeCombination_zero ht] at h
  simpa only [sub_zero] using h

end Synthesis
