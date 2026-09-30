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

end Synthesis
