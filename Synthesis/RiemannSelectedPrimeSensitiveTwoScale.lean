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

end Synthesis
