import Synthesis.RiemannSelectedPrimeSensitiveThreeTapSupportCut

/-!
# The complete two-prime three-tap response and its projective audit

The selected short physical detector g has support |u| < log 2.
After translation by ±log 2, the *literal* von-Mangoldt sum has exactly
the possible positive frequencies n=2 and n=3. Its n=3 amplitude is
g(log (3/2)), not g(0). All n>=4, including n=4, are zero.
The resulting full prime term retains the precise s-t phases.

The projective determinant is NOT linear in the perturbation parameter,
because its second (on-line) column changes as well. The quadratic
coefficient below is therefore essential for any terminal-margin test.
-/

noncomputable section
namespace Synthesis
open scoped Real

private theorem log_two_pos : (0:ℝ) < Real.log 2 := by positivity

private theorem log_three_lt_two_log_two :
    Real.log (3:ℝ) < 2 * Real.log 2 := by
  have h : Real.log (3:ℝ) < Real.log 4 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have h4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ)=2*2 by norm_num, Real.log_mul (by norm_num : (2:ℝ) ≠ 0)
      (by norm_num : (2:ℝ) ≠ 0)]
    ring
  exact h.trans_eq h4

private theorem log_two_lt_log_three :
    Real.log (2:ℝ) < Real.log 3 := by
  exact Real.log_lt_log (by norm_num) (by norm_num)

private theorem log_three_sub_log_two_eq :
    Real.log (3:ℝ) - Real.log 2 = Real.log (3/2 : ℝ) := by
  rw [Real.log_div (by norm_num : (3:ℝ) ≠ 0)
    (by norm_num : (2:ℝ) ≠ 0)]

/-- The third prime is newly exposed by the left translate. -/
theorem detectorThreeTap_at_thirdPrime_of_shortSupport
    (g : ℝ → ℝ) (eps : ℝ)
    (hshort : ∀ u : ℝ, g u ≠ 0 → |u| < Real.log 2) :
    detectorThreeTap g eps (Real.log 2) (Real.log 3)
      = eps * g (Real.log (3/2 : ℝ)) := by
  have hlog2 := log_two_pos
  have hlog23 := log_two_lt_log_three
  have hlog34 := log_three_lt_two_log_two
  have hz (x : ℝ) (hx : Real.log 2 ≤ x) : g x = 0 := by
    by_contra h
    have hs := hshort x h
    rw [abs_of_nonneg (by linarith : 0 ≤ x)] at hs
    exact (not_lt_of_ge hx) hs
  have hz3 : g (Real.log 3) = 0 := hz _ hlog23.le
  have hz3plus : g (Real.log 3 + Real.log 2) = 0 :=
    hz _ (by linarith)
  unfold detectorThreeTap
  rw [hz3, hz3plus, log_three_sub_log_two_eq]
  ring

/-- The full (complex) n=3 summand uses both ±log 3; its phase can
cancel the n=2 summand, so neither term is asserted to be positive. -/
theorem detectorThreeTap_literalThirdPrimeSummand
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2)
    (eps t s : ℝ) :
    ((ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ) : ℂ)
      * (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          (detectorThreeTap g eps (Real.log 2)) t s (Real.log 3)
       + Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          (detectorThreeTap g eps (Real.log 2)) t s (-Real.log 3))
    =
    (((ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
      * (2 * (eps*g (Real.log (3/2 : ℝ)))
        * Real.cos ((s-t)*Real.log 3))) : ℝ) := by
  have h :=
    Zeta23Bridge.LiteralWeilPrimeEvenCone.primeSummand_sampleTest
      (detectorThreeTap_even heven eps (Real.log 2)) t s 3
  rw [detectorThreeTap_at_thirdPrime_of_shortSupport g eps hshort] at h
  exact h

/-- All literal prime-power samples n>=4 vanish, including 4 itself:
strict short support makes the new boundary at 2 log 2 zero. -/
theorem detectorThreeTap_literalPrimeSummand_eq_zero_of_four_le
    {g : ℝ → ℝ}
    (hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2)
    (eps t s : ℝ) (n : ℕ) (hn : 4 ≤ n) :
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          (detectorThreeTap g eps (Real.log 2)) t s (Real.log n)
       + Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          (detectorThreeTap g eps (Real.log 2)) t s (-Real.log n))
       = 0 := by
  have hlog :
      2*Real.log 2 ≤ Real.log (n:ℝ) := by
    have hlogn : Real.log (4:ℝ) ≤ Real.log (n:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    rw [show Real.log (4:ℝ)=2*Real.log 2 by
      rw [show (4:ℝ)=2*2 by norm_num,
        Real.log_mul (by norm_num : (2:ℝ) ≠ 0)
          (by norm_num : (2:ℝ) ≠ 0)]
      ring] at hlogn
    exact hlogn
  have hpos : 0 ≤ Real.log (n:ℝ) := by linarith [log_two_pos]
  have hzplus :
      detectorThreeTap g eps (Real.log 2) (Real.log n) = 0 :=
    detectorThreeTap_vanishes_on_far_right log_two_pos hshort hlog
  have hzminus :
      detectorThreeTap g eps (Real.log 2) (-Real.log n) = 0 :=
    detectorThreeTap_vanishes_on_far_left log_two_pos hshort
      (by linarith)
  simp [Zeta23Bridge.LiteralWeilParityBalance.sampleTest,
    hzplus,hzminus]

/-- Finite full von-Mangoldt sum, in the precise sampleTest convention. -/
theorem detectorThreeTap_primeTerm_eq_two_summands
    {g : ℝ → ℝ}
    (hshort : ∀ u : ℝ, g u ≠ 0 → |u| < Real.log 2)
    (eps t s : ℝ) :
    Zeta23Bridge.LiteralWeilParityBalance.primeTerm
      (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
        (detectorThreeTap g eps (Real.log 2)) t s)
      =
    ∑ n ∈ ({2,3} : Finset ℕ),
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          (detectorThreeTap g eps (Real.log 2)) t s (Real.log n)
        + Zeta23Bridge.LiteralWeilParityBalance.sampleTest
          (detectorThreeTap g eps (Real.log 2)) t s (-Real.log n)) := by
  unfold Zeta23Bridge.LiteralWeilParityBalance.primeTerm
  apply tsum_eq_sum
  intro n hn
  have hneq2 : n ≠ 2 := by
    intro h; exact hn (by simp [h])
  have hneq3 : n ≠ 3 := by
    intro h; exact hn (by simp [h])
  by_cases h4 : 4 ≤ n
  · exact detectorThreeTap_literalPrimeSummand_eq_zero_of_four_le
      hshort eps t s n h4
  · have hn3 : n < 4 := Nat.lt_of_not_ge h4
    interval_cases n <;>
      simp [hneq2,hneq3,ArithmeticFunction.vonMangoldt]

/-- The combined source is exactly eps times TWO explicit cosine terms. -/
theorem detectorThreeTap_primeTerm_eq_two_real_terms
    {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u)
    (hshort : ∀ u : ℝ, g u ≠ 0 → |u| < Real.log 2)
    (eps t s : ℝ) :
    Zeta23Bridge.LiteralWeilParityBalance.primeTerm
      (Zeta23Bridge.LiteralWeilParityBalance.sampleTest
        (detectorThreeTap g eps (Real.log 2)) t s)
      =
    (((2*eps : ℝ) *
      ((ArithmeticFunction.vonMangoldt 2 / Real.sqrt 2 : ℝ)
          * g 0 * Real.cos ((s-t)*Real.log 2)
       + (ArithmeticFunction.vonMangoldt 3 / Real.sqrt 3 : ℝ)
          * g (Real.log (3/2 : ℝ))
          * Real.cos ((s-t)*Real.log 3))) : ℝ) := by
  rw [detectorThreeTap_primeTerm_eq_two_summands hshort eps t s]
  simp only [Finset.sum_insert (by simp : (2:ℕ) ∉ ({3}:Finset ℕ))]
  simp only [Finset.sum_singleton]
  rw [detectorThreeTap_literalFirstPrimeSummand heven hshort,
    detectorThreeTap_literalThirdPrimeSummand heven hshort]
  push_cast
  ring

/-- The full prime term is linear in eps, but projectivizing against a
detector-dependent on-line column creates a genuine quadratic correction. -/
theorem projectiveDefect_twoTap_polynomial
    (P0 P1 A0 A1 r : ℝ) :
    ((P0 + r*P1) * (A0 + r*A1))
       = P0*A0 + r*(P0*A1 + P1*A0) + r^2*(P1*A1) := by ring

/-- Exact two-radius projective quadratic expansion with no unjustified
linearity in the changing on-line detector. -/
theorem projectiveTwoRadius_primeQuadratic
    (P0r P0two P1r P1two A0r A0two A1r A1two eps : ℝ) :
    (P0two + eps*P1two)*(A0r + eps*A1r)
       - (P0r + eps*P1r)*(A0two + eps*A1two)
    =
    (P0two*A0r - P0r*A0two)
      + eps*((P1two*A0r - P1r*A0two)
           + (P0two*A1r - P0r*A1two))
      + eps^2*(P1two*A1r-P1r*A1two) := by ring

/-- In the original selected support the baseline prime column is zero;
the two remaining terms are linear and quadratic in the tap strength. -/
theorem projectiveTwoRadius_zeroBaselinePrime
    (P1r P1two A0r A0two A1r A1two eps : ℝ) :
    (eps*P1two)*(A0r + eps*A1r)
      - (eps*P1r)*(A0two + eps*A1two)
    =
    eps*(P1two*A0r-P1r*A0two)
      + eps^2*(P1two*A1r-P1r*A1two) := by ring

end Synthesis
