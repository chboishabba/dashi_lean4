import Synthesis.MillenniumBSDOriginalTwoCrossingAllDegreeSignPropagationExact

/-!
Section 31 original two-crossing signed Mellin reverse solve:
the STRICT positive source integral forces a quantitative lower
bound on the ratio between every pair of consecutive moments
after the zero-mass normalization.

This is an actual necessary constraint for any attempted selected
complex L-derivative/Mellin identification. No substitute Mellin
measure, no claim the complex L'' is zero, and no BSD rank proof.
-/
namespace DASHI.BSD.SignedCrossing

/-- A strict original signed two-crossing source integral and
the original zeroth moment zero give a positive *weighted slope*
for every degree. This is NOT merely a nonnegative moment sign. -/
theorem original_two_crossing_all_degree_strict_weighted_growth
    (a b : ℝ) (m : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hzero : m 0 = 0)
    (hsource : ∀ n : ℕ,
      0 < h a b n * m (n+2) -
        h a b (n+1) * m (n+1) + (a*b)^(n+1) * m 0) :
    ∀ n, h a b (n+1) * m (n+1) <
      h a b n * m (n+2) := by
  intro n
  have hs := hsource n
  rw [hzero, mul_zero, add_zero] at hs
  linarith

/-- The exact minimum growth ratio required by the SAME original
selected two-crossing Mellin source. This is a falsifiable inverse
condition on an independently computed original complex L-jet. -/
theorem original_two_crossing_strict_moment_ratio
    (a b : ℝ) (m : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hzero : m 0 = 0)
    (hsource : ∀ n : ℕ,
      0 < h a b n * m (n+2) -
        h a b (n+1) * m (n+1) + (a*b)^(n+1) * m 0) :
    ∀ n, (h a b (n+1) * m (n+1)) / h a b n < m (n+2) := by
  intro n
  exact (div_lt_iff₀ (h_pos ha hb n)).2
    (original_two_crossing_all_degree_strict_weighted_growth
      a b m ha hb hzero hsource n)

/-- An original candidate moment sequence that violates the weighted
growth at ANY degree cannot have strict two-crossing source
positivity at all degrees with zero total mass. The contradiction
is on the SAME candidate m, no new analytic carrier. -/
theorem original_two_crossing_no_nonpositive_weighted_increment
    (a b : ℝ) (m : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hzero : m 0 = 0)
    (hsource : ∀ n : ℕ,
      0 < h a b n * m (n+2) -
        h a b (n+1) * m (n+1) + (a*b)^(n+1) * m 0)
    (n : ℕ)
    (hbad : h a b n * m (n+2) ≤
      h a b (n+1) * m (n+1)) : False := by
  exact not_lt_of_ge hbad
    (original_two_crossing_all_degree_strict_weighted_growth
      a b m ha hb hzero hsource n)

end DASHI.BSD.SignedCrossing
