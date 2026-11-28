import Synthesis.MillenniumBSDOriginalTwoCrossingStrictPositiveDegreeFloorExact

/-!
Section40: original two-crossing signed Mellin source monotone
consequence at a genuine geometric crossing threshold.

If max(a,b) >= 1, the original strict growth theorem already
proved from the ALL-DEGREE positive signed two-crossing source
implies m_(n+2)>m_(n+1) at every degree: the previous moment is
nonnegative on the same source. If max(a,b)>1, the original
all-positive-degree envelope also provides strict expansion
relative to m2. This is a necessary admissibility test on a
proposed selected complex Mellin identification, NOT evidence
of that missing identity, Selmer rank or Sha finiteness.

All theorems source-written pending native Lean elaboration.
-/
namespace DASHI.BSD.SignedCrossing

theorem original_two_crossing_positive_scale_monotone_moments
    (a b : ℝ) (m : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hscale : 1 ≤ max a b)
    (hzero : m 0 = 0) (hfirst : 0 ≤ m 1)
    (hsource : ∀ n : ℕ,
      0 < h a b n * m (n+2) -
        h a b (n+1) * m (n+1) +
        (a*b)^(n+1) * m 0) :
    ∀ n, m (n+1) < m (n+2) := by
  intro n
  have hnonneg : 0 ≤ m (n+1) := by
    cases n with
    | zero => simpa using hfirst
    | succ k =>
      exact (original_two_crossing_all_higher_moments_positive
        a b m ha hb hzero hfirst hsource k).le
  have hstrict := original_two_crossing_both_strict_growth
    a b m ha hb hzero hfirst hsource n
  have hcompare : m (n+1) ≤ max a b * m (n+1) := by
    nlinarith
  exact lt_of_le_of_lt hcompare hstrict

/-- A proposed original moment sequence with a non-increasing
positive-degree step contradicts the original signed two-crossing
integral at scale max(a,b)>=1. This does not establish a new
analytic number theory result without the actual Mellin source. -/
theorem original_two_crossing_no_nonincreasing_moment_step
    (a b : ℝ) (m : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hscale : 1 ≤ max a b)
    (hzero : m 0 = 0) (hfirst : 0 ≤ m 1)
    (hsource : ∀ n : ℕ,
      0 < h a b n * m (n+2) -
        h a b (n+1) * m (n+1) +
        (a*b)^(n+1) * m 0)
    (n : ℕ) (hbad : m (n+2) ≤ m (n+1)) : False := by
  exact (not_lt_of_ge hbad)
    (original_two_crossing_positive_scale_monotone_moments
      a b m ha hb hscale hzero hfirst hsource n)

end DASHI.BSD.SignedCrossing
