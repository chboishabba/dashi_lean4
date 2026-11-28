import Synthesis.MillenniumBSDSignedMellinMomentProgressionExact
import Synthesis.MillenniumBSDOriginalTwoCrossingRankFourSignCutExact

/-!
Exact all-degree sign propagation for the original two-crossing Mellin
kernel. The original signed polynomial factorization (already proven)
makes every integrated shifted polynomial strictly positive when the
original two-crossing density has positive mass away from the nodes.
It follows that a nonnegative m1 and zero m0 force ALL m_k (k>=2)
strictly positive, not merely m2.

The physical Mellin/source positivity hypotheses remain explicit.
This is an obstruction/diagnostic on the actual selected source
moments, NOT BSD analytic rank equality or L''=0.
-/
namespace DASHI.BSD.SignedCrossing

/-- Exact all-degree original two-crossing moment progression.
The single shared m0 is carried unchanged at every degree.
No new synthetic source measure or independent recurrence carrier. -/
theorem original_two_crossing_all_higher_moments_positive
    (a b : ℝ) (m : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hzero : m 0 = 0) (hfirst : 0 ≤ m 1)
    (hsource : ∀ n : ℕ,
      0 < h a b n * m (n+2) -
        h a b (n+1) * m (n+1) + (a*b)^(n+1) * m 0) :
    ∀ n : ℕ, 0 < m (n+2) := by
  intro n
  induction n with
  | zero =>
      exact next_moment_pos ha hb 0 hzero hfirst (hsource 0)
  | succ n ih =>
      have hstep := next_moment_pos ha hb (n+1) hzero
        (le_of_lt ih) (hsource (n+1))
      simpa only [Nat.succ_eq_add_one] using hstep

/-- Any alleged nonpositive higher original Mellin moment, in
particular a complex-rank-four second-derivative zero once a true
Mellin-to-L bridge exists, contradicts the conjunction of the
actual positive two-crossing integral source and nonnegative m1. -/
theorem original_two_crossing_zero_higher_obstructs_nonnegative_first
    (a b : ℝ) (m : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hzero : m 0 = 0)
    (hsource : ∀ n : ℕ,
      0 < h a b n * m (n+2) -
        h a b (n+1) * m (n+1) + (a*b)^(n+1) * m 0)
    (n : ℕ) (hnonpos : m (n+2) ≤ 0) :
    m 1 < 0 := by
  by_contra h
  have hfirst : 0 ≤ m 1 := le_of_not_gt h
  have hp := original_two_crossing_all_higher_moments_positive
    a b m ha hb hzero hfirst hsource n
  exact (not_lt_of_ge hnonpos) hp

end DASHI.BSD.SignedCrossing
