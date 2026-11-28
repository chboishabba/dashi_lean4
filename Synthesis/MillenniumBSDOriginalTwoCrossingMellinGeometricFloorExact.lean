import Synthesis.MillenniumBSDOriginalTwoCrossingStrictMomentGrowthExact
import Synthesis.MillenniumBSDOriginalTwoCrossingAllDegreeSignPropagationExact

/-!
Section35: original two-crossing signed Mellin strict moment growth
has a source-dependent *geometric floor*.

For positive original crossing addresses a,b and zeroth moment zero,
the strict original signed polynomial integral implies
  m_(n+2) > a * m_(n+1),  all n,
provided the original first moment is nonnegative. In particular
the original higher moments cannot decay faster than this
positive original crossing scale.

This is a falsifiable boundary condition on any actual selected
complex L-jet/Mellin source identification. It does not establish
such an identification, rank equality, or finiteness of Sha.
-/
namespace DASHI.BSD.SignedCrossing

/-- Strict one-step original Mellin lower slope at the *original*
first crossing a, not an artificial scale fitted to finite data. -/
theorem original_two_crossing_moment_strict_a_growth
    (a b : ℝ) (m : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hzero : m 0 = 0) (hfirst : 0 ≤ m 1)
    (hsource : ∀ n : ℕ,
      0 < h a b n * m (n+2) -
        h a b (n+1) * m (n+1) +
        (a*b)^(n+1) * m 0) :
    ∀ n, a * m (n+1) < m (n+2) := by
  intro n
  have hm : 0 ≤ m (n+1) := by
    cases n with
    | zero => simpa using hfirst
    | succ k =>
      convert (original_two_crossing_all_higher_moments_positive
        a b m ha hb hzero hfirst hsource k).le using 1 <;> omega
  have hs := original_two_crossing_all_degree_strict_weighted_growth
    a b m ha hb hzero hsource n
  have hrecur : h a b (n+1) = a * h a b n + b^(n+1) := rfl
  rw [hrecur] at hs
  have hrest : 0 ≤ b^(n+1) * m (n+1) :=
    mul_nonneg (pow_nonneg hb.le _) hm
  have hh := h_pos ha hb n
  have hw : h a b n * (a * m (n+1)) <
      h a b n * m (n+2) := by
    nlinarith [hs, hrest]
  exact (mul_lt_mul_left hh).mp hw

/-- No original selected two-crossing sequence can have a
nonincreasing moment step after rescaling by a > 0. -/
theorem original_two_crossing_no_sub_a_growth
    (a b : ℝ) (m : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hzero : m 0 = 0) (hfirst : 0 ≤ m 1)
    (hsource : ∀ n : ℕ,
      0 < h a b n * m (n+2) -
        h a b (n+1) * m (n+1) +
        (a*b)^(n+1) * m 0)
    (n : ℕ)
    (hbad : m (n+2) ≤ a * m (n+1)) : False := by
  exact (not_lt_of_ge hbad)
    (original_two_crossing_moment_strict_a_growth
      a b m ha hb hzero hfirst hsource n)

end DASHI.BSD.SignedCrossing
