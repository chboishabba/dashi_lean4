import Synthesis.MillenniumBSDOriginalTwoCrossingMellinGeometricFloorExact

/-!
Section 36 original two-crossing Mellin moment global geometric lower
envelope, on the SAME signed source m and original crossing a.

This compounds the already source-written strict pointwise growth,
without introducing an unrelated moment recurrence or hypothetical
complex L function. The hypothesis that the original integrated signed
two-crossing polynomial is positive at EVERY degree is explicit.

Still missing: actual selected complex L'' / Mellin equality, rank
and Sha. An envelope of original moments is not such an equality.
-/
namespace DASHI.BSD.SignedCrossing

theorem original_two_crossing_all_degree_geometric_floor
    (a b : ℝ) (m : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hzero : m 0 = 0) (hfirst : 0 ≤ m 1)
    (hsource : ∀ n : ℕ,
      0 < h a b n * m (n+2) -
        h a b (n+1) * m (n+1) +
        (a*b)^(n+1) * m 0) :
    ∀ n : ℕ, a^n * m 2 ≤ m (n+2) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := original_two_crossing_moment_strict_a_growth
      a b m ha hb hzero hfirst hsource (n+1)
    have hmult := mul_le_mul_of_nonneg_left ih ha.le
    calc
      a^(n+1) * m 2 = a * (a^n * m 2) := by rw [pow_succ]; ring
      _ ≤ a * m (n+2) := hmult
      _ ≤ m ((n+1)+2) := le_of_lt (by simpa [Nat.add_assoc] using hstep)

/-- The same actual source cannot exhibit an alleged higher moment
below the all-degree original crossing-scaled moment floor. -/
theorem original_two_crossing_geometric_floor_no_go
    (a b : ℝ) (m : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hzero : m 0 = 0) (hfirst : 0 ≤ m 1)
    (hsource : ∀ n : ℕ,
      0 < h a b n * m (n+2) -
        h a b (n+1) * m (n+1) +
        (a*b)^(n+1) * m 0)
    (n : ℕ) (hbad : m (n+2) < a^n * m 2) : False := by
  have hfloor := original_two_crossing_all_degree_geometric_floor
    a b m ha hb hzero hfirst hsource n
  exact (not_lt_of_ge hfloor) hbad

end DASHI.BSD.SignedCrossing
