import Synthesis.MillenniumBSDOriginalTwoCrossingAllDegreeGeometricEnvelopeExact

/-!
Section37: EXACT two-sided original crossing symmetry, not an arbitrary
choice of the first positive node.

The original complete homogeneous polynomial h(a,b,n), already owned
by MillenniumBSDSignedMellinMomentProgressionExact, has BOTH
recurrences:
   h_(n+1)=a*h_n+b^(n+1)=b*h_n+a^(n+1).
Consequently the actual signed two-crossing positive-source integral
with m0=0,m1>=0 imposes STRICTLY faster growth than BOTH original
crossings individually.

The result is a geometry-forward necessary constraint on an alleged
selected ORIGINAL Mellin/L-jet correspondence. It does not prove that
correspondence, analytic rank or finiteness of Sha.
-/
namespace DASHI.BSD.SignedCrossing

/-- The previously one-sided two-crossing h recurrence is literally
symmetric. This avoids assigning arbitrary priority to either
original crossing address in the Mellin source. -/
theorem original_two_crossing_h_reverse_recurrence (a b : ℝ) :
    ∀ n : ℕ, h a b (n+1) = b * h a b n + a^(n+1) := by
  intro n
  induction n with
  | zero =>
      simp [h]
      ring
  | succ n ih =>
      calc
        h a b ((n+1)+1) =
            a * h a b (n+1) + b^((n+1)+1) := rfl
        _ = a * (b*h a b n + a^(n+1)) +
              b * b^(n+1) := by
                rw [ih, pow_succ]
                ring
        _ = b * (a*h a b n + b^(n+1)) +
              a^((n+1)+1) := by
                rw [pow_succ]
                ring
        _ = b * h a b (n+1) + a^((n+1)+1) := rfl

/-- The actual *other* original crossing node b also strictly
bounds the same signed Mellin moment growth. -/
theorem original_two_crossing_moment_strict_b_growth
    (a b : ℝ) (m : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hzero : m 0 = 0) (hfirst : 0 ≤ m 1)
    (hsource : ∀ n : ℕ,
      0 < h a b n * m (n+2) -
        h a b (n+1) * m (n+1) +
        (a*b)^(n+1) * m 0) :
    ∀ n, b * m (n+1) < m (n+2) := by
  intro n
  have hm : 0 ≤ m (n+1) := by
    cases n with
    | zero => simpa using hfirst
    | succ k =>
      convert (original_two_crossing_all_higher_moments_positive
        a b m ha hb hzero hfirst hsource k).le using 1 <;> omega
  have hs := original_two_crossing_all_degree_strict_weighted_growth
    a b m ha hb hzero hsource n
  rw [original_two_crossing_h_reverse_recurrence a b n] at hs
  have hrest : 0 ≤ a^(n+1)*m (n+1) :=
    mul_nonneg (pow_nonneg ha.le _) hm
  have hh := h_pos ha hb n
  have hw : h a b n * (b*m (n+1)) <
      h a b n * m (n+2) := by
    nlinarith [hs,hrest]
  exact (mul_lt_mul_left hh).mp hw

/-- Both original crossing addresses constrain the SAME original
Mellin source for every degree; no orientation choice is assumed. -/
theorem original_two_crossing_both_strict_growth
    (a b : ℝ) (m : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hzero : m 0 = 0) (hfirst : 0 ≤ m 1)
    (hsource : ∀ n : ℕ,
      0 < h a b n * m (n+2) -
        h a b (n+1) * m (n+1) +
        (a*b)^(n+1) * m 0) :
    ∀ n, max a b * m (n+1) < m (n+2) := by
  intro n
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    exact original_two_crossing_moment_strict_b_growth
      a b m ha hb hzero hfirst hsource n
  · rw [max_eq_left hba]
    exact original_two_crossing_moment_strict_a_growth
      a b m ha hb hzero hfirst hsource n

/-- An all-index consequence with the stronger original symmetric
crossing scale max(a,b), not only the chart's first node. -/
theorem original_two_crossing_max_geometric_floor
    (a b : ℝ) (m : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hzero : m 0 = 0) (hfirst : 0 ≤ m 1)
    (hsource : ∀ n : ℕ,
      0 < h a b n * m (n+2) -
        h a b (n+1) * m (n+1) +
        (a*b)^(n+1) * m 0) :
    ∀ n, (max a b)^n * m 2 ≤ m (n+2) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := original_two_crossing_both_strict_growth
      a b m ha hb hzero hfirst hsource (n+1)
    have hm : 0 ≤ max a b := le_max_of_le_left ha.le
    have hmult := mul_le_mul_of_nonneg_left ih hm
    calc
      (max a b)^(n+1)*m 2 =
          max a b * ((max a b)^n * m 2) := by
            rw [pow_succ]; ring
      _ ≤ max a b * m (n+2) := hmult
      _ ≤ m ((n+1)+2) := le_of_lt (by simpa [Nat.add_assoc] using hstep)

end DASHI.BSD.SignedCrossing
