import Synthesis.MillenniumBSDOriginalTwoCrossingSymmetricMomentFloorExact

/-!
Section39 BSD: strict original symmetric two-crossing geometric floor
for every POSITIVE step, including the true n=1 endpoint.

The weaker earlier theorem gave m_(n+2) >= max(a,b)^n m2.
Using the original signed two-crossing source strictness at each
successive step, the actual n>0 source is STRICTLY above that floor.
This is exact and source-native, with no invented Mellin density,
no transfer from a numerical central complex L sample, and no
promotion to BSD analytic-rank or finiteness of Sha.

The still-missing selected complex L''/Mellin identity must satisfy
these necessary inequalities if the original two-crossing source
hypotheses are applicable. Native Lean kernel pending.
-/
namespace DASHI.BSD.SignedCrossing

theorem original_two_crossing_strict_geometric_floor_at_positive_degree
    (a b : ℝ) (m : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hzero : m 0 = 0) (hfirst : 0 ≤ m 1)
    (hsource : ∀ n : ℕ,
      0 < h a b n * m (n+2) -
        h a b (n+1) * m (n+1) +
        (a*b)^(n+1) * m 0) :
    ∀ n : ℕ, 0 < n →
      (max a b)^n * m 2 < m (n+2) := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hfloor := original_two_crossing_max_geometric_floor
    a b m ha hb hzero hfirst hsource k
  have hmax : 0 ≤ max a b := le_max_of_le_left ha.le
  have hmult := mul_le_mul_of_nonneg_left hfloor hmax
  have hstep := original_two_crossing_both_strict_growth
    a b m ha hb hzero hfirst hsource (k+1)
  calc
    (max a b)^(k+1)*m 2 =
        max a b*((max a b)^k*m 2) := by rw [pow_succ]; ring
    _ ≤ max a b*m (k+2) := hmult
    _ < m ((k+1)+2) := by simpa [Nat.add_assoc] using hstep

/-- A genuine reverse-solve obstruction for a proposed original
Mellin moment source, now with STRICT comparison for all n>0. -/
theorem original_two_crossing_no_attained_floor_at_positive_degree
    (a b : ℝ) (m : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hzero : m 0 = 0) (hfirst : 0 ≤ m 1)
    (hsource : ∀ n : ℕ,
      0 < h a b n * m (n+2) -
        h a b (n+1) * m (n+1) +
        (a*b)^(n+1) * m 0)
    (n : ℕ) (hn : 0 < n)
    (hbad : m (n+2) ≤ (max a b)^n*m 2) : False := by
  exact (not_lt_of_ge hbad)
    (original_two_crossing_strict_geometric_floor_at_positive_degree
      a b m ha hb hzero hfirst hsource n hn)

end DASHI.BSD.SignedCrossing
