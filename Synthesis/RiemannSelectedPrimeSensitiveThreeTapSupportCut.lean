import Synthesis.RiemannSelectedPrimeSensitiveThreeTap

/-!
# Prime-sensitive three-tap: exact support tail and first-sample comparison

This consumes the actual source-native detectorThreeTap and short-support
hypotheses from the RH branch. The translated detector can activate a prime
sample at log 2, but its response is exactly zero beyond the twice-shift
threshold. The first sample remains conditional on the source centre g(0)
and its explicit-formula phase; nothing here bounds the completed RH
functional or claims all prime summands have the same sign.
-/

noncomputable section

namespace Synthesis

theorem detectorThreeTap_vanishes_on_far_right
    {g : ℝ → ℝ} {L eps u : ℝ}
    (hL : 0 < L)
    (hshort : ∀ v : ℝ, g v ≠ 0 → |v| < L)
    (hfar : 2 * L ≤ u) :
    detectorThreeTap g eps L u = 0 := by
  have zero_of_large (v : ℝ) (hv : L ≤ |v|) : g v = 0 := by
    by_contra hne
    exact (not_lt_of_ge hv) (hshort v hne)
  have hu : 0 ≤ u := by linarith
  have hminus : 0 ≤ u - L := by linarith
  have hplus : 0 ≤ u + L := by linarith
  have h0 : g u = 0 :=
    zero_of_large u (by rw [abs_of_nonneg hu]; linarith)
  have h1 : g (u-L) = 0 :=
    zero_of_large (u-L) (by rw [abs_of_nonneg hminus]; linarith)
  have h2 : g (u+L) = 0 :=
    zero_of_large (u+L) (by rw [abs_of_nonneg hplus]; linarith)
  simp [detectorThreeTap, h0, h1, h2]

theorem detectorThreeTap_vanishes_on_far_left
    {g : ℝ → ℝ} {L eps u : ℝ}
    (hL : 0 < L)
    (hshort : ∀ v : ℝ, g v ≠ 0 → |v| < L)
    (hfar : u ≤ -(2 * L)) :
    detectorThreeTap g eps L u = 0 := by
  have zero_of_large (v : ℝ) (hv : L ≤ |v|) : g v = 0 := by
    by_contra hne
    exact (not_lt_of_ge hv) (hshort v hne)
  have hu : u ≤ 0 := by linarith
  have hminus : u - L ≤ 0 := by linarith
  have hplus : u + L ≤ 0 := by linarith
  have h0 : g u = 0 :=
    zero_of_large u (by rw [abs_of_nonpos hu]; linarith)
  have h1 : g (u-L) = 0 :=
    zero_of_large (u-L) (by rw [abs_of_nonpos hminus]; linarith)
  have h2 : g (u+L) = 0 :=
    zero_of_large (u+L) (by rw [abs_of_nonpos hplus]; linarith)
  simp [detectorThreeTap, h0, h1, h2]

theorem detectorThreeTap_twoShift_boundary
    {g : ℝ → ℝ} {eps L : ℝ}
    (hL : 0 < L)
    (hshort : ∀ u : ℝ, g u ≠ 0 → |u| < L) :
    detectorThreeTap g eps L (2*L) = 0 :=
  detectorThreeTap_vanishes_on_far_right hL hshort (le_refl _)

theorem detectorThreeTap_physical_far_right
    {R lam mu t eps u : ℝ}
    (hR : 0 < R) (hRone : R < 1) (ht : 200 ≤ t)
    (hfar : 2 * Real.log 2 ≤ u) :
    detectorThreeTap
      (quarticFourPhysicalDetector R lam mu t)
      eps (Real.log 2) u = 0 := by
  exact detectorThreeTap_vanishes_on_far_right
    (by positivity)
    (quarticFourPhysicalDetector_short_of_twoHundred hR hRone ht)
    hfar

theorem detectorThreeTap_physical_first_and_far
    {R lam mu t eps : ℝ}
    (hR : 0 < R) (hRone : R < 1) (ht : 200 ≤ t) :
    detectorThreeTap
      (quarticFourPhysicalDetector R lam mu t)
      eps (Real.log 2) (Real.log 2)
      = eps * quarticFourPhysicalDetector R lam mu t 0
    ∧
    detectorThreeTap
      (quarticFourPhysicalDetector R lam mu t)
      eps (Real.log 2) (2 * Real.log 2) = 0 := by
  constructor
  · exact quarticFourPhysicalDetector_threeTap_firstPrime hR hRone ht
  · exact detectorThreeTap_physical_far_right hR hRone ht (le_refl _)

end Synthesis
