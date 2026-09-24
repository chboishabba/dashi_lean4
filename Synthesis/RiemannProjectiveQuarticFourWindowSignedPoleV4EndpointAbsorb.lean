import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleRvMFourth
import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleHorizontalFourth
import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleLocalRemainderBounds

/-!
# RH V4 endpoint weld and explicit local ABSORB interface

The V4 theorem is naturally stated on the literal Zeta23 half-open window

  (t-r,t+r],

whereas the local fourth-angular carrier uses the closed normalized condition
`|gamma-t| <= r`.  This file pays that convention mismatch explicitly.

For the quartic weight `(gamma-t)^4`, the SameOrd(t) exclusion is invisible
because the weight vanishes at gamma=t.  The only remaining carrier difference
is therefore the left endpoint gamma=t-r.

For every finite exhaustion index n with r<n we obtain the exact identity

  V4_closed(n) = V4_RvM(t,r) + LeftAtom(n).

No generic-position choice is made and no endpoint zero is discarded.

The second half of the file exposes the final local absorption budget with every
currently-paid coefficient visible.  It deliberately does not claim the final
numeric inequality: that is the remaining Clay-facing test.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Interval Real

namespace Synthesis

def quarticSignedPoleLocalHalfWidth
    (t eta : ℝ) : ℝ :=
  eta * (t/16)

def quarticSignedPoleVerticalFourthZeroTerm
    (t : ℝ) (rho : Zeros) : ℝ :=
  ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
    * ((rho : ℂ).im - t)^4

theorem quarticSignedPoleLocal_iff_closed_ordinate_window
    {t eta : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (rho : Zeros) :
    quarticSignedPoleLocal t eta rho
      ↔
    t - quarticSignedPoleLocalHalfWidth t eta
        <= (rho : ℂ).im
      ∧
    (rho : ℂ).im
        <= t + quarticSignedPoleLocalHalfWidth t eta := by
  unfold quarticSignedPoleLocal
    quarticSignedPoleNormalizedOrdinateOffset
    quarticSignedPoleLocalHalfWidth
  have hr : 0 < t/16 := by positivity
  rw [abs_div, abs_of_pos hr, div_le_iff₀ hr, abs_le]
  constructor <;> intro h <;> constructor <;> linarith

/--
The SameOrd guard in the original local vertical carrier is algebraically
irrelevant for the fourth weight.
-/
theorem QuarticFourSignedPolePair.literalLocalVerticalFourthZeroMomentAt_eq_allLocal
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalVerticalFourthZeroMomentAt eta n
      =
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleLocal t eta rho then
        quarticSignedPoleVerticalFourthZeroTerm t rho
      else
        0 := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalVerticalFourthZeroMomentAt
    quarticSignedPoleVerticalFourthZeroTerm
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · simp [hl, hoff]
    · have hsame : rho ∈ (SameOrd t : Set Zeros) := by
        simpa only [Set.mem_compl_iff, not_not] using hoff
      change (rho : ℂ).im = t at hsame
      simp [hl, hoff, hsame]
  · simp [hl]

def QuarticFourSignedPolePair.literalLocalVerticalFourthHalfOpenAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  let r := quarticSignedPoleLocalHalfWidth t eta
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if t-r < (rho : ℂ).im ∧ (rho : ℂ).im <= t+r then
        quarticSignedPoleVerticalFourthZeroTerm t rho
      else
        0

def QuarticFourSignedPolePair.literalLocalVerticalFourthLeftEndpointAtomAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  let r := quarticSignedPoleLocalHalfWidth t eta
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if (rho : ℂ).im = t-r then
        quarticSignedPoleVerticalFourthZeroTerm t rho
      else
        0

theorem QuarticFourSignedPolePair.literalLocalVerticalFourthZeroMomentAt_eq_halfOpen_add_leftAtom
    {t eta : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalVerticalFourthZeroMomentAt eta n
      =
    W.literalLocalVerticalFourthHalfOpenAt eta n
      + W.literalLocalVerticalFourthLeftEndpointAtomAt eta n := by
  classical
  rw [W.literalLocalVerticalFourthZeroMomentAt_eq_allLocal]
  unfold QuarticFourSignedPolePair.literalLocalVerticalFourthHalfOpenAt
    QuarticFourSignedPolePair.literalLocalVerticalFourthLeftEndpointAtomAt
  let r := quarticSignedPoleLocalHalfWidth t eta
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  have hlocal :=
    quarticSignedPoleLocal_iff_closed_ordinate_window
      ht heta rho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · have hclosed := hlocal.mp hl
    by_cases hleft : (rho : ℂ).im = t-r
    · simp [r, hl, hleft]
    · have hopen : t-r < (rho : ℂ).im := by
        exact lt_of_le_of_ne hclosed.1 (Ne.symm hleft)
      simp [r, hl, hleft, hopen, hclosed.2]
  · have hnclosed : ¬
      (t-r <= (rho : ℂ).im ∧ (rho : ℂ).im <= t+r) := by
      simpa [r] using (not_congr hlocal).mp hl
    by_cases hleft : (rho : ℂ).im = t-r
    · exfalso
      apply hnclosed
      rw [hleft]
      constructor
      · exact le_rfl
      · have hr0 : 0 <= r := by
          dsimp [r, quarticSignedPoleLocalHalfWidth]
          positivity
        linarith
    · by_cases hopen :
        t-r < (rho : ℂ).im ∧ (rho : ℂ).im <= t+r
      · exfalso
        exact hnclosed ⟨hopen.1.le,hopen.2⟩
      · simp [r, hl, hleft, hopen]

theorem QuarticFourSignedPolePair.literalLocalVerticalFourthHalfOpenAt_eq_windowPair
    {t eta : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn :
      quarticSignedPoleLocalHalfWidth t eta < (n : ℝ)) :
    W.literalLocalVerticalFourthHalfOpenAt eta n
      =
    zetaWindowWeightedPair
      (t - quarticSignedPoleLocalHalfWidth t eta)
      (t + quarticSignedPoleLocalHalfWidth t eta)
      (quarticSignedPoleVerticalFourthWeight t) := by
  classical
  let r := quarticSignedPoleLocalHalfWidth t eta
  let A := t-r
  let B := t+r
  let F : Finset Zeros :=
    (centeredZeroFinset t n).filter
      (fun rho => A < (rho : ℂ).im ∧ (rho : ℂ).im <= B)
  let G : Finset ℂ :=
    (zetaZeroConfig.finite_window A B).toFinset
  have hr0 : 0 <= r := by
    dsimp [r, quarticSignedPoleLocalHalfWidth]
    positivity
  have hmap :
      F.image (fun rho : Zeros => (rho : ℂ)) = G := by
    ext z
    simp only [Finset.mem_image, Finset.mem_filter,
      Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨rho,⟨hrho,hwin⟩,rfl⟩
      exact ⟨rho.2,hwin.1,hwin.2⟩
    · intro hz
      let rho : Zeros := ⟨z,hz.1⟩
      have hcenter : rho ∈ centeredZeroFinset t n := by
        apply (mem_centeredZeroFinset_iff t n rho).2
        constructor
        · dsimp [rho,A] at hz ⊢
          linarith
        · dsimp [rho,B] at hz ⊢
          linarith
      refine ⟨rho,?_,rfl⟩
      exact ⟨hcenter,by simpa [rho,A,B] using hz.2⟩
  unfold QuarticFourSignedPolePair.literalLocalVerticalFourthHalfOpenAt
    zetaWindowWeightedPair
  rw [finsum_mem_eq_finite_toFinset_sum _
    (zetaZeroConfig.finite_window A B)]
  change
    (∑ rho ∈ centeredZeroFinset t n,
      if A < (rho : ℂ).im ∧ (rho : ℂ).im <= B then
        quarticSignedPoleVerticalFourthZeroTerm t rho
      else 0)
      =
    ∑ z ∈ G,
      (zetaZeroConfig.mult z : ℝ)
        * quarticSignedPoleVerticalFourthWeight t z.im
  rw [← Finset.sum_filter]
  change
    (∑ rho ∈ F, quarticSignedPoleVerticalFourthZeroTerm t rho)
      =
    ∑ z ∈ G,
      (zetaZeroConfig.mult z : ℝ)
        * quarticSignedPoleVerticalFourthWeight t z.im
  rw [← hmap, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro rho hrho
    rfl
  · intro a ha b hb hab
    exact Subtype.ext hab

/--
Exact finite V4 carrier weld.

The only difference between the closed local angular carrier and the literal
half-open RvM carrier is the explicit left endpoint atom.
-/
theorem QuarticFourSignedPolePair.literalLocalVerticalFourthDiscrepancy_eq_rvm_add_leftAtom
    {t eta : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn :
      quarticSignedPoleLocalHalfWidth t eta < (n : ℝ)) :
    W.literalLocalVerticalFourthZeroMomentAt eta n
      - quarticSignedPoleLocalMuVerticalFourthMoment t eta
      =
    quarticSignedPoleRvMVerticalFourthDiscrepancy
      t (quarticSignedPoleLocalHalfWidth t eta)
      +
    W.literalLocalVerticalFourthLeftEndpointAtomAt eta n := by
  let r := quarticSignedPoleLocalHalfWidth t eta
  have hr0 : 0 <= r := by
    dsimp [r, quarticSignedPoleLocalHalfWidth]
    positivity
  rw [W.literalLocalVerticalFourthZeroMomentAt_eq_halfOpen_add_leftAtom
      ht heta]
  rw [W.literalLocalVerticalFourthHalfOpenAt_eq_windowPair
      ht heta n hn]
  unfold quarticSignedPoleRvMVerticalFourthDiscrepancy
    zetaWindowMinusMuPair
    quarticSignedPoleLocalMuVerticalFourthMoment
  have hAB : t-r <= t+r := by linarith
  rw [intervalIntegral.integral_of_le hAB]
  ring

def QuarticFourSignedPolePair.literalLocalVerticalFourthLeftEndpointMultiplicityAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℕ := by
  classical
  let r := quarticSignedPoleLocalHalfWidth t eta
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if (rho : ℂ).im = t-r then
        zetaZeroConfig.mult (rho : ℂ)
      else 0

theorem QuarticFourSignedPolePair.literalLocalVerticalFourthLeftEndpointAtomAt_eq
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalVerticalFourthLeftEndpointAtomAt eta n
      =
    quarticSignedPoleLocalHalfWidth t eta ^ 4
      *
    (W.literalLocalVerticalFourthLeftEndpointMultiplicityAt eta n : ℝ) := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalVerticalFourthLeftEndpointAtomAt
    QuarticFourSignedPolePair.literalLocalVerticalFourthLeftEndpointMultiplicityAt
    quarticSignedPoleVerticalFourthZeroTerm
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  let r := quarticSignedPoleLocalHalfWidth t eta
  by_cases h : (rho : ℂ).im = t-r
  · simp [h, r]
    ring
  · simp [h]

/--
The endpoint atom is nonnegative, so the exact weld immediately compiles V4
and an endpoint multiplicity estimate into the closed local vertical bound.
-/
theorem QuarticFourSignedPolePair.literalLocalVerticalFourthDiscrepancy_abs_upper_of_rvm_and_endpoint
    {t eta EV M : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn :
      quarticSignedPoleLocalHalfWidth t eta < (n : ℝ))
    (hV :
      |quarticSignedPoleRvMVerticalFourthDiscrepancy
        t (quarticSignedPoleLocalHalfWidth t eta)| <= EV)
    (hM :
      (W.literalLocalVerticalFourthLeftEndpointMultiplicityAt eta n : ℝ)
        <= M) :
    W.literalLocalVerticalFourthZeroMomentAt eta n
      - quarticSignedPoleLocalMuVerticalFourthMoment t eta
      <=
    EV + quarticSignedPoleLocalHalfWidth t eta ^ 4 * M := by
  rw [W.literalLocalVerticalFourthDiscrepancy_eq_rvm_add_leftAtom
      ht heta n hn]
  rw [W.literalLocalVerticalFourthLeftEndpointAtomAt_eq]
  have hvr :
      quarticSignedPoleRvMVerticalFourthDiscrepancy
        t (quarticSignedPoleLocalHalfWidth t eta)
      <= EV :=
    (le_abs_self _).trans hV
  have hr4 :
      0 <= quarticSignedPoleLocalHalfWidth t eta ^ 4 := by positivity
  have hm :=
    mul_le_mul_of_nonneg_left hM hr4
  linarith


/--
The explicit left-endpoint multiplicity is bounded by the literal one-unit
Zeta23 window ending at that endpoint.  This is deliberately a counting
theorem, not a generic-position assumption.
-/
theorem QuarticFourSignedPolePair.literalLocalVerticalFourthLeftEndpointMultiplicityAt_le_unitWindowN
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalVerticalFourthLeftEndpointMultiplicityAt eta n
      <=
    zetaZeroConfig.N
      (t - quarticSignedPoleLocalHalfWidth t eta - 1)
      (t - quarticSignedPoleLocalHalfWidth t eta) := by
  classical
  let r := quarticSignedPoleLocalHalfWidth t eta
  let A : ℝ := t-r
  let F : Finset Zeros :=
    (centeredZeroFinset t n).filter
      (fun rho => (rho : ℂ).im = A)
  let s : Set ℂ :=
    (fun rho : Zeros => (rho : ℂ)) '' (↑F : Set Zeros)
  have hsWindow :
      s ⊆ zetaZeroConfig.window (A-1) A := by
    intro z hz
    rcases hz with ⟨rho,hrho,rfl⟩
    have him : (rho : ℂ).im = A :=
      (Finset.mem_filter.mp hrho).2
    exact ⟨rho.2, by linarith [him], by linarith [him]⟩
  have hmono :=
    zetaZeroConfig.finsum_mult_mono
      (A-1) A hsWindow subset_rfl
  have hsFinite : s.Finite :=
    Set.Finite.image F.finite_toSet _
  have hsum :
      W.literalLocalVerticalFourthLeftEndpointMultiplicityAt eta n
        =
      ∑ᶠ z ∈ s, zetaZeroConfig.mult z := by
    unfold
      QuarticFourSignedPolePair.literalLocalVerticalFourthLeftEndpointMultiplicityAt
    change
      (∑ rho ∈ centeredZeroFinset t n,
        if (rho : ℂ).im = A then zetaZeroConfig.mult (rho : ℂ) else 0)
        =
      ∑ᶠ z ∈ s, zetaZeroConfig.mult z
    rw [← Finset.sum_filter]
    change
      (∑ rho ∈ F, zetaZeroConfig.mult (rho : ℂ))
        =
      ∑ᶠ z ∈ s, zetaZeroConfig.mult z
    rw [finsum_mem_eq_finite_toFinset_sum _ hsFinite]
    have himage :
        hsFinite.toFinset
          =
        F.image (fun rho : Zeros => (rho : ℂ)) := by
      ext z
      simp [s]
    rw [himage, Finset.sum_image]
    intro a ha b hb hab
    exact Subtype.ext hab
  rw [hsum]
  simpa [A,r] using hmono

theorem QuarticFourSignedPolePair.literalLocalVerticalFourthLeftEndpointAtomAt_le_unitWindow
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalVerticalFourthLeftEndpointAtomAt eta n
      <=
    quarticSignedPoleLocalHalfWidth t eta ^ 4
      *
    (zetaZeroConfig.N
      (t - quarticSignedPoleLocalHalfWidth t eta - 1)
      (t - quarticSignedPoleLocalHalfWidth t eta) : ℝ) := by
  rw [W.literalLocalVerticalFourthLeftEndpointAtomAt_eq]
  have hN :=
    W.literalLocalVerticalFourthLeftEndpointMultiplicityAt_le_unitWindowN
      (eta:=eta) n
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast hN)
    (by positivity)


/-!
## Orientation firewall against the literal G3 quartic source

The exact joint quartic source has the opposite fourth-angular orientation
from the naive ABSORB reading.  Pointwise,

  P_G3(rho)
    = m_rho * S(W) / (6 r^6)
        * (a_rho^4 - Re(a_rho+i delta_rho)^4).

Thus an UPPER bound on the fourth-angular statistic produces a LOWER bound on
the joint quartic polynomial.  It cannot by itself be substituted for the
upper cone/source budget used by G3.

This identity is the fail-fast test for the V4/H4 recut.
-/

theorem QuarticFourSignedPolePair.literalJointQuarticPolynomial_eq_horizontalFourth_sub_fourthPhase
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.literalJointQuarticPolynomial rho
      =
    (((zetaZeroConfig).mult (rho : ℂ) : ℝ)
        * W.targetStrength
        / (6 * (t/16)^6))
      *
    (heightOf rho^4
      - quarticSignedPolePhysicalFourthPhaseReal t rho) := by
  unfold QuarticFourSignedPolePair.literalJointQuarticPolynomial
    quarticSignedPolePhysicalFourthPhaseReal
    quarticSignedPoleFourthPhaseReal
  field_simp [show t/16 ≠ 0 by positivity]
  ring

theorem QuarticFourSignedPolePair.literalJointQuarticPolynomial_ge_of_fourthPhase_le
    {t B : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hphase :
      quarticSignedPolePhysicalFourthPhaseReal t rho <= B) :
    (((zetaZeroConfig).mult (rho : ℂ) : ℝ)
        * W.targetStrength
        / (6 * (t/16)^6))
      * (heightOf rho^4 - B)
      <=
    W.literalJointQuarticPolynomial rho := by
  rw [W.literalJointQuarticPolynomial_eq_horizontalFourth_sub_fourthPhase
      ht]
  have hcoef :
      0 <=
      ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
        * W.targetStrength
        / (6 * (t/16)^6) := by
    positivity
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_left hphase (heightOf rho^4))
    hcoef

/--
Direction check: the V4/H4 upper estimate is naturally a lower-source
producer after the exact G3 scaling identity.  Any upper-source ABSORB theorem
must therefore obtain a lower fourth-angular estimate, exploit additional
signed cancellation, or use a different exact normal form.
-/
theorem QuarticFourSignedPolePair.fourthAngularUpperBound_has_lowerG3Orientation
    {t B : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hphase :
      quarticSignedPolePhysicalFourthPhaseReal t rho <= B) :
    (((zetaZeroConfig).mult (rho : ℂ) : ℝ)
        * W.targetStrength
        / (6 * (t/16)^6))
      * (heightOf rho^4 - B)
      <=
    W.literalJointQuarticPolynomial rho :=
  W.literalJointQuarticPolynomial_ge_of_fourthPhase_le
    ht rho hphase


/-!
## Same-carrier finite orientation identity

Sum the pointwise orientation firewall before taking any absolute values.  This
keeps the local exact G3 polynomial, the fourth-angular zero statistic, and the
horizontal a^4 mass on the identical centered finite carrier.
-/

def QuarticFourSignedPolePair.literalLocalHorizontalFourthMassAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleLocal t eta rho then
        if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
          ((zetaZeroConfig).mult (rho : ℂ) : ℝ) * heightOf rho^4
        else
          0
      else
        0

def QuarticFourSignedPolePair.literalLocalJointQuarticPolynomialAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleLocal t eta rho then
        if _h : rho ∈ ((SameOrd t)ᶜ : Set Zeros) then
          W.literalJointQuarticPolynomial rho
        else
          0
      else
        0

theorem QuarticFourSignedPolePair.literalLocalJointQuarticPolynomialAt_eq_scaled_mass_sub_fourthPhase
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalJointQuarticPolynomialAt eta n
      =
    (W.targetStrength / (6 * (t/16)^6))
      *
    (W.literalLocalHorizontalFourthMassAt eta n
      - W.literalLocalFourthPhaseMomentAt eta n) := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalJointQuarticPolynomialAt
    QuarticFourSignedPolePair.literalLocalHorizontalFourthMassAt
    QuarticFourSignedPolePair.literalLocalFourthPhaseMomentAt
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · simp [hl, hoff]
      rw [W.literalJointQuarticPolynomial_eq_horizontalFourth_sub_fourthPhase
        ht rho]
      ring
    · simp [hl, hoff]
  · simp [hl]

def QuarticFourSignedPolePair.literalLocalOffOrdExactAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleLocal t eta rho then
        W.literalOffOrdSource rho
      else
        0

def QuarticFourSignedPolePair.literalLocalJointQuarticRemainderAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℝ := by
  classical
  exact
    ∑ rho ∈ centeredZeroFinset t n,
      if quarticSignedPoleLocal t eta rho then
        W.literalJointQuarticRemainderOffOrd rho
      else
        0

theorem QuarticFourSignedPolePair.literalLocalOffOrdExactAt_eq_polynomial_add_remainder
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalOffOrdExactAt eta n
      =
    W.literalLocalJointQuarticPolynomialAt eta n
      + W.literalLocalJointQuarticRemainderAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalOffOrdExactAt
    QuarticFourSignedPolePair.literalLocalJointQuarticPolynomialAt
    QuarticFourSignedPolePair.literalLocalJointQuarticRemainderAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · have hsrc :=
        W.literalOffOrdSource_eq_polynomial_add_remainderOffOrd
          ht rho
      simp [hl, hoff,
        QuarticFourSignedPolePair.literalOffOrdSource,
        QuarticFourSignedPolePair.literalJointQuarticRemainderOffOrd]
        at hsrc ⊢
      exact hsrc
    · simp [hl, hoff,
        QuarticFourSignedPolePair.literalOffOrdSource,
        QuarticFourSignedPolePair.literalJointQuarticRemainderOffOrd]
  · simp [hl]

theorem QuarticFourSignedPolePair.literalLocalJointQuarticRemainderAt_le_debt
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalJointQuarticRemainderAt eta n
      <= W.literalLocalRemainderDebtAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalJointQuarticRemainderAt
    QuarticFourSignedPolePair.literalLocalRemainderDebtAt
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · simp [hl, le_abs_self]
  · simp [hl]

theorem QuarticFourSignedPolePair.literalLocalOffOrdExactAt_le_scaled_mass_sub_fourthPhase_add_remainder
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalOffOrdExactAt eta n
      <=
    (W.targetStrength / (6 * (t/16)^6))
      *
    (W.literalLocalHorizontalFourthMassAt eta n
      - W.literalLocalFourthPhaseMomentAt eta n)
      +
    W.literalLocalRemainderDebtAt eta n := by
  rw [W.literalLocalOffOrdExactAt_eq_polynomial_add_remainder
      ht]
  rw [W.literalLocalJointQuarticPolynomialAt_eq_scaled_mass_sub_fourthPhase
      ht]
  exact add_le_add_left
    (W.literalLocalJointQuarticRemainderAt_le_debt
      (eta:=eta) n) _

/--
The exact finite off-ordinate source splits into this local carrier plus the
already-existing signed FarExact lane.
-/
theorem QuarticFourSignedPolePair.literalOffOrdExactAt_eq_local_add_farExact
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalOffOrdExactAt n
      =
    W.literalLocalOffOrdExactAt eta n
      + W.literalFarExactAt eta n := by
  classical
  unfold QuarticFourSignedPolePair.literalOffOrdExactAt
    QuarticFourSignedPolePair.literalLocalOffOrdExactAt
    QuarticFourSignedPolePair.literalFarExactAt
    QuarticFourSignedPolePair.literalFarExactTerm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · have hnf : ¬ quarticSignedPoleFar t eta rho := by
      unfold quarticSignedPoleFar quarticSignedPoleLocal at *
      linarith
    simp [hl, hnf]
  · have hf : quarticSignedPoleFar t eta rho := by
      unfold quarticSignedPoleFar quarticSignedPoleLocal at *
      exact lt_of_not_ge hl
    simp [hl, hf]

theorem QuarticFourSignedPolePair.literalOffOrdExactAt_le_scaled_mass_sub_fourthPhase_add_remainder_add_far
    {t eta : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalOffOrdExactAt n
      <=
    (W.targetStrength / (6 * (t/16)^6))
      *
    (W.literalLocalHorizontalFourthMassAt eta n
      - W.literalLocalFourthPhaseMomentAt eta n)
      +
    W.literalLocalRemainderDebtAt eta n
      +
    W.literalFarExactAt eta n := by
  rw [W.literalOffOrdExactAt_eq_local_add_farExact]
  have hlocal :=
    W.literalLocalOffOrdExactAt_le_scaled_mass_sub_fourthPhase_add_remainder
      ht (eta:=eta) n
  linarith


/-!
## Correct-polarity lower fourth-angular compiler

The G3 upper source needs a LOWER bound on the local fourth-angular statistic.
V4 already provides this because its theorem is absolute.  H4 has a simple
unconditional lower envelope from the critical strip and the local ordinate
radius:

  a^2(a^2-6 delta^2) >= -3/2 r^2.

This produces the correct source orientation without any Montgomery input.
-/

def QuarticFourSignedPolePair.literalLocalMultiplicityAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta : ℝ) (n : ℕ) : ℕ :=
  ∑ rho ∈ centeredZeroFinset t n,
    if quarticSignedPoleLocal t eta rho then
      zetaZeroConfig.mult (rho : ℂ)
    else
      0

theorem QuarticFourSignedPolePair.literalLocalHorizontalFourthMassAt_le_sixteenth_multiplicity
    {t eta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.literalLocalHorizontalFourthMassAt eta n
      <=
    (1/16 : ℝ) * (W.literalLocalMultiplicityAt eta n : ℝ) := by
  classical
  unfold QuarticFourSignedPolePair.literalLocalHorizontalFourthMassAt
    QuarticFourSignedPolePair.literalLocalMultiplicityAt
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · have ha := zetaZero_height_abs_le_half rho
    have ha2 : heightOf rho^2 <= (1/4 : ℝ) := by
      nlinarith [sq_abs (heightOf rho), sq_nonneg (heightOf rho)]
    have ha4 : heightOf rho^4 <= (1/16 : ℝ) := by
      nlinarith [sq_nonneg (heightOf rho^2 - (1/4 : ℝ))]
    by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · simp [hl, hoff]
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left ha4
          (by positivity :
            0 <= ((zetaZeroConfig).mult (rho : ℂ) : ℝ)))
    · simp [hl, hoff]
      positivity
  · simp [hl]

theorem QuarticFourSignedPolePair.literalLocalHorizontalFourthCorrectionAt_lower
    {t eta : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    -(3/2 : ℝ)
        * quarticSignedPoleLocalHalfWidth t eta ^ 2
        * (W.literalLocalMultiplicityAt eta n : ℝ)
      <=
    W.literalLocalHorizontalFourthCorrectionAt eta n := by
  classical
  let r := quarticSignedPoleLocalHalfWidth t eta
  have hr0 : 0 <= r := by
    dsimp [r, quarticSignedPoleLocalHalfWidth]
    positivity
  unfold QuarticFourSignedPolePair.literalLocalHorizontalFourthCorrectionAt
    QuarticFourSignedPolePair.literalLocalMultiplicityAt
  rw [Nat.cast_sum, Finset.mul_sum]
  rw [show
      -(3/2 : ℝ) * r^2
        * (∑ rho ∈ centeredZeroFinset t n,
          (if quarticSignedPoleLocal t eta rho then
             (zetaZeroConfig.mult (rho : ℂ) : ℝ)
           else 0))
      =
      ∑ rho ∈ centeredZeroFinset t n,
        (-(3/2 : ℝ) * r^2)
          * (if quarticSignedPoleLocal t eta rho then
               (zetaZeroConfig.mult (rho : ℂ) : ℝ)
             else 0) by
        rw [Finset.mul_sum]]
  apply Finset.sum_le_sum
  intro rho hrho
  by_cases hl : quarticSignedPoleLocal t eta rho
  · have hclosed :=
      (quarticSignedPoleLocal_iff_closed_ordinate_window
        ht heta rho).mp hl
    have hdeltaAbs :
        |(rho : ℂ).im - t| <= r := by
      rw [abs_le]
      constructor <;> dsimp [r] at hclosed ⊢ <;> linarith
    have hd2 :
        ((rho : ℂ).im-t)^2 <= r^2 := by
      nlinarith [sq_abs ((rho : ℂ).im-t),
        sq_nonneg ((rho : ℂ).im-t)]
    have ha := zetaZero_height_abs_le_half rho
    have ha2 : heightOf rho^2 <= (1/4 : ℝ) := by
      nlinarith [sq_abs (heightOf rho), sq_nonneg (heightOf rho)]
    by_cases hoff : rho ∈ ((SameOrd t)ᶜ : Set Zeros)
    · have hterm :
        -(3/2 : ℝ) * r^2
          <=
        heightOf rho^2
          * (heightOf rho^2 - 6*((rho : ℂ).im-t)^2) := by
        have ha20 : 0 <= heightOf rho^2 := sq_nonneg _
        have hd20 : 0 <= ((rho : ℂ).im-t)^2 := sq_nonneg _
        nlinarith
      simp [hl, hoff]
      exact mul_le_mul_of_nonneg_right hterm (by positivity)
    · simp [hl, hoff]
      have hnon :
          -(3/2 : ℝ) * r^2
            * ((zetaZeroConfig).mult (rho : ℂ) : ℝ) <= 0 := by
        positivity
      exact hnon
  · simp [hl]

theorem QuarticFourSignedPolePair.literalLocalVerticalFourthDiscrepancy_ge_neg_rvm
    {t eta EV : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn :
      quarticSignedPoleLocalHalfWidth t eta < (n : ℝ))
    (hV :
      |quarticSignedPoleRvMVerticalFourthDiscrepancy
        t (quarticSignedPoleLocalHalfWidth t eta)| <= EV) :
    -EV
      <=
    W.literalLocalVerticalFourthZeroMomentAt eta n
      - quarticSignedPoleLocalMuVerticalFourthMoment t eta := by
  rw [W.literalLocalVerticalFourthDiscrepancy_eq_rvm_add_leftAtom
      ht heta n hn]
  have hv :
      -EV <=
      quarticSignedPoleRvMVerticalFourthDiscrepancy
        t (quarticSignedPoleLocalHalfWidth t eta) :=
    (abs_le.mp hV).1
  have hatom :
      0 <= W.literalLocalVerticalFourthLeftEndpointAtomAt eta n := by
    rw [W.literalLocalVerticalFourthLeftEndpointAtomAt_eq]
    positivity
  linarith

theorem QuarticFourSignedPolePair.literalLocalCenteredFourthAngularAt_lower
    {t eta EV : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn :
      quarticSignedPoleLocalHalfWidth t eta < (n : ℝ))
    (hV :
      |quarticSignedPoleRvMVerticalFourthDiscrepancy
        t (quarticSignedPoleLocalHalfWidth t eta)| <= EV) :
    -EV
      -
    (3/2 : ℝ)
      * quarticSignedPoleLocalHalfWidth t eta ^ 2
      * (W.literalLocalMultiplicityAt eta n : ℝ)
      <=
    W.literalLocalCenteredFourthAngularAt eta n := by
  rw [W.literalLocalCenteredFourthAngularAt_eq]
  have hv :=
    W.literalLocalVerticalFourthDiscrepancy_ge_neg_rvm
      ht heta n hn hV
  have hh :=
    W.literalLocalHorizontalFourthCorrectionAt_lower
      ht heta n
  linarith

/--
Correct-polarity explicit local G3 upper bound.

Unlike the earlier candidate ABSORB surface, this theorem is actually oriented
toward the literal G3 upper-source compiler.  It needs only:
* the absolute V4 estimate EV;
* one bound M on the literal local multiplicity.

The endpoint atom is favorable and disappears from the debt.
-/
theorem QuarticFourSignedPolePair.literalOffOrdExactAt_le_corrected_v4h4_budget
    {t eta EV M : ℝ}
    (ht : 0 < t)
    (heta : 0 <= eta)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn :
      quarticSignedPoleLocalHalfWidth t eta < (n : ℝ))
    (hV :
      |quarticSignedPoleRvMVerticalFourthDiscrepancy
        t (quarticSignedPoleLocalHalfWidth t eta)| <= EV)
    (hM :
      (W.literalLocalMultiplicityAt eta n : ℝ) <= M) :
    W.literalOffOrdExactAt n
      <=
    (W.targetStrength / (6 * (t/16)^6))
      *
    (
      EV
        +
      ((1/16 : ℝ)
        + (3/2 : ℝ)
            * quarticSignedPoleLocalHalfWidth t eta ^ 2)
        * M
        -
      quarticSignedPoleLocalMuVerticalFourthMoment t eta
    )
      +
    W.literalLocalRemainderDebtAt eta n
      +
    W.literalFarExactAt eta n := by
  have hsource :=
    W.literalOffOrdExactAt_le_scaled_mass_sub_fourthPhase_add_remainder_add_far
      ht (eta:=eta) n
  have hmass :=
    W.literalLocalHorizontalFourthMassAt_le_sixteenth_multiplicity
      (eta:=eta) n
  have hang :=
    W.literalLocalCenteredFourthAngularAt_lower
      ht heta n hn hV
  have hcenter :
      W.literalLocalFourthPhaseMomentAt eta n
        =
      W.literalLocalCenteredFourthAngularAt eta n
        + quarticSignedPoleLocalMuVerticalFourthMoment t eta := by
    unfold QuarticFourSignedPolePair.literalLocalCenteredFourthAngularAt
    ring
  have hM0 :
      0 <= (W.literalLocalMultiplicityAt eta n : ℝ) := by positivity
  have hcoef :
      0 <= W.targetStrength / (6 * (t/16)^6) := by positivity
  have hinside :
      W.literalLocalHorizontalFourthMassAt eta n
        - W.literalLocalFourthPhaseMomentAt eta n
      <=
      EV
        +
      ((1/16 : ℝ)
        + (3/2 : ℝ)
            * quarticSignedPoleLocalHalfWidth t eta ^ 2)
        * M
        -
      quarticSignedPoleLocalMuVerticalFourthMoment t eta := by
    rw [hcenter]
    have hmM :=
      mul_le_mul_of_nonneg_left hM (by norm_num : (0:ℝ) <= 1/16)
    have hrM :=
      mul_le_mul_of_nonneg_left hM
        (by positivity :
          0 <= (3/2 : ℝ)
            * quarticSignedPoleLocalHalfWidth t eta ^ 2)
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hinside hcoef
  exact hsource.trans (by
    linarith)

/-!
## Fail-closed explicit ABSORB surface

This is a fail-closed candidate scalar surface, not yet a proved upper-source
budget.  V4 and H4 are paid upper-bound producers; the orientation firewall
above shows that their fourth-angular upper bound points toward a lower bound
for the leading G3 quartic polynomial.  Therefore the missing hsource premise
below is mathematically substantive until a lower angular estimate, additional
signed cancellation, or another exact normal form pays it.

The local sixth-order debt and FarExact stay on their existing literal finite
carriers.  FarExact is deliberately signed.
-/

def QuarticFourSignedPolePair.v4h4ExplicitAbsorbBudgetAt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eta EV M A0 : ℝ) (n : ℕ) : ℝ :=
  EV
    + quarticSignedPoleLocalHalfWidth t eta ^ 4 * M
    + (3/16 : ℝ) * A0 * Real.log (t+5)
    + W.literalLocalRemainderDebtAt eta n
    + W.literalFarExactAt eta n

def QuarticFourSignedPolePair.V4H4ExplicitAbsorb
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (eta EV M A0 : ℝ) : Prop :=
  ∃ eps : ℝ, 0 < eps ∧
    ∃ N : ℕ, ∀ n : ℕ, N <= n ->
      W.v4h4ExplicitAbsorbBudgetAt eta EV M A0 n
        <= W.compensationTargetThreshold rho - eps

theorem QuarticFourSignedPolePair.v4h4ExplicitAbsorb_expanded
    {t eta EV M A0 : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.V4H4ExplicitAbsorb rho eta EV M A0
      ↔
    ∃ eps : ℝ, 0 < eps ∧
      ∃ N : ℕ, ∀ n : ℕ, N <= n ->
        EV
          + quarticSignedPoleLocalHalfWidth t eta ^ 4 * M
          + (3/16 : ℝ) * A0 * Real.log (t+5)
          + W.literalLocalRemainderDebtAt eta n
          + W.literalFarExactAt eta n
          <=
        W.compensationTargetThreshold rho - eps := by
  rfl

/--
Pure scalar compiler for the remaining test: once the literal local exact
source has been bounded by the exposed V4/H4/sixth/FarExact budget, a strict
budget margin implies the old compensation target inequality.  This theorem
contains no hidden absolute value on FarExact.
-/
theorem QuarticFourSignedPolePair.v4h4ExplicitAbsorb_compiles_local_upper
    {t eta EV M A0 eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (n : ℕ)
    (hsource :
      W.literalOffOrdExactAt n
        <= W.v4h4ExplicitAbsorbBudgetAt eta EV M A0 n)
    (hbudget :
      W.v4h4ExplicitAbsorbBudgetAt eta EV M A0 n
        <= W.compensationTargetThreshold rho - eps) :
    W.literalOffOrdExactAt n
      <= W.compensationTargetThreshold rho - eps :=
  hsource.trans hbudget

end Synthesis
