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
## Fail-closed explicit ABSORB surface

This is the exact scalar shape we now want to test.  V4 and H4 are paid
producers; the local sixth-order debt and FarExact stay on their existing
literal finite carriers.  FarExact is deliberately signed.
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
