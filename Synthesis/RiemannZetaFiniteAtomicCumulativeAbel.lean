import Synthesis.RiemannZetaFiniteAtomicAbel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Tail-sum = cumulative-count integral on the literal Zeta23 window

This closes the second half of the finite atomic Abel identity.

For one zero ordinate gamma in (A,B],

  integral_gamma^B phi'
    = integral_A^B 1_{gamma < x} phi'(x) dx.

The proof uses the exact identity

  1_{gamma < x} phi'(x)
    = phi'(x) - 1_{x <= gamma} phi'(x)

and Mathlib's interval-indicator theorem for the prefix [A,gamma].

Summing over the finite actual zero window and interchanging the finite sum
with the interval integral gives a strict cumulative count.  That strict count
equals Zeta23.Ncount(A,x) away from the finitely many zero ordinates, hence
almost everywhere.  Therefore

  sum_rho m_rho integral_(Im rho)^B phi'
    = integral_A^B phi'(x) Ncount(A,x) dx.

No Stieltjes approximation, ordering of zeros, or quadrature enters.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators Interval Real

namespace Synthesis

open Zeta23

private def strictWindowCountFinset
    (F : Finset ℂ) (x : ℝ) : ℝ :=
  ∑ rho ∈ F, (zetaZeroConfig.mult rho : ℝ) * if rho.im < x then 1 else 0

private theorem tailIntegral_eq_integral_strictIndicator
    {A B gamma : ℝ} {phi' : ℝ -> ℝ}
    (hgamma : gamma ∈ Set.Icc A B)
    (hint : IntervalIntegrable phi' volume A B) :
    (∫ x in gamma..B, phi' x)
      =
    ∫ x in A..B, (if gamma < x then phi' x else 0) := by
  have hpreInt :
      IntervalIntegrable
        (fun x => Set.indicator {x : ℝ | x ≤ gamma} phi' x)
        volume A B := by
    exact hint.indicator measurableSet_Iic
  have hprefix :
      (∫ x in A..B,
        Set.indicator {x : ℝ | x ≤ gamma} phi' x)
        =
      ∫ x in A..gamma, phi' x := by
    exact intervalIntegral.integral_indicator hgamma
  have hsplit :
      (∫ x in A..B, phi' x)
        =
      (∫ x in A..gamma, phi' x)
        + ∫ x in gamma..B, phi' x := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact hint.mono_set (by
        rw [Set.uIcc_of_le hgamma.2,
            Set.uIcc_of_le (hgamma.1.trans hgamma.2)]
        intro x hx
        exact ⟨hgamma.1.trans hx.1, hx.2⟩)
    · exact hint.mono_set (by
        rw [Set.uIcc_of_le hgamma.2,
            Set.uIcc_of_le (hgamma.1.trans hgamma.2)]
        intro x hx
        exact ⟨hgamma.1.trans hx.1, hx.2⟩)
  calc
    (∫ x in gamma..B, phi' x)
      =
    (∫ x in A..B, phi' x)
      - (∫ x in A..gamma, phi' x) := by linarith
    _ =
    (∫ x in A..B, phi' x)
      -
    (∫ x in A..B,
      Set.indicator {x : ℝ | x ≤ gamma} phi' x) := by
        rw [hprefix]
    _ =
    ∫ x in A..B,
      (phi' x
        - Set.indicator {x : ℝ | x ≤ gamma} phi' x) := by
      rw [intervalIntegral.integral_sub hint hpreInt]
    _ =
    ∫ x in A..B, (if gamma < x then phi' x else 0) := by
      apply intervalIntegral.integral_congr
      intro x hx
      by_cases h : x ≤ gamma
      · simp [Set.indicator, h, not_lt.mpr h]
      · have hlt : gamma < x := lt_of_not_ge h
        simp [Set.indicator, h, hlt]

private theorem strictWindowCountFinset_eq_Ncount_ae
    {A B : ℝ}
    (hAB : A ≤ B) :
    ∀ᵐ x ∂volume,
      x ∈ Set.Ioc A B ->
      strictWindowCountFinset
          (zetaZeroConfig.finite_window A B).toFinset x
        =
      (Ncount A x : ℝ) := by
  classical
  let F : Finset ℂ := (zetaZeroConfig.finite_window A B).toFinset
  let O : Set ℝ := Complex.im '' zetaZeroConfig.window A B
  have hOfin : O.Finite :=
    (zetaZeroConfig.finite_window A B).image _
  have hOzero : volume O = 0 :=
    hOfin.measure_zero volume
  have hnot : ∀ᵐ x ∂volume, x ∉ O :=
    measure_eq_zero_iff_ae_notMem.mp hOzero
  filter_upwards [hnot] with x hxnot hx
  rcases hx with ⟨hAx, hxB⟩
  have hAxle : A ≤ x := le_of_lt hAx
  have hfinx := zetaZeroConfig.finite_window A x
  let Fx : Finset ℂ := hfinx.toFinset

  have hfilter :
      F.filter (fun rho => rho.im < x) = Fx := by
    ext rho
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hrhoF, hrhox⟩
      exact ⟨hrhoF.1, hrhoF.2.1, le_of_lt hrhox⟩
    · intro hrhox
      have hrhoF :
          rho ∈ zetaZeroConfig.window A B := by
        exact ⟨hrhox.1, hrhox.2.1, hrhox.2.2.trans hxB⟩
      have hne : rho.im ≠ x := by
        intro heq
        apply hxnot
        exact ⟨rho, hrhoF, heq⟩
      exact ⟨hrhoF, lt_of_le_of_ne hrhox.2.2 hne⟩

  unfold strictWindowCountFinset
  rw [show (zetaZeroConfig.finite_window A B).toFinset = F by rfl]
  calc
    (∑ rho ∈ F,
      (zetaZeroConfig.mult rho : ℝ) * if rho.im < x then 1 else 0)
      =
    ∑ rho ∈ F.filter (fun rho => rho.im < x),
      (zetaZeroConfig.mult rho : ℝ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro rho hrho
        by_cases hlt : rho.im < x <;> simp [hlt]
    _ =
    ∑ rho ∈ Fx, (zetaZeroConfig.mult rho : ℝ) := by
      rw [hfilter]
    _ =
    (zetaZeroConfig.N A x : ℝ) := by
      unfold ZeroConfig.N
      rw [finsum_mem_eq_finite_toFinset_sum _ hfinx]
      push_cast
      rfl
    _ = (Ncount A x : ℝ) := by
      rw [zetaZeroConfig_N]

theorem zetaWindowWeightedTailIntegral_eq_cumulativeCountIntegral
    {A B : ℝ} {phi' : ℝ -> ℝ}
    (hAB : A ≤ B)
    (hint : IntervalIntegrable phi' volume A B) :
    zetaWindowWeightedTailIntegral A B phi'
      =
    ∫ x in A..B, phi' x * (Ncount A x : ℝ) := by
  classical
  let hfin : (zetaZeroConfig.window A B).Finite :=
    zetaZeroConfig.finite_window A B
  let F : Finset ℂ := hfin.toFinset

  have htail :
      zetaWindowWeightedTailIntegral A B phi'
        =
      ∑ rho ∈ F,
        (zetaZeroConfig.mult rho : ℝ)
          * (∫ x in rho.im..B, phi' x) := by
    unfold zetaWindowWeightedTailIntegral
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    rfl

  rw [htail]
  have hterm :
      ∀ rho ∈ F,
        (zetaZeroConfig.mult rho : ℝ)
          * (∫ x in rho.im..B, phi' x)
        =
      ∫ x in A..B,
        (zetaZeroConfig.mult rho : ℝ)
          * (if rho.im < x then phi' x else 0) := by
    intro rho hrho
    have hrhoSet :
        rho ∈ zetaZeroConfig.window A B := by
      simpa [F, hfin] using hrho
    have hrange : rho.im ∈ Set.Icc A B :=
      ⟨le_of_lt hrhoSet.2.1, hrhoSet.2.2⟩
    rw [tailIntegral_eq_integral_strictIndicator hrange hint,
        intervalIntegral.integral_const_mul]

  calc
    (∑ rho ∈ F,
      (zetaZeroConfig.mult rho : ℝ)
        * (∫ x in rho.im..B, phi' x))
      =
    ∑ rho ∈ F,
      ∫ x in A..B,
        (zetaZeroConfig.mult rho : ℝ)
          * (if rho.im < x then phi' x else 0) := by
          apply Finset.sum_congr rfl
          exact hterm
    _ =
    ∫ x in A..B,
      ∑ rho ∈ F,
        (zetaZeroConfig.mult rho : ℝ)
          * (if rho.im < x then phi' x else 0) := by
      rw [intervalIntegral.integral_finsetSum]
      intro rho hrho
      have hi :
          IntervalIntegrable
            (fun x => if rho.im < x then phi' x else 0)
            volume A B := by
        exact hint.indicator measurableSet_Ioi
      exact hi.const_mul _
    _ =
    ∫ x in A..B,
      phi' x * strictWindowCountFinset F x := by
      apply intervalIntegral.integral_congr
      intro x hx
      unfold strictWindowCountFinset
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho hrho
      by_cases hlt : rho.im < x <;> simp [hlt]
    _ =
    ∫ x in A..B, phi' x * (Ncount A x : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [strictWindowCountFinset_eq_Ncount_ae hAB] with x hxN hx
      rw [show F = (zetaZeroConfig.finite_window A B).toFinset by rfl,
          hxN hx]


theorem phi_mul_Ncount_intervalIntegrable
    {A B : ℝ} {phi' : ℝ -> ℝ}
    (hAB : A ≤ B)
    (hint : IntervalIntegrable phi' volume A B) :
    IntervalIntegrable
      (fun x => phi' x * (Ncount A x : ℝ))
      volume A B := by
  classical
  let F : Finset ℂ := (zetaZeroConfig.finite_window A B).toFinset
  have hterm :
      ∀ rho ∈ F,
        IntervalIntegrable
          (fun x =>
            (zetaZeroConfig.mult rho : ℝ)
              * (if rho.im < x then phi' x else 0))
          volume A B := by
    intro rho hrho
    have hi :
        IntervalIntegrable
          (fun x => if rho.im < x then phi' x else 0)
          volume A B := by
      exact hint.indicator measurableSet_Ioi
    exact hi.const_mul _
  have hsum :
      IntervalIntegrable
        (fun x =>
          ∑ rho ∈ F,
            (zetaZeroConfig.mult rho : ℝ)
              * (if rho.im < x then phi' x else 0))
        volume A B := by
    classical
    induction F using Finset.induction_on with
    | empty =>
        simpa using
          (intervalIntegrable_zero :
            IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume A B)
    | @insert rho F hrho ih =>
        have hρ := hterm rho (by simp)
        have hrest :
            IntervalIntegrable
              (fun x =>
                ∑ sigma ∈ F,
                  (zetaZeroConfig.mult sigma : ℝ)
                    * (if sigma.im < x then phi' x else 0))
              volume A B := by
          apply ih
          intro sigma hsigma
          exact hterm sigma (by simp [hsigma])
        simpa [Finset.sum_insert, hrho] using hρ.add hrest
  have hstrict :
      IntervalIntegrable
        (fun x => phi' x * strictWindowCountFinset F x)
        volume A B := by
    refine hsum.congr_ae ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with x hx
    unfold strictWindowCountFinset
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rho hrho
    by_cases hlt : rho.im < x <;> simp [hlt]
  refine hstrict.congr_ae ?_
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [strictWindowCountFinset_eq_Ncount_ae hAB] with x hxN hx
  rw [show F = (zetaZeroConfig.finite_window A B).toFinset by rfl,
      hxN hx]

end Synthesis
