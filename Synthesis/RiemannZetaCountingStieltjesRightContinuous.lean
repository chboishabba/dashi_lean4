import Synthesis.RiemannZetaCountingStieltjesMeasure

/-!
# Right continuity of the literal Zeta23 cumulative count

For fixed A define

  C_A(x) = N(A, max A x).

Zeta23 gives local finiteness of every zero window.  For x >= A, the ordinates
of zeros in (x,x+1] therefore form a finite set S not containing x.  Its
complement is an open neighbourhood of x, so a sufficiently small right
neighbourhood contains no new zero ordinate.  Hence N(x,y)=0 there and
N(A,y)=N(A,x) by Ncount_add.

For x<A the max makes C_A locally constant trivially.

Thus C_A is right-continuous everywhere, so its Mathlib Stieltjes measure has
literal mass N(a,b) on every Ioc(a,b) above A, with no regularization residue.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Synthesis

open Zeta23

private def localFutureZeroOrdinates (x : ℝ) : Set ℝ :=
  Complex.im '' zetaZeroConfig.window x (x + 1)

private theorem localFutureZeroOrdinates_finite (x : ℝ) :
    (localFutureZeroOrdinates x).Finite := by
  unfold localFutureZeroOrdinates
  exact (zetaZeroConfig.finite_window x (x+1)).image _

private theorem self_not_mem_localFutureZeroOrdinates (x : ℝ) :
    x ∉ localFutureZeroOrdinates x := by
  rintro ⟨rho, hrho, hEq⟩
  unfold ZeroConfig.window at hrho
  have hlt : x < rho.im := hrho.2.1
  linarith

private theorem exists_right_zero_free_radius (x : ℝ) :
    ∃ eps : ℝ, 0 < eps ∧ eps <= 1 ∧
      ∀ y : ℝ, x < y -> y < x + eps ->
        y ∉ localFutureZeroOrdinates x := by
  have hfin := localFutureZeroOrdinates_finite x
  have hopen : IsOpen (localFutureZeroOrdinates x)ᶜ :=
    hfin.isClosed.isOpen_compl
  have hx :
      x ∈ (localFutureZeroOrdinates x)ᶜ := by
    simpa using self_not_mem_localFutureZeroOrdinates x
  have hnhds := hopen.mem_nhds hx
  rcases Metric.mem_nhds_iff.1 hnhds with ⟨d, hd, hball⟩
  let eps : ℝ := min d 1
  have heps : 0 < eps := by
    dsimp [eps]
    exact lt_min hd (by norm_num)
  have heps1 : eps <= 1 := min_le_right _ _
  refine ⟨eps, heps, heps1, ?_⟩
  intro y hxy hy
  have hdist : dist y x < d := by
    rw [Real.dist_eq]
    have hpos : 0 <= y-x := by linarith
    rw [abs_of_nonneg hpos]
    have hed : eps <= d := min_le_left _ _
    linarith
  have hyball : y ∈ Metric.ball x d := by
    simpa [dist_comm] using hdist
  exact hball hyball

private theorem Ncount_zero_of_no_future_ordinate
    {x y : ℝ}
    (hxy : x <= y)
    (hy1 : y <= x + 1)
    (havoid :
      ∀ z : ℝ, x < z -> z <= y ->
        z ∉ localFutureZeroOrdinates x) :
    Ncount x y = 0 := by
  have hzero : zerosIn x y = ∅ := by
    ext rho
    constructor
    · intro hrho
      exfalso
      have hz : IsNontrivialZero rho := hrho.1
      have hlo : x < rho.im := hrho.2.1
      have hhi : rho.im <= y := hrho.2.2
      have hcarrier : rho ∈ zetaZeroConfig.carrier := by
        rw [zetaZeroConfig_carrier]
        exact hz
      have hwin : rho ∈ zetaZeroConfig.window x (x+1) := by
        exact ⟨hcarrier, hlo, hhi.trans hy1⟩
      have himem : rho.im ∈ localFutureZeroOrdinates x :=
        ⟨rho, hwin, rfl⟩
      exact (havoid rho.im hlo hhi) himem
    · intro h
      simp at h
  unfold Ncount
  rw [hzero]
  simp

theorem zetaCumulativeCountFrom_rightContinuous
    (A x : ℝ) :
    ContinuousWithinAt
      (zetaCumulativeCountFrom A) (Set.Ici x) x := by
  by_cases hxA : x < A
  · have hIio : Set.Iio A ∈ 𝓝 x := Set.Iio_mem_nhds hxA
    have hev :
        zetaCumulativeCountFrom A
          =ᶠ[𝓝[Set.Ici x] x]
        fun _ => zetaCumulativeCountFrom A x := by
      filter_upwards [hIio, self_mem_nhdsWithin] with y hyA hyx
      unfold zetaCumulativeCountFrom
      rw [max_eq_left (le_of_lt hyA), max_eq_left hxA.le]
    exact continuousWithinAt_const.congr_of_eventuallyEq hev.symm
  · have hAx : A <= x := le_of_not_gt hxA
    obtain ⟨eps, heps, heps1, hfree⟩ :=
      exists_right_zero_free_radius x
    have hball : Metric.ball x eps ∈ 𝓝 x :=
      Metric.ball_mem_nhds x heps
    have hev :
        zetaCumulativeCountFrom A
          =ᶠ[𝓝[Set.Ici x] x]
        fun _ => zetaCumulativeCountFrom A x := by
      filter_upwards [hball, self_mem_nhdsWithin] with y hyball hyx
      have hxy : x <= y := hyx
      have hdist : |y-x| < eps := by
        have hb : dist y x < eps := by
          simpa [dist_comm] using hyball
        simpa [Real.dist_eq] using hb
      have hyUpper : y <= x + eps := by
        have hnon : 0 <= y-x := by linarith
        rw [abs_of_nonneg hnon] at hdist
        linarith
      have hy1 : y <= x+1 := by linarith
      have havoid :
          ∀ z : ℝ, x < z -> z <= y ->
            z ∉ localFutureZeroOrdinates x := by
        intro z hxz hzy
        exact hfree z hxz (lt_of_le_of_lt hzy (lt_of_le_of_lt hyUpper (by linarith)))
      have hzero :
          Ncount x y = 0 :=
        Ncount_zero_of_no_future_ordinate hxy hy1 havoid
      have hadd :=
        Ncount_add (a := A) (b := x) (c := y) hAx hxy
      unfold zetaCumulativeCountFrom
      rw [max_eq_right (hAx.trans hxy), max_eq_right hAx]
      rw [hadd, hzero]
      simp
    exact continuousWithinAt_const.congr_of_eventuallyEq hev.symm

theorem zetaCountingStieltjesFrom_apply_literal
    (A x : ℝ) :
    zetaCountingStieltjesFrom A x
      = zetaCumulativeCountFrom A x :=
  zetaCountingStieltjesFrom_apply_of_rightContinuous
    (zetaCumulativeCountFrom_rightContinuous A x)

theorem zetaCountingMeasureFrom_Ioc_literal
    {A a b : ℝ}
    (hAa : A <= a)
    (hab : a <= b) :
    zetaCountingMeasureFrom A (Set.Ioc a b)
      =
    ENNReal.ofReal (Ncount a b : ℝ) := by
  exact zetaCountingMeasureFrom_Ioc_eq_Ncount
    hAa hab
    (zetaCumulativeCountFrom_rightContinuous A a)
    (zetaCumulativeCountFrom_rightContinuous A b)


/--
Public zero-isolation form needed by the signed projective discrepancy consumer.

For every ordinate x there is a genuine right interval (x,x+eps] containing no
literal Zeta23 zero ordinates.  This is extracted only from local finiteness of
the actual zero carrier.
-/
theorem exists_right_zero_free_literal_window (x : ℝ) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      ∀ y : ℝ, x < y → y < x + eps →
        zetaZeroConfig.window x y = ∅ := by
  obtain ⟨eps, heps, heps1, hfree⟩ :=
    exists_right_zero_free_radius x
  refine ⟨eps, heps, heps1, ?_⟩
  intro y hxy hy
  ext rho
  constructor
  · intro hrho
    exfalso
    have him : rho.im ∈ localFutureZeroOrdinates x := by
      refine ⟨rho, ?_, rfl⟩
      exact ⟨hrho.1, hrho.2.1, hrho.2.2.trans (by linarith [heps1])⟩
    exact (hfree rho.im hrho.2.1 (lt_of_le_of_lt hrho.2.2 hy)) him
  · intro h
    simp at h

/-- Every such right zero-free interval has literal count zero. -/
theorem exists_right_zero_free_Ncount (x : ℝ) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      ∀ y : ℝ, x < y → y < x + eps →
        Ncount x y = 0 := by
  obtain ⟨eps, heps, heps1, hwin⟩ :=
    exists_right_zero_free_literal_window x
  refine ⟨eps, heps, heps1, ?_⟩
  intro y hxy hy
  unfold Ncount
  rw [show zerosIn x y = zetaZeroConfig.window x y by rfl,
      hwin y hxy hy]
  simp


end Synthesis
