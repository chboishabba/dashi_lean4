import Synthesis.MillenniumBSDOddEulerDirichletAgreement
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Tactic

/-!
# Holomorphy of the prime-to-2 BSD L-series in a concrete half-plane

The coarse coefficient bound |a_n| <= n^2 on odd n gives absolute
convergence for Re(s)>3.  We package the odd coefficients as an ordinary
L-series, bound its abscissa of absolute convergence by 3, and inherit
mathlib's generic holomorphy theorem.  Via the Euler/Dirichlet agreement this
is also a holomorphic realization of the actual prime-to-2 global Euler
product on that half-plane.
-/

namespace Synthesis.Millennium.BSD

noncomputable def cmOddCoefficient (n : ℕ) : ℂ :=
  if Odd n then (cmAllNCoefficient n : ℂ) else 0

@[simp] theorem cmOddCoefficient_zero :
    cmOddCoefficient 0 = 0 := by
  simp [cmOddCoefficient]

theorem cmOddDirichletSummand_eq_LSeriesTerm
    (s : ℂ) (n : ℕ) :
    cmOddDirichletSummand s n =
      LSeries.term cmOddCoefficient s n := by
  rw [LSeries.term_def₀ cmOddCoefficient_zero]
  simp [cmOddDirichletSummand, cmOddCoefficient]

theorem cmOddLSeries_eq_LSeries
    (s : ℂ) :
    cmOddLSeries s = LSeries cmOddCoefficient s := by
  unfold cmOddLSeries LSeries
  apply tsum_congr
  intro n
  exact cmOddDirichletSummand_eq_LSeriesTerm s n

theorem cmOddCoefficient_LSeriesSummable
    {s : ℂ} (hs : 3 < s.re) :
    LSeriesSummable cmOddCoefficient s := by
  unfold LSeriesSummable
  rw [← summable_congr
    (fun n => (cmOddDirichletSummand_eq_LSeriesTerm s n).symm)]
  exact cmOddDirichletSummand_summable hs

theorem cmOddCoefficient_abscissaOfAbsConv_le_three :
    LSeries.abscissaOfAbsConv cmOddCoefficient ≤ 3 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact cmOddCoefficient_LSeriesSummable (s := (y : ℂ)) (by simpa using hy)

theorem cmOddLSeries_analyticOn :
    AnalyticOn ℂ cmOddLSeries {s : ℂ | 3 < s.re} := by
  rw [show cmOddLSeries = LSeries cmOddCoefficient by
    funext s; exact cmOddLSeries_eq_LSeries s]
  exact (LSeries.LSeries_analyticOn cmOddCoefficient).mono (by
    intro s hs
    exact lt_of_le_of_lt cmOddCoefficient_abscissaOfAbsConv_le_three hs)

theorem cmOddLSeries_differentiableOn :
    DifferentiableOn ℂ cmOddLSeries {s : ℂ | 3 < s.re} :=
  cmOddLSeries_analyticOn.differentiableOn

theorem cmPrimeToTwoAnalyticEulerProduct_eq_LSeries
    {s : ℂ} (hs : 3 < s.re) :
    cmPrimeToTwoAnalyticEulerProduct s =
      LSeries cmOddCoefficient s := by
  rw [← cmOddLSeries_eq_LSeries s]
  exact (cmOddLSeries_eq_primeToTwoAnalyticEulerProduct hs).symm

theorem cmPrimeToTwoAnalyticEulerProduct_eq_cmOddLSeries
    {s : ℂ} (hs : 3 < s.re) :
    cmPrimeToTwoAnalyticEulerProduct s = cmOddLSeries s :=
  (cmOddLSeries_eq_primeToTwoAnalyticEulerProduct hs).symm

theorem cmPrimeToTwoAnalyticEulerProduct_locally_holomorphic
    {s : ℂ} (hs : 3 < s.re) :
    ∃ U ∈ 𝓝 s,
      EqOn cmPrimeToTwoAnalyticEulerProduct
        (LSeries cmOddCoefficient) U ∧
      AnalyticOn ℂ (LSeries cmOddCoefficient) U := by
  let U : Set ℂ := {z | 3 < z.re}
  refine ⟨U, ?_, ?_, ?_⟩
  · exact (isOpen_halfSpace_re_gt (3 : ℝ)).mem_nhds hs
  · intro z hz
    exact cmPrimeToTwoAnalyticEulerProduct_eq_LSeries hz
  · exact (LSeries.LSeries_analyticOn cmOddCoefficient).mono (by
      intro z hz
      exact lt_of_le_of_lt cmOddCoefficient_abscissaOfAbsConv_le_three hz)

theorem cmPrimeToTwoAnalyticEulerProduct_ne_zero_on_halfPlane
    {s : ℂ} (hs : 3 < s.re) :
    cmPrimeToTwoAnalyticEulerProduct s ≠ 0 :=
  cmPrimeToTwoAnalyticEulerProduct_ne_zero (by linarith)

end Synthesis.Millennium.BSD
