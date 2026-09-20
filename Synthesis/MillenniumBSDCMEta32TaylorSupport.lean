import Synthesis.MillenniumBSDCMEta32QuarterFactor
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Literal Taylor support of the eta32 q-product

The q-product is analytic on the open unit disk.  Its exact quarter-turn
identity `f(iq)=i f(q)` therefore acts on the canonical Taylor coefficients

  c_n = f^(n)(0) / n!.

Using the native iterated-derivative scaling theorem,

  i^n c_n = i c_n.

Hence c_n=0 unless n ≡ 1 (mod 4).  This removes the final 'coefficient API'
qualification from the eta-side lacunarity statement.
-/

namespace Synthesis.Millennium.BSD

open Complex Set

noncomputable def cmEtaEulerProduct (q : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - q ^ (n + 1))

theorem cmEta32QProduct_eq_eulerProduct_composition (q : ℂ) :
    cmEta32QProduct q =
      q * (cmEtaEulerProduct (q ^ 4)) ^ 2 *
        (cmEtaEulerProduct (q ^ 8)) ^ 2 := by
  unfold cmEta32QProduct cmEtaEulerProduct
  simp_rw [← pow_mul]
  ring

theorem cmEtaEulerProduct_differentiableOn_unitDisk :
    DifferentiableOn ℂ cmEtaEulerProduct (Metric.ball 0 1) := by
  simpa [cmEtaEulerProduct] using
    ModularForm.differentiableOn_tprod_one_sub_pow

theorem pow_maps_unitDisk (m : ℕ) (hm : 0 < m) :
    MapsTo (fun q : ℂ => q ^ m) (Metric.ball 0 1) (Metric.ball 0 1) := by
  intro q hq
  simp only [Metric.mem_ball, dist_zero_right] at hq ⊢
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg q) hq hm.ne'

theorem cmEta32QProduct_differentiableOn_unitDisk :
    DifferentiableOn ℂ cmEta32QProduct (Metric.ball 0 1) := by
  intro q hq
  have hq4 : q ^ 4 ∈ Metric.ball (0 : ℂ) 1 :=
    pow_maps_unitDisk 4 (by norm_num) hq
  have hq8 : q ^ 8 ∈ Metric.ball (0 : ℂ) 1 :=
    pow_maps_unitDisk 8 (by norm_num) hq
  have hP4 : DifferentiableAt ℂ cmEtaEulerProduct (q ^ 4) :=
    (cmEtaEulerProduct_differentiableOn_unitDisk (q ^ 4) hq4).differentiableAt
      (Metric.isOpen_ball.mem_nhds hq4)
  have hP8 : DifferentiableAt ℂ cmEtaEulerProduct (q ^ 8) :=
    (cmEtaEulerProduct_differentiableOn_unitDisk (q ^ 8) hq8).differentiableAt
      (Metric.isOpen_ball.mem_nhds hq8)
  rw [cmEta32QProduct_eq_eulerProduct_composition]
  exact (((differentiableAt_id.mul
    ((hP4.comp q (by fun_prop)).pow 2)).mul
      ((hP8.comp q (by fun_prop)).pow 2))).differentiableWithinAt

theorem cmEta32QProduct_contDiffOn_unitDisk (n : ℕ) :
    ContDiffOn ℂ n cmEta32QProduct (Metric.ball 0 1) := by
  exact cmEta32QProduct_differentiableOn_unitDisk.contDiffOn Metric.isOpen_ball

noncomputable def cmEta32TaylorCoeff (n : ℕ) : ℂ :=
  iteratedDeriv n cmEta32QProduct 0 / n.factorial

theorem cmEta32QProduct_analyticAt_zero :
    AnalyticAt ℂ cmEta32QProduct 0 := by
  exact (cmEta32QProduct_differentiableOn_unitDisk.analyticOnNhd
    Metric.isOpen_ball) 0 (by simp)

theorem cmEta32_hasCanonicalTaylorSeriesAt_zero :
    HasFPowerSeriesAt cmEta32QProduct
      (FormalMultilinearSeries.ofScalars ℂ cmEta32TaylorCoeff) 0 := by
  simpa [cmEta32TaylorCoeff] using
    cmEta32QProduct_analyticAt_zero.hasFPowerSeriesAt

theorem cmEta32_iteratedDeriv_quarterTurn (n : ℕ) :
    Complex.I ^ n * iteratedDeriv n cmEta32QProduct 0 =
      Complex.I * iteratedDeriv n cmEta32QProduct 0 := by
  let s : Set ℂ := Metric.ball 0 1
  have h0 : (0 : ℂ) ∈ s := by simp [s]
  have huniq : UniqueDiffOn ℂ s := Metric.isOpen_ball.uniqueDiffOn
  have hcont : ContDiffOn ℂ n cmEta32QProduct s := by
    simpa [s] using cmEta32QProduct_contDiffOn_unitDisk n
  have hmap : MapsTo (fun q : ℂ => Complex.I * q) s s := by
    intro q hq
    simp only [s, Metric.mem_ball, dist_zero_right] at hq ⊢
    simpa using hq
  have hleft := iteratedDerivWithin_comp_const_smul
    (s := s) (x := (0 : ℂ)) h0 huniq hcont Complex.I hmap
  have heqfun :
      (fun q : ℂ => cmEta32QProduct (Complex.I * q)) =
        fun q : ℂ => Complex.I * cmEta32QProduct q := by
    funext q
    exact cmEta32QProduct_mul_I q
  have heq := congrArg
    (fun f : ℂ → ℂ => iteratedDerivWithin n f s 0) heqfun
  rw [hleft] at heq
  rw [iteratedDerivWithin_const_mul_field] at heq
  have hopen := Metric.isOpen_ball
  rw [iteratedDerivWithin_of_isOpen hopen h0,
      iteratedDerivWithin_of_isOpen hopen h0] at heq
  simpa using heq

theorem complex_I_pow_ne_I_of_mod_four_ne_one
    {n : ℕ} (h : n % 4 ≠ 1) :
    Complex.I ^ n ≠ Complex.I := by
  rw [Complex.I_pow_eq_pow_mod]
  interval_cases hn : n % 4 <;> simp [hn] at h ⊢

theorem cmEta32TaylorCoeff_eq_zero_of_mod_four_ne_one
    {n : ℕ} (h : n % 4 ≠ 1) :
    cmEta32TaylorCoeff n = 0 := by
  unfold cmEta32TaylorCoeff
  have hderiv := cmEta32_iteratedDeriv_quarterTurn n
  have hzero : iteratedDeriv n cmEta32QProduct 0 = 0 := by
    apply (mul_left_cancel₀
      (sub_ne_zero.mpr (complex_I_pow_ne_I_of_mod_four_ne_one h)))
    calc
      (Complex.I ^ n - Complex.I) *
          iteratedDeriv n cmEta32QProduct 0
        = Complex.I ^ n * iteratedDeriv n cmEta32QProduct 0 -
            Complex.I * iteratedDeriv n cmEta32QProduct 0 := by ring
      _ = 0 := by rw [hderiv]; ring
      _ = (Complex.I ^ n - Complex.I) * 0 := by ring
  rw [hzero]
  simp

end Synthesis.Millennium.BSD
