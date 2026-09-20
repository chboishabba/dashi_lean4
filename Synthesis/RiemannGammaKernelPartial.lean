import Synthesis.RiemannGammaArchimedeanKernelGeometry
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite Gamma kernels and their exact geometric sum

The anchored digamma partial bracket corresponds to

  K_N(u) =
    exp(-|u|/2)
      + sum_{n<N} exp(-2(n+5/4)|u|).

For u != 0,

  K_N(u)
    = exp(-|u|/2) * (1-exp(-2|u|)^(N+1))
        / (1-exp(-2|u|)),

so K_N increases to

  K(u)=exp(-|u|/2)/(1-exp(-2|u|)).
-/

noncomputable section

open Filter
open scoped Real Topology

namespace Synthesis

def gammaKernelPartial (N : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-|u|/2)
    + ∑ n ∈ Finset.range N,
        Real.exp (-2 * ((n:ℝ)+5/4) * |u|)

theorem gammaKernelPartial_tail_geometric
    (N : ℕ) (u : ℝ) :
    (∑ n ∈ Finset.range N,
      Real.exp (-2 * ((n:ℝ)+5/4) * |u|))
      =
    Real.exp (-5*|u|/2)
      * ∑ n ∈ Finset.range N, (Real.exp (-2*|u|))^n := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Real.exp_nat_mul]
  rw [← Real.exp_add]
  congr 1
  ring

theorem gammaKernelPartial_closed
    {N : ℕ} {u : ℝ} (hu : u ≠ 0) :
    gammaKernelPartial N u
      =
    Real.exp (-|u|/2)
      * (1 - (Real.exp (-2*|u|))^(N+1))
        / (1 - Real.exp (-2*|u|)) := by
  have huabs : 0 < |u| := abs_pos.mpr hu
  have hq : Real.exp (-2*|u|) ≠ 1 := by
    have hlt : Real.exp (-2*|u|) < 1 := by
      exact Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  unfold gammaKernelPartial
  rw [gammaKernelPartial_tail_geometric]
  rw [geom_sum_eq (by exact hq)]
  have hexp :
      Real.exp (-5*|u|/2)
        = Real.exp (-|u|/2) * Real.exp (-2*|u|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  field_simp [hq]
  ring

theorem gammaKernelPartial_nonneg (N : ℕ) (u : ℝ) :
    0 <= gammaKernelPartial N u := by
  unfold gammaKernelPartial
  positivity

theorem gammaKernelPartial_le_arch
    {N : ℕ} {u : ℝ} (hu : u ≠ 0) :
    gammaKernelPartial N u <= gammaArchKernel |u| := by
  rw [gammaKernelPartial_closed hu]
  unfold gammaArchKernel
  have hs : 0 < |u| := abs_pos.mpr hu
  have hden : 0 < 1 - Real.exp (-2*|u|) :=
    gammaArchKernel_denom_pos hs
  have hpow : 0 <= (Real.exp (-2*|u|))^(N+1) := by positivity
  have hexp : 0 < Real.exp (-|u|/2) := Real.exp_pos _
  rw [div_le_div_iff_of_pos_right hden]
  nlinarith

theorem gammaKernelPartial_tendsto_arch
    {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun N => gammaKernelPartial N u)
      atTop (nhds (gammaArchKernel |u|)) := by
  rw [show gammaArchKernel |u|
      = Real.exp (-|u|/2) / (1-Real.exp (-2*|u|)) by rfl]
  have hs : 0 < |u| := abs_pos.mpr hu
  have hq0 : 0 <= Real.exp (-2*|u|) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2*|u|) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hpow :
      Tendsto (fun N : ℕ =>
        (Real.exp (-2*|u|))^(N+1))
        atTop (nhds 0) := by
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp
      (tendsto_add_atTop_nat 1)
  have hform :
      (fun N => gammaKernelPartial N u)
        =
      fun N =>
        Real.exp (-|u|/2)
          * (1-(Real.exp (-2*|u|))^(N+1))
            / (1-Real.exp (-2*|u|)) := by
    funext N
    exact gammaKernelPartial_closed hu
  rw [hform]
  convert
    (tendsto_const_nhds.mul
      (tendsto_const_nhds.sub hpow)).div_const
        (1-Real.exp (-2*|u|)) using 1 <;> ring

theorem gammaKernelPartial_centered_product_tendsto
    {h : ℝ → ℝ} (h0 : h 0 = 0) (t u : ℝ) :
    Tendsto
      (fun N =>
        h u * Real.cos (t*u) * gammaKernelPartial N u)
      atTop
      (nhds
        (h u * Real.cos (t*u) * gammaArchKernel |u|)) := by
  by_cases hu : u = 0
  · subst u
    simp [h0]
  · exact
      (gammaKernelPartial_tendsto_arch hu).const_mul
        (h u * Real.cos (t*u))

end Synthesis
