import Synthesis.RiemannGammaBracketAnchoredSeries
import Synthesis.RiemannGammaKernelPartial
import Synthesis.RiemannCosFTInversionAtZero

/-!
# Finite anchored Gamma responses equal finite time-domain kernels

For an even compactly supported C^2 taper h with h(0)=0, define

  Gamma_N(h,t)
    = (1/(2*pi)) * integral_x cosFT h (x-t) * B_N(x),

where B_N is the anchored digamma partial bracket.

Then exactly

  Gamma_N(h,t)
    = - integral_u h(u) cos(tu) K_N(u).

No limiting argument is used in this file; it is finite algebra plus the exact
Lorentzian convolution theorem.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance

def gammaRespPartial (N : ℕ) (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1/(2*Real.pi))
    * ∫ x : ℝ, cosFT h (x-t) * gammaBracketPartial N x

theorem integral_cosFT_shift_eq_zero
    {h : ℝ → ℝ}
    (hC2 : ContDiff ℝ 2 h)
    (hcompact : HasCompactSupport h)
    (heven : ∀ x, h (-x)=h x)
    (h0 : h 0 = 0) (t : ℝ) :
    (∫ x : ℝ, cosFT h (x-t)) = 0 := by
  have hbase :=
    integral_cosFT_centered_eq_zero hC2 hcompact heven h0
  have hshift :=
    integral_sub_right_eq_self (cosFT h) t
  simpa using hshift.trans hbase

theorem integral_cosFT_mul_gammaHeadIncrement
    {h : ℝ → ℝ}
    (hC2 : ContDiff ℝ 2 h)
    (hcompact : HasCompactSupport h)
    (heven : ∀ x, h (-x)=h x)
    (h0 : h 0 = 0) (t : ℝ) :
    (∫ x : ℝ,
      cosFT h (x-t) * gammaHeadIncrement x)
      =
    -2*Real.pi *
      ∫ u : ℝ,
        h u * Real.cos (t*u) * Real.exp (-|u|/2) := by
  unfold gammaHeadIncrement
  have hz := integral_cosFT_shift_eq_zero
    hC2 hcompact heven h0 t
  have hconv :=
    integral_cosFT_mul_digammaLorentzian
      hC2.continuous hcompact
      (a:=(1/4:ℝ)) (t:=t) (by norm_num)
  have hCos := cosFT_integrable hC2 hcompact
  have hshift : Integrable (fun x => cosFT h (x-t)) :=
    hCos.comp_sub_right t
  have hL := digammaLorentzian_integrable (show (0:ℝ)<1/4 by norm_num)
  have hprod : Integrable
      (fun x => cosFT h (x-t) * digammaLorentzian (1/4) x) :=
    hL.mul_of_bounded_right
      hshift
      (by
        obtain ⟨C,hC⟩ := hC2.continuous.bddAbove_range
        exact ⟨C, fun x => by positivity⟩)
  rw [integral_sub
    (hshift.const_mul (digammaLorentzian (1/4) 0))
    hprod]
  rw [integral_const_mul, hz, zero_mul, zero_sub, hconv]
  congr 2
  apply integral_congr
  intro u
  congr 1
  ring

theorem integral_cosFT_mul_gammaTailIncrement
    {h : ℝ → ℝ}
    (hC2 : ContDiff ℝ 2 h)
    (hcompact : HasCompactSupport h)
    (heven : ∀ x, h (-x)=h x)
    (h0 : h 0 = 0) (t : ℝ) (n : ℕ) :
    (∫ x : ℝ,
      cosFT h (x-t) * gammaTailIncrement n x)
      =
    -2*Real.pi *
      ∫ u : ℝ,
        h u * Real.cos (t*u)
          * Real.exp (-2*((n:ℝ)+5/4)*|u|) := by
  unfold gammaTailIncrement
  let a : ℝ := (n:ℝ)+5/4
  have ha : 0 < a := by dsimp [a]; positivity
  have hz := integral_cosFT_shift_eq_zero
    hC2 hcompact heven h0 t
  have hconv :=
    integral_cosFT_mul_digammaLorentzian
      hC2.continuous hcompact
      (a:=a) (t:=t) ha
  have hCos := cosFT_integrable hC2 hcompact
  have hshift : Integrable (fun x => cosFT h (x-t)) :=
    hCos.comp_sub_right t
  have hL := digammaLorentzian_integrable ha
  have hprod : Integrable
      (fun x => cosFT h (x-t) * digammaLorentzian a x) := by
    have hb :
        ∀ x, |cosFT h (x-t)|
          <= ∫ u : ℝ, |h u| := by
      intro x
      unfold cosFT
      calc
        |∫ u : ℝ, h u * Real.cos ((x-t)*u)|
            <= ∫ u : ℝ, |h u * Real.cos ((x-t)*u)| :=
          abs_integral_le_integral_abs
        _ <= ∫ u : ℝ, |h u| := by
          apply integral_mono
          · exact (hC2.continuous.abs.integrable_of_hasCompactSupport
              hcompact.abs)
          · exact (hC2.continuous.abs.integrable_of_hasCompactSupport
              hcompact.abs)
          · intro u
            rw [abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg (h u))
              (Real.abs_cos_le_one _)
    exact hL.mul_of_bounded_left
      (∫ u : ℝ, |h u|) hshift hb
  rw [integral_sub
    (hshift.const_mul (digammaLorentzian a 0))
    hprod]
  rw [integral_const_mul, hz, zero_mul, zero_sub, hconv]
  rfl

theorem gammaRespPartial_eq_kernelPartial
    {h : ℝ → ℝ}
    (hC2 : ContDiff ℝ 2 h)
    (hcompact : HasCompactSupport h)
    (heven : ∀ x, h (-x)=h x)
    (h0 : h 0 = 0) (t : ℝ) (N : ℕ) :
    gammaRespPartial N h t
      =
    - ∫ u : ℝ,
        h u * Real.cos (t*u) * gammaKernelPartial N u := by
  unfold gammaRespPartial gammaBracketPartial
  have hz := integral_cosFT_shift_eq_zero
    hC2 hcompact heven h0 t
  have hhead :=
    integral_cosFT_mul_gammaHeadIncrement
      hC2 hcompact heven h0 t
  have htail :
      ∀ n,
      (∫ x : ℝ,
        cosFT h (x-t) * gammaTailIncrement n x)
      =
      -2*Real.pi *
        ∫ u : ℝ,
          h u * Real.cos (t*u)
            * Real.exp (-2*((n:ℝ)+5/4)*|u|) :=
    fun n => integral_cosFT_mul_gammaTailIncrement
      hC2 hcompact heven h0 t n
  rw [show (fun x : ℝ =>
      cosFT h (x-t)
        * (Zeta23.EF.gammaBracket 0
          + gammaHeadIncrement x
          + ∑ n ∈ Finset.range N, gammaTailIncrement n x))
      =
      fun x =>
        Zeta23.EF.gammaBracket 0 * cosFT h (x-t)
          + cosFT h (x-t) * gammaHeadIncrement x
          + ∑ n ∈ Finset.range N,
              cosFT h (x-t) * gammaTailIncrement n x by
      funext x
      rw [Finset.mul_sum]
      ring]
  rw [integral_add, integral_add]
  · rw [integral_const_mul, hz, mul_zero, zero_add, hhead]
    rw [integral_finsetSum]
    · simp_rw [htail]
      unfold gammaKernelPartial
      rw [integral_neg]
      field_simp [Real.pi_ne_zero]
      rw [integral_add]
      · rw [integral_finsetSum]
        · ring_nf
        · intro n hn
          exact (hC2.continuous.integrable_of_hasCompactSupport hcompact).mul
            (by fun_prop)
      · exact (hC2.continuous.integrable_of_hasCompactSupport hcompact).mul
          (by fun_prop)
    · intro n hn
      exact (hC2.continuous.integrable_of_hasCompactSupport hcompact).mul
        (by fun_prop)
  · exact (hC2.continuous.integrable_of_hasCompactSupport hcompact).mul
      (by fun_prop)
  · exact (hC2.continuous.integrable_of_hasCompactSupport hcompact).mul
      (by fun_prop)

end Synthesis
