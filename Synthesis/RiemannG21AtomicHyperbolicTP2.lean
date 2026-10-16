import Synthesis.RiemannG21ScaledTanhMonotonicity

/-!
# Atomic strict TP2 for the G21 sinh/cosh kernels

The Agda G21 frontier names the pointwise strict determinant signs

  sinh(p v)sinh(a u) > sinh(p u)sinh(a v),
  cosh(p v)cosh(a u) > cosh(p u)cosh(a v)

for `0<a<p` and `0<u<v` as the atomic inputs for the odd/even continuum moment
producers.  The preceding scaled-hyperbolic files make these consequences of
ordinary one-variable monotonicity rather than independent analytic mysteries.

For sinh, the ratio

  R_s(u) = sinh(pu)/sinh(au)

has derivative numerator

  p cosh(pu)sinh(au) - a cosh(au)sinh(pu),

whose positivity is exactly the `x*coth(x)` comparison at `x=au<pu`.
For cosh the analogous ratio uses the `x*tanh(x)` comparison.

This file source-writes those two chains.  It still does not integrate the
pointwise signs against the actual G21 taper or produce the finite-radius
parity minors.
-/

noncomputable section

open Set

namespace Synthesis

/-- Scale ratio for the odd/sinh kernel. -/
def sinhScaleRatio (a p u : ℝ) : ℝ :=
  Real.sinh (p*u) / Real.sinh (a*u)

/-- Scale ratio for the even/cosh kernel. -/
def coshScaleRatio (a p u : ℝ) : ℝ :=
  Real.cosh (p*u) / Real.cosh (a*u)

private theorem sinhScaleRatio_hasDerivAt
    {a p u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    HasDerivAt (sinhScaleRatio a p)
      ((p * Real.cosh (p*u) * Real.sinh (a*u)
          - a * Real.cosh (a*u) * Real.sinh (p*u))
        / Real.sinh (a*u)^2) u := by
  have hau : 0 < a*u := mul_pos ha hu
  have hden : Real.sinh (a*u) ≠ 0 :=
    (Real.sinh_ne_zero).2 hau.ne'
  have hp :
      HasDerivAt (fun x : ℝ => Real.sinh (p*x))
        (Real.cosh (p*u) * p) u :=
    (hasDerivAt_const_mul (x := u) p).sinh
  have ha' :
      HasDerivAt (fun x : ℝ => Real.sinh (a*x))
        (Real.cosh (a*u) * a) u :=
    (hasDerivAt_const_mul (x := u) a).sinh
  have hraw := hp.div ha' hden
  unfold sinhScaleRatio
  convert hraw using 1 <;> ring

private theorem coshScaleRatio_hasDerivAt
    {a p u : ℝ} :
    HasDerivAt (coshScaleRatio a p)
      ((p * Real.sinh (p*u) * Real.cosh (a*u)
          - a * Real.sinh (a*u) * Real.cosh (p*u))
        / Real.cosh (a*u)^2) u := by
  have hden : Real.cosh (a*u) ≠ 0 := (Real.cosh_pos _).ne'
  have hp :
      HasDerivAt (fun x : ℝ => Real.cosh (p*x))
        (Real.sinh (p*u) * p) u :=
    (hasDerivAt_const_mul (x := u) p).cosh
  have ha' :
      HasDerivAt (fun x : ℝ => Real.cosh (a*x))
        (Real.sinh (a*u) * a) u :=
    (hasDerivAt_const_mul (x := u) a).cosh
  have hraw := hp.div ha' hden
  unfold coshScaleRatio
  convert hraw using 1 <;> ring

/-- Positive derivative of the sinh scale ratio from `x*coth(x)` strict
monotonicity. -/
theorem deriv_sinhScaleRatio_pos
    {a p u : ℝ} (ha : 0 < a) (hap : a < p) (hu : 0 < u) :
    0 < deriv (sinhScaleRatio a p) u := by
  rw [(sinhScaleRatio_hasDerivAt ha hu).deriv]
  have hau : 0 < a*u := mul_pos ha hu
  have hpu : 0 < p*u := by
    exact mul_pos (ha.trans hap) hu
  have haupu : a*u < p*u := mul_lt_mul_of_pos_right hap hu
  have hcoth := scaledCothCarrier_lt hau haupu
  unfold scaledCothCarrier at hcoth
  have hsa : 0 < Real.sinh (a*u) := (Real.sinh_pos_iff).2 hau
  have hsp : 0 < Real.sinh (p*u) := (Real.sinh_pos_iff).2 hpu
  have hcross := (div_lt_div_iff₀ hsa hsp).mp hcoth
  have hcross' :
      a * Real.cosh (a*u) * Real.sinh (p*u)
        < p * Real.cosh (p*u) * Real.sinh (a*u) := by
    have huCross :
        u * (a * Real.cosh (a*u) * Real.sinh (p*u))
          < u * (p * Real.cosh (p*u) * Real.sinh (a*u)) := by
      convert hcross using 1 <;> ring
    exact (mul_lt_mul_left hu).mp huCross
  exact div_pos (sub_pos.mpr hcross') (sq_pos_of_pos hsa)

/-- Positive derivative of the cosh scale ratio from `x*tanh(x)` strict
monotonicity. -/
theorem deriv_coshScaleRatio_pos
    {a p u : ℝ} (ha : 0 < a) (hap : a < p) (hu : 0 < u) :
    0 < deriv (coshScaleRatio a p) u := by
  rw [(coshScaleRatio_hasDerivAt (a := a) (p := p) (u := u)).deriv]
  have hau : 0 < a*u := mul_pos ha hu
  have hpu : 0 < p*u := mul_pos (ha.trans hap) hu
  have haupu : a*u < p*u := mul_lt_mul_of_pos_right hap hu
  have htanh := scaledTanhCarrier_strictMonoOn hau hpu haupu
  unfold scaledTanhCarrier at htanh
  have hca : 0 < Real.cosh (a*u) := Real.cosh_pos _
  have hcp : 0 < Real.cosh (p*u) := Real.cosh_pos _
  have hcross := (div_lt_div_iff₀ hca hcp).mp htanh
  have hcross' :
      a * Real.sinh (a*u) * Real.cosh (p*u)
        < p * Real.sinh (p*u) * Real.cosh (a*u) := by
    have huCross :
        u * (a * Real.sinh (a*u) * Real.cosh (p*u))
          < u * (p * Real.sinh (p*u) * Real.cosh (a*u)) := by
      convert hcross using 1 <;> ring
    exact (mul_lt_mul_left hu).mp huCross
  exact div_pos (sub_pos.mpr hcross') (sq_pos_of_pos hca)

/-- For fixed `0<a<p`, `sinh(pu)/sinh(au)` is strictly increasing on the
positive axis. -/
theorem sinhScaleRatio_strictMonoOn
    {a p : ℝ} (ha : 0 < a) (hap : a < p) :
    StrictMonoOn (sinhScaleRatio a p) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro u hu
    exact (sinhScaleRatio_hasDerivAt ha hu).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ioi, mem_Ioi] at hu
    exact deriv_sinhScaleRatio_pos ha hap hu

/-- For fixed `0<a<p`, `cosh(pu)/cosh(au)` is strictly increasing on the
positive axis. -/
theorem coshScaleRatio_strictMonoOn
    {a p : ℝ} (ha : 0 < a) (hap : a < p) :
    StrictMonoOn (coshScaleRatio a p) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro u hu
    exact (coshScaleRatio_hasDerivAt (a := a) (p := p) (u := u)).continuousAt.continuousWithinAt
  · intro u hu
    rw [interior_Ioi, mem_Ioi] at hu
    exact deriv_coshScaleRatio_pos ha hap hu

/-- Atomic odd/sinh strict TP2 determinant. -/
theorem sinhKernel_strictTP2
    {a p u v : ℝ}
    (ha : 0 < a) (hap : a < p) (hu : 0 < u) (huv : u < v) :
    Real.sinh (p*v) * Real.sinh (a*u)
      > Real.sinh (p*u) * Real.sinh (a*v) := by
  have hv : 0 < v := hu.trans huv
  have hratio := sinhScaleRatio_strictMonoOn ha hap hu hv huv
  unfold sinhScaleRatio at hratio
  have hdu : 0 < Real.sinh (a*u) := (Real.sinh_pos_iff).2 (mul_pos ha hu)
  have hdv : 0 < Real.sinh (a*v) := (Real.sinh_pos_iff).2 (mul_pos ha hv)
  exact (div_lt_div_iff₀ hdu hdv).mp hratio

/-- Atomic even/cosh strict TP2 determinant. -/
theorem coshKernel_strictTP2
    {a p u v : ℝ}
    (ha : 0 < a) (hap : a < p) (hu : 0 < u) (huv : u < v) :
    Real.cosh (p*v) * Real.cosh (a*u)
      > Real.cosh (p*u) * Real.cosh (a*v) := by
  have hv : 0 < v := hu.trans huv
  have hratio := coshScaleRatio_strictMonoOn ha hap hu hv huv
  unfold coshScaleRatio at hratio
  have hcu : 0 < Real.cosh (a*u) := Real.cosh_pos _
  have hcv : 0 < Real.cosh (a*v) := Real.cosh_pos _
  exact (div_lt_div_iff₀ hcu hcv).mp hratio

end Synthesis
