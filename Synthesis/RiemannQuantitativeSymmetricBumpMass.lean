import Synthesis.RiemannQuantitativeScaledBumpMass
import Zeta23Bridge.LiteralWeilOddChannelTaper

/-!
# L1 scaling of the symmetric quantitative bump

For phi_{c,R}(u)=psi((u-c)/R), define

    sym phi (u) = phi(u) + phi(-u).

Reflection preserves L1 mass, while derivatives only introduce signs. Hence

    M0(sym phi) <= 2 R M0*,
    M1(sym phi) <= 2 M1*,
    M2(sym phi) <= 2 R^{-1} M2*.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilOddChannelTaper
open Zeta23Bridge.LiteralWeilProjectiveStripConstant

def quantitativeSymBump (c R : ℝ) : ℝ → ℝ :=
  symmetrize (scaledUnitBump c R)

theorem quantitativeSymBump_contDiff {c R : ℝ} (hR : R ≠ 0) :
    ContDiff ℝ 2 (quantitativeSymBump c R) := by
  unfold quantitativeSymBump
  exact symmetrize_contDiff (scaledUnitBump_contDiff hR c)

theorem quantitativeSymBump_hasCompactSupport {c R : ℝ} (hR : 0 < R) :
    HasCompactSupport (quantitativeSymBump c R) := by
  unfold quantitativeSymBump
  exact symmetrize_hasCompactSupport
    (scaledUnitBump_hasCompactSupport hR)

theorem quantitativeSymBump_nonneg (c R u : ℝ) :
    0 <= quantitativeSymBump c R u := by
  unfold quantitativeSymBump symmetrize
  exact add_nonneg
    (scaledUnitBump_nonneg c R u)
    (scaledUnitBump_nonneg c R (-u))

theorem integral_abs_reflect_eq (f : ℝ → ℝ) :
    (∫ u : ℝ, |f (-u)|) = ∫ u : ℝ, |f u| := by
  simpa using
    MeasureTheory.integral_neg_eq_self
      (fun u : ℝ => |f (-u)|) (volume : Measure ℝ)

theorem taperMass_symmetrize_le
    {f : ℝ → ℝ}
    (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    taperMass (symmetrize f) <= 2 * taperMass f := by
  have hfi : Integrable (fun u : ℝ => |f u|) :=
    hf.abs.integrable_of_hasCompactSupport hfc.abs
  have hfri : Integrable (fun u : ℝ => |f (-u)|) := by
    have hc : Continuous (fun u : ℝ => |f (-u)|) :=
      (hf.comp continuous_neg).abs
    have hs : HasCompactSupport (fun u : ℝ => |f (-u)|) :=
      (hfc.comp_homeomorph (Homeomorph.neg ℝ)).abs
    exact hc.integrable_of_hasCompactSupport hs
  unfold taperMass symmetrize
  have hpt : ∀ u : ℝ, |f u + f (-u)| <= |f u| + |f (-u)| :=
    fun u => abs_add _ _
  have hsum := integral_mono
    ((hf.add (hf.comp continuous_neg)).abs.integrable_of_hasCompactSupport
      (hfc.add (hfc.comp_homeomorph (Homeomorph.neg ℝ))).abs)
    (hfi.add hfri) hpt
  rw [integral_add hfi hfri, integral_abs_reflect_eq] at hsum
  nlinarith

theorem deriv_symmetrize {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) :
    deriv (symmetrize f)
      = fun u => deriv f u - deriv f (-u) := by
  funext u
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hneg : HasDerivAt (fun x : ℝ => f (-x)) (-deriv f (-u)) u := by
    have hi : HasDerivAt (fun x : ℝ => -x) (-1) u := by
      simpa using (hasDerivAt_id u).neg
    have hc := (hd (-u)).hasDerivAt.comp u hi
    simpa using hc
  have hs := (hd u).hasDerivAt.add hneg
  rw [hs.deriv]
  unfold symmetrize
  ring

theorem deriv2_symmetrize {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) :
    deriv (deriv (symmetrize f))
      = fun u => deriv (deriv f) u + deriv (deriv f) (-u) := by
  rw [deriv_symmetrize hf.of_le (by norm_num)]
  funext u
  have hd1 : Differentiable ℝ (deriv f) :=
    hf.differentiable_deriv_two
  have hneg :
      HasDerivAt (fun x : ℝ => - deriv f (-x))
        (deriv (deriv f) (-u)) u := by
    have hi : HasDerivAt (fun x : ℝ => -x) (-1) u := by
      simpa using (hasDerivAt_id u).neg
    have hc := (hd1 (-u)).hasDerivAt.comp u hi
    have hn := hc.neg
    simpa using hn
  have hs := (hd1 u).hasDerivAt.add hneg
  rw [hs.deriv]
  ring

theorem taperMass_quantitativeSymBump_le
    {c R : ℝ} (hR : 0 < R) :
    taperMass (quantitativeSymBump c R)
      <= 2 * R * unitBumpMass0 := by
  unfold quantitativeSymBump
  have h :=
    taperMass_symmetrize_le
      (scaledUnitBump_continuous hR.ne' c)
      (scaledUnitBump_hasCompactSupport hR)
  rw [taperMass_scaledUnitBump hR] at h
  nlinarith

theorem taperMass_deriv_quantitativeSymBump_le
    {c R : ℝ} (hR : 0 < R) :
    taperMass (deriv (quantitativeSymBump c R))
      <= 2 * unitBumpMass1 := by
  have hphi := scaledUnitBump_contDiff hR.ne' c
  have hpc := scaledUnitBump_hasCompactSupport hR
  rw [quantitativeSymBump, deriv_symmetrize hphi.of_le (by norm_num)]
  unfold taperMass
  have hpt : ∀ u : ℝ,
      |deriv (scaledUnitBump c R) u - deriv (scaledUnitBump c R) (-u)|
        <= |deriv (scaledUnitBump c R) u|
          + |deriv (scaledUnitBump c R) (-u)| :=
    fun u => abs_sub _ _
  have hdcont := (hphi.deriv').continuous
  have hdi : Integrable (fun u : ℝ => |deriv (scaledUnitBump c R) u|) :=
    hdcont.abs.integrable_of_hasCompactSupport hpc.deriv.abs
  have hdri : Integrable
      (fun u : ℝ => |deriv (scaledUnitBump c R) (-u)|) := by
    exact (hdcont.comp continuous_neg).abs.integrable_of_hasCompactSupport
      (hpc.deriv.comp_homeomorph (Homeomorph.neg ℝ)).abs
  have hsum := integral_mono
    ((hdcont.sub (hdcont.comp continuous_neg)).abs.integrable_of_hasCompactSupport
      (hpc.deriv.add
        (hpc.deriv.comp_homeomorph (Homeomorph.neg ℝ))).abs)
    (hdi.add hdri) hpt
  rw [integral_add hdi hdri,
    integral_abs_reflect_eq,
    taperMass_deriv_scaledUnitBump hR] at hsum
  exact hsum

theorem taperMass_deriv2_quantitativeSymBump_le
    {c R : ℝ} (hR : 0 < R) :
    taperMass (deriv (deriv (quantitativeSymBump c R)))
      <= 2 * R⁻¹ * unitBumpMass2 := by
  have hphi := scaledUnitBump_contDiff hR.ne' c
  have hpc := scaledUnitBump_hasCompactSupport hR
  rw [quantitativeSymBump, deriv2_symmetrize hphi]
  unfold taperMass
  have hd2cont :=
    Zeta23Bridge.LiteralWeilProjectiveStripConstant.continuous_deriv2 hphi
  have hpt : ∀ u : ℝ,
      |deriv (deriv (scaledUnitBump c R)) u
        + deriv (deriv (scaledUnitBump c R)) (-u)|
        <= |deriv (deriv (scaledUnitBump c R)) u|
          + |deriv (deriv (scaledUnitBump c R)) (-u)| :=
    fun u => abs_add _ _
  have hdi : Integrable
      (fun u : ℝ => |deriv (deriv (scaledUnitBump c R)) u|) :=
    hd2cont.abs.integrable_of_hasCompactSupport hpc.deriv.deriv.abs
  have hdri : Integrable
      (fun u : ℝ => |deriv (deriv (scaledUnitBump c R)) (-u)|) :=
    (hd2cont.comp continuous_neg).abs.integrable_of_hasCompactSupport
      (hpc.deriv.deriv.comp_homeomorph (Homeomorph.neg ℝ)).abs
  have hsum := integral_mono
    ((hd2cont.add (hd2cont.comp continuous_neg)).abs.integrable_of_hasCompactSupport
      (hpc.deriv.deriv.add
        (hpc.deriv.deriv.comp_homeomorph (Homeomorph.neg ℝ))).abs)
    (hdi.add hdri) hpt
  rw [integral_add hdi hdri,
    integral_abs_reflect_eq,
    taperMass_deriv2_scaledUnitBump hR] at hsum
  nlinarith

end Synthesis
