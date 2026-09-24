import Synthesis.RiemannReflectionPartnerSchurNoGo
import Synthesis.RiemannConstructedSmoothShortWindowSchur
import Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Reflection-pair lower bound inside the same-ordinate cluster

For the constructed smooth short windows, every admitted radius 0 < r <= 1 is
radially admissible because

  2 r |u| < 2 log 2 < 3/2 < pi/2.

Hence every same-ordinate zero has nonnegative two-radius defect.

If rho is off the critical line, its functional-equation partner is a distinct
member of the same ordinate fibre and has exactly the same defect. Therefore

  2 * D_rho <= D_cluster

coordinatewise for every taper in the smooth Schur family.

This is the actual signal inhabitant: the unavoidable reflection partner doubles
the target instead of becoming a nuisance budget.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilTwoTaperCoefficientGate

theorem two_log_two_lt_pi_div_two :
    2 * Real.log 2 < Real.pi / 2 := by
  have hlog := Real.log_two_lt_d9
  have hpi := Real.pi_gt_three
  nlinarith

namespace SmoothShortWindowSchurCertificate

variable {sigma rho : Zeros}
variable (C : SmoothShortWindowSchurCertificate sigma rho)

theorem radialAdmissible_of_radius_le_one
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∀ j u, C.g j u ≠ 0 →
      2 * r * |u| < Real.pi / 2 := by
  intro j u hu
  have hus : |u| < Real.log 2 := C.shortPair j u hu
  have hmul : r * |u| ≤ |u| :=
    mul_le_of_le_one_left (abs_nonneg u) hr.le hr1
  have hlogpi := two_log_two_lt_pi_div_two
  nlinarith

theorem zeroHeightDefect_nonneg_on_pair
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (j : Fin 2) (z : Zeros) :
    0 ≤ zeroHeightDefect (C.g j) r z := by
  exact zeroHeightDefect_nonneg
    (C.smoothPair j).continuous
    (C.compactPair j)
    (C.nonnegPair j)
    hr
    (C.radialAdmissible_of_radius_le_one hr hr1 j)
    z

theorem targetZeroHeightDefect_pos
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (j : Fin 2) {z : Zeros}
    (hoff : heightOf z ≠ 0) :
    0 < zeroHeightDefect (C.g j) r z := by
  obtain ⟨u, v, hu, hv, huv⟩ := C.twoPointPositive j
  exact zeroHeightDefect_pos
    (C.smoothPair j).continuous
    (C.compactPair j)
    (C.nonnegPair j)
    hr
    (C.radialAdmissible_of_radius_le_one hr hr1 j)
    hu hv huv hoff

theorem reflectZeroHeightDefect_eq
    (j : Fin 2) (r : ℝ) (z : Zeros) :
    zeroHeightDefect (C.g j) r (reflectZero z)
      = zeroHeightDefect (C.g j) r z := by
  unfold zeroHeightDefect
  rw [reflectZero_mult, heightOf_reflectZero, heightDefect_neg_height]

theorem two_targetDefect_le_cluster
    {t r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1)
    (j : Fin 2)
    {z : Zeros}
    (him : (z : ℂ).im = t)
    (hoff : heightOf z ≠ 0) :
    2 * zeroHeightDefect (C.g j) r z
      ≤ clusterHeightDefect (C.g j) t r := by
  classical
  rw [clusterHeightDefect_eq_tsum
    (C.smoothPair j) (C.compactPair j) (C.evenPair j) t r]

  let z0 : SameOrd t := ⟨z, him⟩
  let z1 : SameOrd t :=
    ⟨reflectZero z, by simpa [reflectZero_im] using him⟩

  have hneZ : z1 ≠ z0 := by
    intro h
    have hv : (z1 : Zeros) = (z0 : Zeros) := congrArg Subtype.val h
    dsimp [z0, z1] at hv
    exact (reflectZero_ne_of_height_ne_zero hoff) hv

  have hsum :=
    Summable.sum_le_tsum
      (f := fun w : SameOrd t =>
        zeroHeightDefect (C.g j) r (w : Zeros))
      {z0, z1}
      (fun w _ => C.zeroHeightDefect_nonneg_on_pair hr hr1 j (w : Zeros))
      (summable_zeroHeightDefect
        (C.smoothPair j) (C.compactPair j) (C.evenPair j) t r)

  have href :
      zeroHeightDefect (C.g j) r (z1 : Zeros)
        = zeroHeightDefect (C.g j) r z := by
    dsimp [z1]
    exact C.reflectZeroHeightDefect_eq j r z

  have hz0 :
      zeroHeightDefect (C.g j) r (z0 : Zeros)
        = zeroHeightDefect (C.g j) r z := by
    rfl

  have hfinite :
      ∑ w ∈ ({z0, z1} : Finset (SameOrd t)),
          zeroHeightDefect (C.g j) r (w : Zeros)
        =
      2 * zeroHeightDefect (C.g j) r z := by
    rw [Finset.sum_insert]
    · rw [Finset.sum_singleton, hz0, href]
      ring
    · simpa [Finset.mem_singleton] using hneZ

  rw [hfinite] at hsum
  exact hsum

theorem two_targetDefect_pos_and_le_cluster
    {t r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1)
    (j : Fin 2)
    {z : Zeros}
    (him : (z : ℂ).im = t)
    (hoff : heightOf z ≠ 0) :
    0 < 2 * zeroHeightDefect (C.g j) r z
      ∧
    2 * zeroHeightDefect (C.g j) r z
      ≤ clusterHeightDefect (C.g j) t r := by
  refine ⟨?_, C.two_targetDefect_le_cluster hr hr1 j him hoff⟩
  have hpos := C.targetZeroHeightDefect_pos hr hr1 j hoff
  nlinarith

end SmoothShortWindowSchurCertificate

end Synthesis
