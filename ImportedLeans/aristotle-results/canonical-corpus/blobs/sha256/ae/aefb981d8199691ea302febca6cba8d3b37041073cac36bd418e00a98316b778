/-
# Finite-radius transfer of the strict even moment determinant

This is the even/cosine counterpart of `OddTaylorDeterminant.lean`.

`StrictKernelMomentRatio.lean` closes the *continuum* even obligation with a
strict margin,

  `Δ_even = M 0 a * M 2 p − M 2 a * M 0 p > 0`   for `0 < a < p`.

This module transports that margin to the **actual finite-radius even response**

  `A_y(r) = ∫₀ᴸ φ(u) cosh (y u) cos (r u) du`,

which is the even (cosine) channel of the two-height observation at radius `r`.

The chain mirrors the odd one:

* `abs_cos_sub_taylor2` : `|cos x − (1 − x²/2)| ≤ x⁴/24` for `x ≥ 0`;

* `evenResponse_sub_trunc_abs_le` : the entrywise remainder bound
  `|A_y(r) − (M 0 y − (r²/2) M 2 y)| ≤ (r⁴/24) M 4 y`;

* `evenTruncatedDeterminant_eq` : the **exact** cancellation identity
  `T_a(r) T_p(2r) − T_a(2r) T_p(r) = −( (3/2) r² Δ_even )`
  (the `M₀×M₀` and `M₂×M₂` contributions cancel identically; only the
  `M₀/M₂` cross terms survive);

* `evenMoment_le_of_support` : `M 2 y ≤ L² M 0 y` and `M 4 y ≤ L⁴ M 0 y`;

* `evenFiniteRadiusDeterminant_neg` : the sign-preservation gate.  For
  `0 < r`, `r L ≤ 1` and the *relative* smallness condition
  `2 r² L⁴ M 0 a * M 0 p < Δ_even`, the finite-radius minor
  `D_R = A_a(r) A_p(2r) − A_a(2r) A_p(r)` is strictly negative;

* `exists_radius_evenFiniteRadiusDeterminant_neg` : combined with the continuum
  theorem, an explicit threshold below which the actual finite-radius even minor
  has a strict sign.

The determinant-level error is again handled through the exact identity
`oddDeterminant_sub_truncated_eq` (a pure algebraic identity, reused here), so
the analysis is never four independent entrywise approximations.

No `sorry`, no `axiom`, no numerical evidence.
-/

import Mathlib
import RiemannAnalytic.OddTaylorDeterminant

open MeasureTheory Set

namespace RiemannAnalytic
namespace EvenTaylorDeterminant

open StrictKernelMomentRatio OddTaylorDeterminant

/-! ## The fourth-order cosine remainder -/

/-- The fourth-order cosine remainder bound on the positive axis. -/
theorem abs_cos_sub_taylor2 {x : ℝ} (hx : 0 ≤ x) :
    |Real.cos x - (1 - x ^ 2 / 2)| ≤ x ^ 4 / 24 := by
  rw [abs_le]
  refine ⟨by nlinarith [Real.one_sub_sq_div_two_le_cos (x := x), pow_nonneg hx 4], ?_⟩
  nlinarith [cos_le_quartic hx]

/-! ## The finite-radius even response and its truncation -/

/-- The even (cosine) response of the taper at height `y` and observation radius `r`. -/
noncomputable def evenResponse (L : ℝ) (φ : ℝ → ℝ) (y r : ℝ) : ℝ :=
  ∫ u in Ioc (0 : ℝ) L, φ u * Real.cosh (y * u) * Real.cos (r * u)

/-- The quadratic truncation `T_y(r) = M 0 y − (r²/2) M 2 y`. -/
noncomputable def evenTrunc (L : ℝ) (φ : ℝ → ℝ) (y r : ℝ) : ℝ :=
  evenMoment L φ 0 y - r ^ 2 / 2 * evenMoment L φ 2 y

section Taper

variable {L Cφ y r : ℝ} {φ : ℝ → ℝ}

/-- Integrability of the even moment integrands. -/
theorem integrable_evenMoment (hφmeas : Measurable φ)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (hy : 0 < y) (k : ℕ) :
    Integrable (fun u => u ^ k * φ u * Real.cosh (y * u)) (volume.restrict (Ioc (0 : ℝ) L)) := by
  refine integrable_restrict_Ioc_of_bounded
    ((measurable_id.pow_const k |>.mul hφmeas).mul
      (Real.measurable_cosh.comp (measurable_const.mul measurable_id)))
    (C := L ^ k * |Cφ| * Real.cosh (y * L)) ?_
  intro u hu
  rw [abs_mul, abs_mul]
  have h1 : |u ^ k| ≤ L ^ k := by
    rw [abs_pow, abs_of_pos hu.1]
    exact pow_le_pow_left₀ hu.1.le hu.2 k
  have h2 : |φ u| ≤ |Cφ| := (hφb u hu).trans (le_abs_self _)
  have h3 : |Real.cosh (y * u)| ≤ Real.cosh (y * L) := by
    rw [abs_of_pos (Real.cosh_pos _)]
    exact Real.cosh_le_cosh.2 (by
      rw [abs_of_pos (mul_pos hy hu.1), abs_of_pos (mul_pos hy hL)]
      exact mul_le_mul_of_nonneg_left hu.2 hy.le)
  have hs : 0 ≤ Real.cosh (y * L) := (Real.cosh_pos _).le
  exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) h3 (abs_nonneg _)
    (by positivity)

theorem integrable_evenResponse (hφmeas : Measurable φ)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (hy : 0 < y) :
    Integrable (fun u => φ u * Real.cosh (y * u) * Real.cos (r * u))
      (volume.restrict (Ioc (0 : ℝ) L)) := by
  refine integrable_restrict_Ioc_of_bounded
    ((hφmeas.mul (Real.measurable_cosh.comp (measurable_const.mul measurable_id))).mul
      (Real.measurable_cos.comp (measurable_const.mul measurable_id)))
    (C := |Cφ| * Real.cosh (y * L) * 1) ?_
  intro u hu
  rw [abs_mul, abs_mul]
  have h2 : |φ u| ≤ |Cφ| := (hφb u hu).trans (le_abs_self _)
  have h3 : |Real.cosh (y * u)| ≤ Real.cosh (y * L) := by
    rw [abs_of_pos (Real.cosh_pos _)]
    exact Real.cosh_le_cosh.2 (by
      rw [abs_of_pos (mul_pos hy hu.1), abs_of_pos (mul_pos hy hL)]
      exact mul_le_mul_of_nonneg_left hu.2 hy.le)
  have hs : 0 ≤ Real.cosh (y * L) := (Real.cosh_pos _).le
  exact mul_le_mul (mul_le_mul h2 h3 (abs_nonneg _) (abs_nonneg _))
    (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)

/-- **Entrywise remainder bound.**  The even response differs from its quadratic
truncation by at most `(r⁴/24) M 4 y`. -/
theorem evenResponse_sub_trunc_abs_le (hφmeas : Measurable φ)
    (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (hy : 0 < y) (hr : 0 ≤ r) :
    |evenResponse L φ y r - evenTrunc L φ y r| ≤ r ^ 4 / 24 * evenMoment L φ 4 y := by
  have hI1 := integrable_evenResponse (r := r) hφmeas hφb hL hy
  have hM0 := integrable_evenMoment hφmeas hφb hL hy 0
  have hM2 := integrable_evenMoment hφmeas hφb hL hy 2
  have hM4 := integrable_evenMoment hφmeas hφb hL hy 4
  have hG : Integrable (fun u => 1 * (u ^ 0 * φ u * Real.cosh (y * u))
      - r ^ 2 / 2 * (u ^ 2 * φ u * Real.cosh (y * u))) (volume.restrict (Ioc (0 : ℝ) L)) := by
    simpa using (hM0.const_mul 1).sub (hM2.const_mul (r ^ 2 / 2))
  have hdiff : evenResponse L φ y r - evenTrunc L φ y r
      = ∫ u in Ioc (0 : ℝ) L,
          φ u * Real.cosh (y * u) * (Real.cos (r * u) - (1 - (r * u) ^ 2 / 2)) := by
    calc evenResponse L φ y r - evenTrunc L φ y r
        = (∫ u in Ioc (0 : ℝ) L, φ u * Real.cosh (y * u) * Real.cos (r * u))
          - ((∫ u in Ioc (0 : ℝ) L, 1 * (u ^ 0 * φ u * Real.cosh (y * u)))
            - (∫ u in Ioc (0 : ℝ) L, r ^ 2 / 2 * (u ^ 2 * φ u * Real.cosh (y * u)))) := by
          rw [evenResponse, evenTrunc, evenMoment, evenMoment, integral_const_mul,
            integral_const_mul]
          ring
      _ = ∫ u in Ioc (0 : ℝ) L, (φ u * Real.cosh (y * u) * Real.cos (r * u)
            - (1 * (u ^ 0 * φ u * Real.cosh (y * u))
              - r ^ 2 / 2 * (u ^ 2 * φ u * Real.cosh (y * u)))) := by
          rw [integral_sub hI1 hG, integral_sub (hM0.const_mul 1) (hM2.const_mul (r ^ 2 / 2))]
      _ = ∫ u in Ioc (0 : ℝ) L,
            φ u * Real.cosh (y * u) * (Real.cos (r * u) - (1 - (r * u) ^ 2 / 2)) := by
          congr 1
          funext u
          ring
  rw [hdiff]
  have hbound : ∀ u ∈ Ioc (0 : ℝ) L,
      |φ u * Real.cosh (y * u) * (Real.cos (r * u) - (1 - (r * u) ^ 2 / 2))|
        ≤ r ^ 4 / 24 * (u ^ 4 * φ u * Real.cosh (y * u)) := by
    intro u hu
    have hφu := hφ0 u hu
    have hcu : 0 ≤ Real.cosh (y * u) := (Real.cosh_pos _).le
    have hru : 0 ≤ r * u := mul_nonneg hr hu.1.le
    have h := abs_cos_sub_taylor2 hru
    rw [abs_mul, abs_of_nonneg (mul_nonneg hφu hcu)]
    have hkey : |Real.cos (r * u) - (1 - (r * u) ^ 2 / 2)| ≤ r ^ 4 / 24 * u ^ 4 := by
      refine h.trans (le_of_eq ?_)
      ring
    calc φ u * Real.cosh (y * u) * |Real.cos (r * u) - (1 - (r * u) ^ 2 / 2)|
        ≤ φ u * Real.cosh (y * u) * (r ^ 4 / 24 * u ^ 4) :=
          mul_le_mul_of_nonneg_left hkey (mul_nonneg hφu hcu)
      _ = r ^ 4 / 24 * (u ^ 4 * φ u * Real.cosh (y * u)) := by ring
  calc |∫ u in Ioc (0 : ℝ) L,
          φ u * Real.cosh (y * u) * (Real.cos (r * u) - (1 - (r * u) ^ 2 / 2))|
      ≤ ∫ u in Ioc (0 : ℝ) L,
          |φ u * Real.cosh (y * u) * (Real.cos (r * u) - (1 - (r * u) ^ 2 / 2))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u in Ioc (0 : ℝ) L, r ^ 4 / 24 * (u ^ 4 * φ u * Real.cosh (y * u)) := by
        refine integral_mono_of_nonneg (by filter_upwards with u using abs_nonneg _)
          (hM4.const_mul _) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu using hbound u hu
    _ = r ^ 4 / 24 * evenMoment L φ 4 y := by
        rw [integral_const_mul]; rfl

/-! ## Compact-support moment domination -/

/-- `M k y ≥ 0` for a nonnegative taper. -/
theorem evenMoment_nonneg (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u) (k : ℕ) :
    0 ≤ evenMoment L φ k y := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact mul_nonneg (mul_nonneg (pow_nonneg hu.1.le k) (hφ0 u hu)) (Real.cosh_pos _).le

/-- **Support domination.**  `M (k+j) y ≤ L^j * M k y`. -/
theorem evenMoment_le_of_support (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (hy : 0 < y) (k j : ℕ) :
    evenMoment L φ (k + j) y ≤ L ^ j * evenMoment L φ k y := by
  have hMk := integrable_evenMoment hφmeas hφb hL hy k
  have hMkj := integrable_evenMoment hφmeas hφb hL hy (k + j)
  have hmain : evenMoment L φ (k + j) y ≤ ∫ u in Ioc (0 : ℝ) L,
      L ^ j * (u ^ k * φ u * Real.cosh (y * u)) := by
    refine integral_mono_ae hMkj (hMk.const_mul _) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    · have hφu := hφ0 u hu
      have hcu : 0 ≤ Real.cosh (y * u) := (Real.cosh_pos _).le
      have huj : u ^ j ≤ L ^ j := pow_le_pow_left₀ hu.1.le hu.2 j
      have hrw : u ^ (k + j) * φ u * Real.cosh (y * u)
          = (u ^ k * φ u * Real.cosh (y * u)) * u ^ j := by rw [pow_add]; ring
      rw [hrw]
      have hnn : 0 ≤ u ^ k * φ u * Real.cosh (y * u) :=
        mul_nonneg (mul_nonneg (pow_nonneg hu.1.le k) hφu) hcu
      calc (u ^ k * φ u * Real.cosh (y * u)) * u ^ j
          ≤ (u ^ k * φ u * Real.cosh (y * u)) * L ^ j := mul_le_mul_of_nonneg_left huj hnn
        _ = L ^ j * (u ^ k * φ u * Real.cosh (y * u)) := by ring
  rw [integral_const_mul] at hmain
  exact hmain

end Taper

/-! ## Exact determinant algebra -/

/-- **Exact truncated determinant.**  At the radii `r` and `2r` the `M₀×M₀` and
`M₂×M₂` contributions cancel identically; the surviving signal is the `M₀/M₂`
cross term, proportional to the continuum margin `Δ_even`. -/
theorem evenTruncatedDeterminant_eq (L : ℝ) (φ : ℝ → ℝ) (a p r : ℝ) :
    evenTrunc L φ a r * evenTrunc L φ p (2 * r) - evenTrunc L φ a (2 * r) * evenTrunc L φ p r
      = -(3 / 2 * r ^ 2 * (evenMoment L φ 0 a * evenMoment L φ 2 p
          - evenMoment L φ 2 a * evenMoment L φ 0 p)) := by
  simp only [evenTrunc]
  ring

/-! ## The sign-preservation gate -/

set_option maxHeartbeats 1000000 in
/-- **Relative-margin sign transfer, even sector.**  Given the moment domination
bounds, the entrywise fourth-order remainder bounds and the *relative* smallness
condition `2 r² L⁴ M₀(a) M₀(p) < Δ_even`, the finite-radius even determinant is
strictly negative. -/
theorem even_sign_transfer {A0 A2 A4 P0 P2 P4 Aa1 Aa2 Ap1 Ap2 Ta1 Ta2 Tp1 Tp2 L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) (hrL : r * L ≤ 1)
    (hA0 : 0 ≤ A0) (hA2 : 0 ≤ A2) (hP0 : 0 ≤ P0) (hP2 : 0 ≤ P2)
    (hA2L : A2 ≤ L ^ 2 * A0) (hA4L : A4 ≤ L ^ 4 * A0)
    (hP2L : P2 ≤ L ^ 2 * P0) (hP4L : P4 ≤ L ^ 4 * P0)
    (hTa1 : Ta1 = A0 - r ^ 2 / 2 * A2) (hTa2 : Ta2 = A0 - (2 * r) ^ 2 / 2 * A2)
    (hTp1 : Tp1 = P0 - r ^ 2 / 2 * P2) (hTp2 : Tp2 = P0 - (2 * r) ^ 2 / 2 * P2)
    (hEa1 : |Aa1 - Ta1| ≤ r ^ 4 / 24 * A4) (hEa2 : |Aa2 - Ta2| ≤ (2 * r) ^ 4 / 24 * A4)
    (hEp1 : |Ap1 - Tp1| ≤ r ^ 4 / 24 * P4) (hEp2 : |Ap2 - Tp2| ≤ (2 * r) ^ 4 / 24 * P4)
    (hgap : 2 * r ^ 2 * L ^ 4 * (A0 * P0) < A0 * P2 - A2 * P0) :
    Aa1 * Ap2 - Aa2 * Ap1 < 0 := by
  have hrL0 : 0 < r * L := mul_pos hr hL
  have hsq : (r * L) ^ 2 ≤ 1 := pow_le_one₀ hrL0.le hrL
  have h4L : r ^ 4 * L ^ 4 ≤ 1 := by
    calc r ^ 4 * L ^ 4 = (r * L) ^ 4 := by ring
      _ ≤ 1 := pow_le_one₀ hrL0.le hrL
  have hkeya : r ^ 2 * A2 ≤ A0 := by
    calc r ^ 2 * A2 ≤ r ^ 2 * (L ^ 2 * A0) := mul_le_mul_of_nonneg_left hA2L (by positivity)
      _ = (r * L) ^ 2 * A0 := by ring
      _ ≤ 1 * A0 := mul_le_mul_of_nonneg_right hsq hA0
      _ = A0 := one_mul _
  have hkeyp : r ^ 2 * P2 ≤ P0 := by
    calc r ^ 2 * P2 ≤ r ^ 2 * (L ^ 2 * P0) := mul_le_mul_of_nonneg_left hP2L (by positivity)
      _ = (r * L) ^ 2 * P0 := by ring
      _ ≤ 1 * P0 := mul_le_mul_of_nonneg_right hsq hP0
      _ = P0 := one_mul _
  have hr2A2 : 0 ≤ r ^ 2 * A2 := by positivity
  have hr2P2 : 0 ≤ r ^ 2 * P2 := by positivity
  have hbTa1 : |Ta1| ≤ A0 := by rw [hTa1, abs_le]; constructor <;> linarith
  have hbTa2 : |Ta2| ≤ A0 := by rw [hTa2, abs_le]; constructor <;> linarith
  have hbTp1 : |Tp1| ≤ P0 := by rw [hTp1, abs_le]; constructor <;> linarith
  have hbTp2 : |Tp2| ≤ P0 := by rw [hTp2, abs_le]; constructor <;> linarith
  have hEa1' : |Aa1 - Ta1| ≤ r ^ 4 * L ^ 4 * A0 / 24 := by
    refine hEa1.trans ?_
    calc r ^ 4 / 24 * A4 ≤ r ^ 4 / 24 * (L ^ 4 * A0) :=
          mul_le_mul_of_nonneg_left hA4L (by positivity)
      _ = r ^ 4 * L ^ 4 * A0 / 24 := by ring
  have hEa2' : |Aa2 - Ta2| ≤ 16 * (r ^ 4 * L ^ 4 * A0) / 24 := by
    refine hEa2.trans ?_
    calc (2 * r) ^ 4 / 24 * A4 ≤ (2 * r) ^ 4 / 24 * (L ^ 4 * A0) :=
          mul_le_mul_of_nonneg_left hA4L (by positivity)
      _ = 16 * (r ^ 4 * L ^ 4 * A0) / 24 := by ring
  have hEp1' : |Ap1 - Tp1| ≤ r ^ 4 * L ^ 4 * P0 / 24 := by
    refine hEp1.trans ?_
    calc r ^ 4 / 24 * P4 ≤ r ^ 4 / 24 * (L ^ 4 * P0) :=
          mul_le_mul_of_nonneg_left hP4L (by positivity)
      _ = r ^ 4 * L ^ 4 * P0 / 24 := by ring
  have hEp2' : |Ap2 - Tp2| ≤ 16 * (r ^ 4 * L ^ 4 * P0) / 24 := by
    refine hEp2.trans ?_
    calc (2 * r) ^ 4 / 24 * P4 ≤ (2 * r) ^ 4 / 24 * (L ^ 4 * P0) :=
          mul_le_mul_of_nonneg_left hP4L (by positivity)
      _ = 16 * (r ^ 4 * L ^ 4 * P0) / 24 := by ring
  have hZ0 : (0 : ℝ) ≤ 2 * (r ^ 4 * L ^ 4 * (A0 * P0)) := by positivity
  have hshrink : (r ^ 4 * L ^ 4 * (A0 * P0)) * (r ^ 4 * L ^ 4)
      ≤ (r ^ 4 * L ^ 4 * (A0 * P0)) * 1 :=
    mul_le_mul_of_nonneg_left h4L (by positivity)
  have b1 : |Ta1 * (Ap2 - Tp2)| ≤ (1 / 3) * (2 * (r ^ 4 * L ^ 4 * (A0 * P0))) := by
    rw [abs_mul]
    calc |Ta1| * |Ap2 - Tp2| ≤ A0 * (16 * (r ^ 4 * L ^ 4 * P0) / 24) :=
          mul_le_mul hbTa1 hEp2' (abs_nonneg _) hA0
      _ = (1 / 3) * (2 * (r ^ 4 * L ^ 4 * (A0 * P0))) := by ring
  have b2 : |(Aa1 - Ta1) * Tp2| ≤ (1 / 48) * (2 * (r ^ 4 * L ^ 4 * (A0 * P0))) := by
    rw [abs_mul]
    calc |Aa1 - Ta1| * |Tp2| ≤ (r ^ 4 * L ^ 4 * A0 / 24) * P0 :=
          mul_le_mul hEa1' hbTp2 (abs_nonneg _) (by positivity)
      _ = (1 / 48) * (2 * (r ^ 4 * L ^ 4 * (A0 * P0))) := by ring
  have b3 : |(Aa1 - Ta1) * (Ap2 - Tp2)| ≤ (1 / 72) * (2 * (r ^ 4 * L ^ 4 * (A0 * P0))) := by
    rw [abs_mul]
    refine (mul_le_mul hEa1' hEp2' (abs_nonneg _) (by positivity)).trans ?_
    calc (r ^ 4 * L ^ 4 * A0 / 24) * (16 * (r ^ 4 * L ^ 4 * P0) / 24)
        = (1 / 36) * ((r ^ 4 * L ^ 4 * (A0 * P0)) * (r ^ 4 * L ^ 4)) := by ring
      _ ≤ (1 / 36) * ((r ^ 4 * L ^ 4 * (A0 * P0)) * 1) := by linarith
      _ = (1 / 72) * (2 * (r ^ 4 * L ^ 4 * (A0 * P0))) := by ring
  have b4 : |Ta2 * (Ap1 - Tp1)| ≤ (1 / 48) * (2 * (r ^ 4 * L ^ 4 * (A0 * P0))) := by
    rw [abs_mul]
    calc |Ta2| * |Ap1 - Tp1| ≤ A0 * (r ^ 4 * L ^ 4 * P0 / 24) :=
          mul_le_mul hbTa2 hEp1' (abs_nonneg _) hA0
      _ = (1 / 48) * (2 * (r ^ 4 * L ^ 4 * (A0 * P0))) := by ring
  have b5 : |(Aa2 - Ta2) * Tp1| ≤ (1 / 3) * (2 * (r ^ 4 * L ^ 4 * (A0 * P0))) := by
    rw [abs_mul]
    calc |Aa2 - Ta2| * |Tp1| ≤ (16 * (r ^ 4 * L ^ 4 * A0) / 24) * P0 :=
          mul_le_mul hEa2' hbTp1 (abs_nonneg _) (by positivity)
      _ = (1 / 3) * (2 * (r ^ 4 * L ^ 4 * (A0 * P0))) := by ring
  have b6 : |(Aa2 - Ta2) * (Ap1 - Tp1)| ≤ (1 / 72) * (2 * (r ^ 4 * L ^ 4 * (A0 * P0))) := by
    rw [abs_mul]
    refine (mul_le_mul hEa2' hEp1' (abs_nonneg _) (by positivity)).trans ?_
    calc (16 * (r ^ 4 * L ^ 4 * A0) / 24) * (r ^ 4 * L ^ 4 * P0 / 24)
        = (1 / 36) * ((r ^ 4 * L ^ 4 * (A0 * P0)) * (r ^ 4 * L ^ 4)) := by ring
      _ ≤ (1 / 36) * ((r ^ 4 * L ^ 4 * (A0 * P0)) * 1) := by linarith
      _ = (1 / 72) * (2 * (r ^ 4 * L ^ 4 * (A0 * P0))) := by ring
  refine det_sign_from_bounds (S := 3 / 2 * r ^ 2 * (A0 * P2 - A2 * P0))
    (Z := 2 * (r ^ 4 * L ^ 4 * (A0 * P0))) ?_ b1 b2 b3 b4 b5 b6 (by norm_num) hZ0 ?_
  · subst hTa1; subst hTa2; subst hTp1; subst hTp2; ring
  · have hstep : 2 * (r ^ 4 * L ^ 4 * (A0 * P0)) < 3 / 2 * r ^ 2 * (A0 * P2 - A2 * P0) := by
      have h := mul_lt_mul_of_pos_left hgap (show (0:ℝ) < 3 / 4 * r ^ 2 by positivity)
      have hnn : (0 : ℝ) ≤ r ^ 4 * L ^ 4 * (A0 * P0) := by positivity
      nlinarith [hnn]
    exact hstep

/-! ## The actual finite-radius even minor -/

/-- The two-height, two-radius even minor at radii `r` and `2r`. -/
noncomputable def evenFiniteRadiusDeterminant (L : ℝ) (φ : ℝ → ℝ) (a p r : ℝ) : ℝ :=
  evenResponse L φ a r * evenResponse L φ p (2 * r)
    - evenResponse L φ a (2 * r) * evenResponse L φ p r

/-- **Finite-radius sign preservation, even sector.**  Under the relative
smallness condition `2 r² L⁴ M₀(a) M₀(p) < Δ_even`, the actual finite-radius even
minor is strictly negative. -/
theorem evenFiniteRadiusDeterminant_neg {L Cφ a p r : ℝ} {φ : ℝ → ℝ}
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (ha : 0 < a) (hap : a < p) (hr : 0 < r) (hrL : r * L ≤ 1)
    (hgap : 2 * r ^ 2 * L ^ 4 * (evenMoment L φ 0 a * evenMoment L φ 0 p)
      < evenMoment L φ 0 a * evenMoment L φ 2 p - evenMoment L φ 2 a * evenMoment L φ 0 p) :
    evenFiniteRadiusDeterminant L φ a p r < 0 := by
  have hp : 0 < p := ha.trans hap
  have hA2L : evenMoment L φ 2 a ≤ L ^ 2 * evenMoment L φ 0 a := by
    have h := evenMoment_le_of_support hφmeas hφ0 hφb hL ha 0 2
    norm_num at h
    exact h
  have hA4L : evenMoment L φ 4 a ≤ L ^ 4 * evenMoment L φ 0 a := by
    have h := evenMoment_le_of_support hφmeas hφ0 hφb hL ha 0 4
    norm_num at h
    exact h
  have hP2L : evenMoment L φ 2 p ≤ L ^ 2 * evenMoment L φ 0 p := by
    have h := evenMoment_le_of_support hφmeas hφ0 hφb hL hp 0 2
    norm_num at h
    exact h
  have hP4L : evenMoment L φ 4 p ≤ L ^ 4 * evenMoment L φ 0 p := by
    have h := evenMoment_le_of_support hφmeas hφ0 hφb hL hp 0 4
    norm_num at h
    exact h
  exact even_sign_transfer (A4 := evenMoment L φ 4 a) (P4 := evenMoment L φ 4 p)
    hL hr hrL
    (evenMoment_nonneg hφ0 0) (evenMoment_nonneg hφ0 2)
    (evenMoment_nonneg hφ0 0) (evenMoment_nonneg hφ0 2)
    hA2L hA4L hP2L hP4L rfl rfl rfl rfl
    (evenResponse_sub_trunc_abs_le (y := a) (r := r) hφmeas hφ0 hφb hL ha hr.le)
    (evenResponse_sub_trunc_abs_le (y := a) (r := 2 * r) hφmeas hφ0 hφb hL ha (by linarith))
    (evenResponse_sub_trunc_abs_le (y := p) (r := r) hφmeas hφ0 hφb hL hp hr.le)
    (evenResponse_sub_trunc_abs_le (y := p) (r := 2 * r) hφmeas hφ0 hφb hL hp (by linarith))
    hgap

/-- **The even finite-radius minor has a strict sign at all small radii.** -/
theorem exists_radius_evenFiniteRadiusDeterminant_neg {L Cφ a p c d m : ℝ} {φ : ℝ → ℝ}
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ)
    (hL : 0 < L) (ha : 0 < a) (hap : a < p)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ → evenFiniteRadiusDeterminant L φ a p r < 0 := by
  set Δ : ℝ := evenMoment L φ 0 a * evenMoment L φ 2 p - evenMoment L φ 2 a * evenMoment L φ 0 p
    with hΔdef
  have hΔ : 0 < Δ := by
    have h := evenMomentDeterminant_strictNegative hφmeas hφ0 hφb hL ha hap hc hcd hdL hm hplateau
    rw [hΔdef]
    linarith
  set K : ℝ := 2 * L ^ 4 * (evenMoment L φ 0 a * evenMoment L φ 0 p) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact mul_nonneg (by positivity)
      (mul_nonneg (evenMoment_nonneg hφ0 0) (evenMoment_nonneg hφ0 0))
  refine ⟨min (min (1 / L) 1) (Δ / (K + 1)), ?_, ?_⟩
  · exact lt_min (lt_min (by positivity) one_pos) (by positivity)
  · intro r hr hlt
    have h1 : r < 1 / L := lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_left _ _))
    have h2 : r < 1 := lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (min_le_right _ _))
    have h3 : r < Δ / (K + 1) := lt_of_lt_of_le hlt (min_le_right _ _)
    have hrL : r * L ≤ 1 := le_of_lt ((lt_div_iff₀ hL).1 (by simpa [one_div] using h1))
    refine evenFiniteRadiusDeterminant_neg hφmeas hφ0 hφb hL ha hap hr hrL ?_
    have hrK : r * (K + 1) < Δ := (lt_div_iff₀ (by linarith : (0:ℝ) < K + 1)).1 h3
    have hrK0 : 0 ≤ r * K := mul_nonneg hr.le hK0
    have hr2 : r ^ 2 * K ≤ r * K := by
      calc r ^ 2 * K = r * (r * K) := by ring
        _ ≤ 1 * (r * K) := mul_le_mul_of_nonneg_right h2.le hrK0
        _ = r * K := one_mul _
    calc 2 * r ^ 2 * L ^ 4 * (evenMoment L φ 0 a * evenMoment L φ 0 p) = r ^ 2 * K := by
          rw [hKdef]; ring
      _ ≤ r * K := hr2
      _ < Δ := by linarith

end EvenTaylorDeterminant
end RiemannAnalytic
