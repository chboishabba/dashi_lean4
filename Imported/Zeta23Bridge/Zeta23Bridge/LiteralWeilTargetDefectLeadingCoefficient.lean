/-
# The small-radius leading coefficient of the target height defect

The projective tranche (`LiteralWeilProjectiveSeparationGate`) bounds the whole
residual side of the literal two-radius balance by

    |D_cluster(t, r)| ≤ r² · E_proj(g, Λ, t),

so the residual is quadratically small in the sampling radius.  For the gate
inequality

    r² · E_proj(g, Λ, t) < D_{ρ*}(r)

to be a *coefficient* comparison rather than an order comparison, the signal side
must be shown to be quadratically small **too**, with an explicit leading
coefficient.  That is what this module does.

Write

    M_y = ∫ g(u) cosh(yu) du,        N_y = ∫ g(u) u² cosh(yu) du

for the zeroth and second cosh-moments of the taper.  The even response
`A_y(s) = ∫ g(u) cosh(yu) cos(su) du` obeys the exact quartic-remainder estimate

    |A_y(s) − (M_y − s²N_y/2)| ≤ (s⁴/24) ∫ |g(u)| u⁴ cosh(yu) du,

which follows from the elementary global inequality
`|cos x − (1 − x²/2)| ≤ x⁴/24` (proved here from scratch, `abs_cos_sub_quadratic_le`).

Substituting into the two-radius determinant

    heightDefect(g, r, a, 0) = A_a(r)A_0(2r) − A_a(2r)A_0(r)

the constant×constant terms cancel identically and the surviving `r²` term is

    (3/2) r² (N_a M_0 − M_a N_0)              (`targetLeadingCoeff`)

with an explicit `O(r⁴)` remainder (`defectRemainderCoeff`).

Consequently the gate inequality reduces, for a fixed taper and small radius, to
the *radius-free* comparison

    E_proj(g, Λ, t)  <  2·mult(ρ*) · targetLeadingCoeff(g, heightOf ρ*)

(`gate_of_coefficientComparison`).  That comparison is **not** proved here; it is
the single remaining quantitative obligation of the programme and appears only as
a hypothesis.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile

noncomputable section

open scoped Real
open MeasureTheory

namespace Zeta23Bridge
namespace LiteralWeilTargetDefectLeadingCoefficient

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile

/-! ## An elementary global quartic bound for the cosine -/

/-- `sin y ≥ y − y³/6` for `y ≥ 0`. -/
theorem cubic_le_sin {y : ℝ} (hy : 0 ≤ y) : 0 ≤ y ^ 3 / 6 + Real.sin y - y := by
  have hmono : MonotoneOn (fun y : ℝ => y ^ 3 / 6 + Real.sin y - y) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop) ?_
    intro z _
    have h1 : HasDerivAt (fun y : ℝ => y ^ 3 / 6) (3 * z ^ 2 / 6) z := by
      simpa using (hasDerivAt_pow 3 z).div_const 6
    have hd : HasDerivAt (fun y : ℝ => y ^ 3 / 6 + Real.sin y - y)
        (3 * z ^ 2 / 6 + Real.cos z - 1) z :=
      (h1.add (Real.hasDerivAt_sin z)).sub (hasDerivAt_id z)
    rw [hd.deriv]
    have := Real.one_sub_sq_div_two_le_cos (x := z)
    nlinarith
  simpa using hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy

/-- The global quartic upper bound `cos x ≤ 1 − x²/2 + x⁴/24`. -/
theorem cos_le_quartic (x : ℝ) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have key : ∀ y : ℝ, 0 ≤ y → Real.cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 / 24 := by
    have hmono2 : MonotoneOn (fun y : ℝ => 1 - y ^ 2 / 2 + y ^ 4 / 24 - Real.cos y)
        (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop) ?_
      intro z hz
      rw [interior_Ici] at hz
      have hz' : (0 : ℝ) ≤ z := le_of_lt hz
      have h1 : HasDerivAt (fun y : ℝ => 1 - y ^ 2 / 2) (-(2 * z / 2)) z := by
        simpa using ((hasDerivAt_pow 2 z).div_const 2).const_sub 1
      have h2 : HasDerivAt (fun y : ℝ => y ^ 4 / 24) (4 * z ^ 3 / 24) z := by
        simpa using (hasDerivAt_pow 4 z).div_const 24
      have hd : HasDerivAt (fun y : ℝ => 1 - y ^ 2 / 2 + y ^ 4 / 24 - Real.cos y)
          (-(2 * z / 2) + 4 * z ^ 3 / 24 - -Real.sin z) z :=
        (h1.add h2).sub (Real.hasDerivAt_cos z)
      rw [hd.deriv]
      have := cubic_le_sin hz'
      nlinarith
    intro y hy
    have h := hmono2 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
    norm_num at h
    linarith
  rcases le_total 0 x with h | h
  · exact key x h
  · have h' := key (-x) (by linarith)
    rw [Real.cos_neg] at h'
    linarith [h']

/-- **The global second-order Taylor bound for the cosine.** -/
theorem abs_cos_sub_quadratic_le (x : ℝ) :
    |Real.cos x - (1 - x ^ 2 / 2)| ≤ x ^ 4 / 24 := by
  have h1 := cos_le_quartic x
  have h2 := Real.one_sub_sq_div_two_le_cos (x := x)
  rw [abs_le]
  constructor <;> linarith

/-! ## Cosh moments of the taper -/

/-- `M_y = ∫ g(u) cosh(yu) du`. -/
def coshMoment (g : ℝ → ℝ) (y : ℝ) : ℝ := ∫ u : ℝ, g u * Real.cosh (y * u)

/-- `N_y = ∫ g(u) u² cosh(yu) du`. -/
def sqCoshMoment (g : ℝ → ℝ) (y : ℝ) : ℝ := ∫ u : ℝ, g u * (u ^ 2 * Real.cosh (y * u))

/-- `Q⁰_y = ∫ |g(u)| cosh(yu) du`. -/
def absMom0 (g : ℝ → ℝ) (y : ℝ) : ℝ := ∫ u : ℝ, |g u| * Real.cosh (y * u)

/-- `Q²_y = ∫ |g(u)| u² cosh(yu) du`. -/
def absMom2 (g : ℝ → ℝ) (y : ℝ) : ℝ := ∫ u : ℝ, |g u| * (u ^ 2 * Real.cosh (y * u))

/-- `Q⁴_y = ∫ |g(u)| u⁴ cosh(yu) du`. -/
def absMom4 (g : ℝ → ℝ) (y : ℝ) : ℝ := ∫ u : ℝ, |g u| * (u ^ 4 * Real.cosh (y * u))

theorem absMom0_nonneg (g : ℝ → ℝ) (y : ℝ) : 0 ≤ absMom0 g y :=
  integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (Real.cosh_pos _).le

theorem absMom2_nonneg (g : ℝ → ℝ) (y : ℝ) : 0 ≤ absMom2 g y :=
  integral_nonneg fun u =>
    mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (Real.cosh_pos _).le)

theorem absMom4_nonneg (g : ℝ → ℝ) (y : ℝ) : 0 ≤ absMom4 g y :=
  integral_nonneg fun u =>
    mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (Real.cosh_pos _).le)

/-- A uniform majorization device for taper integrals. -/
theorem abs_integral_taper_le {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {h w : ℝ → ℝ} (hh : Continuous h) (hw : Continuous w) (hle : ∀ u, |h u| ≤ w u) :
    |∫ u : ℝ, g u * h u| ≤ ∫ u : ℝ, |g u| * w u := by
  have hint : Integrable (fun u : ℝ => g u * h u) := taper_integrable hg hgc hh
  have hdom : Integrable (fun u : ℝ => |g u| * w u) :=
    taper_integrable hg.abs hgc.abs hw
  refine le_trans (abs_integral_le_integral_abs) (integral_mono hint.abs hdom ?_)
  intro u
  show |g u * h u| ≤ |g u| * w u
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hle u) (abs_nonneg _)

theorem abs_evenResp_le {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (y s : ℝ) : |evenResp g y s| ≤ absMom0 g y := by
  refine abs_integral_taper_le hg hgc (by fun_prop) (by fun_prop) ?_
  intro u
  calc |Real.cosh (y * u) * Real.cos (s * u)|
      = Real.cosh (y * u) * |Real.cos (s * u)| := by
        rw [abs_mul, abs_of_pos (Real.cosh_pos _)]
    _ ≤ Real.cosh (y * u) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.cosh_pos _).le
    _ = Real.cosh (y * u) := mul_one _

theorem abs_coshMoment_le {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (y : ℝ) : |coshMoment g y| ≤ absMom0 g y := by
  refine abs_integral_taper_le hg hgc (by fun_prop) (by fun_prop) ?_
  intro u
  exact le_of_eq (abs_of_pos (Real.cosh_pos _))

theorem abs_sqCoshMoment_le {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (y : ℝ) : |sqCoshMoment g y| ≤ absMom2 g y := by
  refine abs_integral_taper_le hg hgc (by fun_prop) (by fun_prop) ?_
  intro u
  exact le_of_eq (abs_of_nonneg (by positivity))

/-! ## The quartic remainder of the even response -/

/-- **The even response is its own second-order Taylor polynomial in the sampling
radius, up to a quartic remainder.** -/
theorem abs_evenResp_sub_quadratic_le {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (y s : ℝ) :
    |evenResp g y s - (coshMoment g y - s ^ 2 / 2 * sqCoshMoment g y)|
      ≤ s ^ 4 / 24 * absMom4 g y := by
  have h1 : Integrable (fun u : ℝ => g u * (Real.cosh (y * u) * Real.cos (s * u))) :=
    taper_integrable hg hgc (by fun_prop)
  have h2 : Integrable (fun u : ℝ => g u * Real.cosh (y * u)) :=
    taper_integrable hg hgc (by fun_prop)
  have h3 : Integrable (fun u : ℝ => g u * (u ^ 2 * Real.cosh (y * u))) :=
    taper_integrable hg hgc (by fun_prop)
  have hEq : (∫ u : ℝ, g u *
        (Real.cosh (y * u) * (Real.cos (s * u) - (1 - (s * u) ^ 2 / 2))))
      = evenResp g y s - (coshMoment g y - s ^ 2 / 2 * sqCoshMoment g y) := by
    have hfun : (fun u : ℝ => g u *
          (Real.cosh (y * u) * (Real.cos (s * u) - (1 - (s * u) ^ 2 / 2))))
        = (fun u : ℝ => (g u * (Real.cosh (y * u) * Real.cos (s * u))
              - g u * Real.cosh (y * u)) + s ^ 2 / 2 * (g u * (u ^ 2 * Real.cosh (y * u)))) :=
      funext fun u => by ring
    have hi : Integrable (fun u : ℝ => g u * (Real.cosh (y * u) * Real.cos (s * u))
        - g u * Real.cosh (y * u)) := h1.sub h2
    have hj : Integrable (fun u : ℝ =>
        s ^ 2 / 2 * (g u * (u ^ 2 * Real.cosh (y * u)))) := h3.const_mul _
    rw [hfun]
    rw [integral_add hi hj]
    rw [integral_sub h1 h2]
    rw [integral_const_mul]
    unfold evenResp coshMoment sqCoshMoment
    ring
  rw [← hEq]
  have hbound :
      |∫ u : ℝ, g u * (Real.cosh (y * u) * (Real.cos (s * u) - (1 - (s * u) ^ 2 / 2)))|
        ≤ ∫ u : ℝ, |g u| * (s ^ 4 / 24 * (u ^ 4 * Real.cosh (y * u))) := by
    refine abs_integral_taper_le hg hgc (by fun_prop) (by fun_prop) ?_
    intro u
    calc |Real.cosh (y * u) * (Real.cos (s * u) - (1 - (s * u) ^ 2 / 2))|
        = Real.cosh (y * u) * |Real.cos (s * u) - (1 - (s * u) ^ 2 / 2)| := by
          rw [abs_mul, abs_of_pos (Real.cosh_pos _)]
      _ ≤ Real.cosh (y * u) * ((s * u) ^ 4 / 24) :=
          mul_le_mul_of_nonneg_left (abs_cos_sub_quadratic_le _) (Real.cosh_pos _).le
      _ = s ^ 4 / 24 * (u ^ 4 * Real.cosh (y * u)) := by ring
  refine hbound.trans (le_of_eq ?_)
  have hfun2 : (fun u : ℝ => |g u| * (s ^ 4 / 24 * (u ^ 4 * Real.cosh (y * u))))
      = (fun u : ℝ => s ^ 4 / 24 * (|g u| * (u ^ 4 * Real.cosh (y * u)))) :=
    funext fun u => by ring
  rw [hfun2, integral_const_mul]
  rfl

/-! ## The leading coefficient of the two-radius height defect -/

/-- The leading `r²` coefficient of `heightDefect g r a 0`. -/
def targetLeadingCoeff (g : ℝ → ℝ) (a : ℝ) : ℝ :=
  3 / 2 * (sqCoshMoment g a * coshMoment g 0 - coshMoment g a * sqCoshMoment g 0)

/-- An explicit coefficient for the quartic remainder of `heightDefect g r a 0`. -/
def defectRemainderCoeff (g : ℝ → ℝ) (a : ℝ) : ℝ :=
  (17 * (absMom4 g a * absMom0 g 0 + absMom0 g a * absMom4 g 0)
    + 10 * (absMom2 g a * absMom4 g 0)) / 24

theorem defectRemainderCoeff_nonneg (g : ℝ → ℝ) (a : ℝ) : 0 ≤ defectRemainderCoeff g a := by
  have h1 := absMom0_nonneg g a
  have h2 := absMom0_nonneg g 0
  have h3 := absMom2_nonneg g a
  have h4 := absMom4_nonneg g a
  have h5 := absMom4_nonneg g 0
  unfold defectRemainderCoeff
  positivity

/-- A determinant-level product estimate. -/
theorem abs_mul_sub_mul_le {x x' y y' bx by' cx cy : ℝ}
    (h1 : |x - x'| ≤ cx) (h2 : |y| ≤ by') (h3 : |x'| ≤ bx) (h4 : |y - y'| ≤ cy)
    (hbx : 0 ≤ bx) (hcx : 0 ≤ cx) :
    |x * y - x' * y'| ≤ cx * by' + bx * cy := by
  have hsplit : x * y - x' * y' = (x - x') * y + x' * (y - y') := by ring
  have hb1 : |x - x'| * |y| ≤ cx * by' :=
    mul_le_mul h1 h2 (abs_nonneg _) hcx
  have hb2 : |x'| * |y - y'| ≤ bx * cy :=
    mul_le_mul h3 h4 (abs_nonneg _) hbx
  calc |x * y - x' * y'| = |(x - x') * y + x' * (y - y')| := by rw [hsplit]
    _ ≤ |(x - x') * y| + |x' * (y - y')| := abs_add_le _ _
    _ = |x - x'| * |y| + |x'| * |y - y'| := by rw [abs_mul, abs_mul]
    _ ≤ cx * by' + bx * cy := by linarith


/-- **The abstract two-radius determinant remainder estimate.**  Purely algebraic:
given second-order approximations of the four responses with quartic remainders and
uniform size bounds, the two-radius determinant differs from its leading `r²` term
by at most `r⁴` times an explicit combination of the majorants. -/
theorem det_remainder_bound {A1 A2 B1 B2 Ma Na M0 N0 Q0a Q2a Q4a Q00 Q40 r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hA1 : |A1 - (Ma - r ^ 2 / 2 * Na)| ≤ r ^ 4 / 24 * Q4a)
    (hA2 : |A2 - (Ma - (2 * r) ^ 2 / 2 * Na)| ≤ (2 * r) ^ 4 / 24 * Q4a)
    (hB1 : |B1 - (M0 - r ^ 2 / 2 * N0)| ≤ r ^ 4 / 24 * Q40)
    (hB2 : |B2 - (M0 - (2 * r) ^ 2 / 2 * N0)| ≤ (2 * r) ^ 4 / 24 * Q40)
    (hB1' : |B1| ≤ Q00) (hB2' : |B2| ≤ Q00)
    (hMa : |Ma| ≤ Q0a) (hNa : |Na| ≤ Q2a)
    (hQ0a : 0 ≤ Q0a) (hQ2a : 0 ≤ Q2a) (hQ4a : 0 ≤ Q4a) (hQ40 : 0 ≤ Q40) :
    |A1 * B2 - A2 * B1 - r ^ 2 * (3 / 2 * (Na * M0 - Ma * N0))|
      ≤ r ^ 4 * ((17 * (Q4a * Q00 + Q0a * Q40) + 10 * (Q2a * Q40)) / 24) := by
  have hPa1B : |Ma - r ^ 2 / 2 * Na| ≤ Q0a + r ^ 2 / 2 * Q2a := by
    have hstep : |Ma - r ^ 2 / 2 * Na| ≤ |Ma| + |r ^ 2 / 2 * Na| := abs_sub _ _
    have hmul : |r ^ 2 / 2 * Na| = r ^ 2 / 2 * |Na| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ 2 / 2)]
    have hle : r ^ 2 / 2 * |Na| ≤ r ^ 2 / 2 * Q2a :=
      mul_le_mul_of_nonneg_left hNa (by positivity)
    linarith [hstep, hmul.le, hmul.ge]
  have hPa2B : |Ma - (2 * r) ^ 2 / 2 * Na| ≤ Q0a + (2 * r) ^ 2 / 2 * Q2a := by
    have hstep : |Ma - (2 * r) ^ 2 / 2 * Na| ≤ |Ma| + |(2 * r) ^ 2 / 2 * Na| := abs_sub _ _
    have hmul : |(2 * r) ^ 2 / 2 * Na| = (2 * r) ^ 2 / 2 * |Na| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * r) ^ 2 / 2)]
    have hle : (2 * r) ^ 2 / 2 * |Na| ≤ (2 * r) ^ 2 / 2 * Q2a :=
      mul_le_mul_of_nonneg_left hNa (by positivity)
    linarith [hstep, hmul.le, hmul.ge]
  have key1 : |A1 * B2 - (Ma - r ^ 2 / 2 * Na) * (M0 - (2 * r) ^ 2 / 2 * N0)|
      ≤ (r ^ 4 / 24 * Q4a) * Q00
        + (Q0a + r ^ 2 / 2 * Q2a) * ((2 * r) ^ 4 / 24 * Q40) :=
    abs_mul_sub_mul_le hA1 hB2' hPa1B hB2
      (add_nonneg hQ0a (mul_nonneg (by positivity) hQ2a)) (mul_nonneg (by positivity) hQ4a)
  have key2 : |A2 * B1 - (Ma - (2 * r) ^ 2 / 2 * Na) * (M0 - r ^ 2 / 2 * N0)|
      ≤ ((2 * r) ^ 4 / 24 * Q4a) * Q00
        + (Q0a + (2 * r) ^ 2 / 2 * Q2a) * (r ^ 4 / 24 * Q40) :=
    abs_mul_sub_mul_le hA2 hB1' hPa2B hB1
      (add_nonneg hQ0a (mul_nonneg (by positivity) hQ2a)) (mul_nonneg (by positivity) hQ4a)
  have hsplit : A1 * B2 - A2 * B1 - r ^ 2 * (3 / 2 * (Na * M0 - Ma * N0))
      = (A1 * B2 - (Ma - r ^ 2 / 2 * Na) * (M0 - (2 * r) ^ 2 / 2 * N0))
        - (A2 * B1 - (Ma - (2 * r) ^ 2 / 2 * Na) * (M0 - r ^ 2 / 2 * N0)) := by ring
  have htri : |A1 * B2 - A2 * B1 - r ^ 2 * (3 / 2 * (Na * M0 - Ma * N0))|
      ≤ |A1 * B2 - (Ma - r ^ 2 / 2 * Na) * (M0 - (2 * r) ^ 2 / 2 * N0)|
        + |A2 * B1 - (Ma - (2 * r) ^ 2 / 2 * Na) * (M0 - r ^ 2 / 2 * N0)| := by
    rw [hsplit]; exact abs_sub _ _
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hr4 : (0:ℝ) ≤ r ^ 4 := by positivity
  have hr6 : r ^ 6 ≤ r ^ 4 := by
    nlinarith [mul_nonneg hr4 (sub_nonneg.2 hr2)]
  have hkey : 10 / 24 * (Q2a * Q40) * r ^ 6 ≤ 10 / 24 * (Q2a * Q40) * r ^ 4 :=
    mul_le_mul_of_nonneg_left hr6 (mul_nonneg (by norm_num) (mul_nonneg hQ2a hQ40))
  linarith [htri, key1, key2, hkey]

/-- **The two-radius height defect is quadratically small, with leading coefficient
`targetLeadingCoeff` and an explicit quartic remainder.** -/
theorem abs_heightDefect_sub_leading_le {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (a r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |heightDefect g r a 0 - r ^ 2 * targetLeadingCoeff g a|
      ≤ r ^ 4 * defectRemainderCoeff g a :=
  det_remainder_bound hr0 hr1
    (abs_evenResp_sub_quadratic_le hg hgc a r)
    (abs_evenResp_sub_quadratic_le hg hgc a (2 * r))
    (abs_evenResp_sub_quadratic_le hg hgc 0 r)
    (abs_evenResp_sub_quadratic_le hg hgc 0 (2 * r))
    (abs_evenResp_le hg hgc 0 r) (abs_evenResp_le hg hgc 0 (2 * r))
    (abs_coshMoment_le hg hgc a) (abs_sqCoshMoment_le hg hgc a)
    (absMom0_nonneg g a) (absMom2_nonneg g a) (absMom4_nonneg g a)
    (absMom4_nonneg g 0)


/-! ## The gate inequality as a coefficient comparison -/

/-- The leading `r²` coefficient of `zeroHeightDefect g r ρ`. -/
def zeroLeadingCoeff (g : ℝ → ℝ) (ρ : Zeros) : ℝ :=
  2 * ((Zeta23.zetaZeroConfig).mult ρ : ℝ) * targetLeadingCoeff g (heightOf ρ)

/-- The remainder coefficient of `zeroHeightDefect g r ρ`. -/
def zeroRemainderCoeff (g : ℝ → ℝ) (ρ : Zeros) : ℝ :=
  2 * ((Zeta23.zetaZeroConfig).mult ρ : ℝ) * defectRemainderCoeff g (heightOf ρ)

/-- **The per-zero signal is quadratically small with an explicit leading
coefficient.** -/
theorem abs_zeroHeightDefect_sub_leading_le {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (ρ : Zeros) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |zeroHeightDefect g r ρ - r ^ 2 * zeroLeadingCoeff g ρ|
      ≤ r ^ 4 * zeroRemainderCoeff g ρ := by
  set m : ℝ := ((Zeta23.zetaZeroConfig).mult ρ : ℝ) with hm
  have hm0 : 0 ≤ m := by positivity
  have hbase := abs_heightDefect_sub_leading_le hg hgc (heightOf ρ) r hr0 hr1
  have hEq : zeroHeightDefect g r ρ - r ^ 2 * zeroLeadingCoeff g ρ
      = 2 * m * (heightDefect g r (heightOf ρ) 0 - r ^ 2 * targetLeadingCoeff g (heightOf ρ)) := by
    unfold zeroHeightDefect zeroLeadingCoeff
    rw [← hm]; ring
  rw [hEq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * m)]
  unfold zeroRemainderCoeff
  rw [← hm]
  have := mul_le_mul_of_nonneg_left hbase (by positivity : (0:ℝ) ≤ 2 * m)
  nlinarith [this]

/-- **The gate inequality is now a comparison of coefficients.**

If the projectivized residual coefficient `E` is beaten by the target's own
leading coefficient, with enough room to absorb the quartic remainder at the
sampling radius actually used, then the gate inequality

    r² · E  <  D_{ρ*}(r)

holds.  Both sides carry the same power of `r`; the projective tranche is exactly
what made that true. -/
theorem gate_of_coefficientComparison {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (ρ : Zeros) (r E : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hcmp : E + r ^ 2 * zeroRemainderCoeff g ρ < zeroLeadingCoeff g ρ) :
    r ^ 2 * E < zeroHeightDefect g r ρ := by
  have hbase := abs_zeroHeightDefect_sub_leading_le hg hgc ρ r hr0.le hr1
  have hlow : r ^ 2 * zeroLeadingCoeff g ρ - r ^ 4 * zeroRemainderCoeff g ρ
      ≤ zeroHeightDefect g r ρ := by
    have := abs_le.1 hbase
    linarith [this.1]
  have hr2 : 0 < r ^ 2 := by positivity
  nlinarith [hcmp, hlow, hr2]

end LiteralWeilTargetDefectLeadingCoefficient
end Zeta23Bridge
