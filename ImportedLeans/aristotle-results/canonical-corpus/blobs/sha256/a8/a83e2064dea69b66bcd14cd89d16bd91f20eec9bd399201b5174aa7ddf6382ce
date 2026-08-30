/-
# The strip constant of the projective taper is `O(r²)`

The off-ordinate projective envelope of `LiteralWeilOffOrdinateProjectiveTail` reads

    |𝔇_{Z_off}(r)| ≤ 4 · stripConst (sampleTest h_r t 0) Λ · W(t),        h_r = g · B_r,

so the whole quadratic gain of the projective method is located in the strip
constant of the projective taper.  This module proves

    stripConst (sampleTest (projTaper g r) t 0) Λ ≤ r² · projStripCoeff g Λ t

with a completely explicit coefficient that does not depend on `r`.

Two ingredients.

* **The twist is unimodular and its two derivatives are elementary.**  For
  `k(u) = h(u) e^{icu}`,

      ‖k‖₁ = ‖h‖₁,        ‖k''‖₁ ≤ ‖h''‖₁ + 2|c| ‖h'‖₁ + c² ‖h‖₁.

* **All three derivatives of the bracket are `O(r²)` on the support**, which is the
  content of `LiteralWeilProjectiveTaper`; the Leibniz rule therefore makes
  `‖h_r‖₁`, `‖h_r'‖₁` and `‖h_r''‖₁` all `O(r²)`.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilOffOrdinateProjectiveTail

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilProjectiveStripConstant

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilOffOrdinateTail
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilProjectiveTaper

/-! ## The unimodular twist -/

/-- The twist `e^{icu}` by which a real taper is turned into a sample test function. -/
def twist (c : ℝ) : ℝ → ℂ := fun u => Complex.exp (Complex.I * ((c * u : ℝ) : ℂ))

theorem sampleTest_eq_twist (g : ℝ → ℝ) (t s : ℝ) :
    sampleTest g t s = fun u => (g u : ℂ) * twist (s - t) u := rfl

theorem norm_twist (c u : ℝ) : ‖twist c u‖ = 1 := by
  unfold twist
  rw [Complex.norm_exp]
  simp

theorem hasDerivAt_twist (c u : ℝ) :
    HasDerivAt (twist c) (twist c u * (Complex.I * c)) u := by
  have h1 : HasDerivAt (fun v : ℝ => ((c * v : ℝ) : ℂ)) (c : ℂ) u := by
    simpa using (((hasDerivAt_id u).const_mul c).ofReal_comp)
  exact (h1.const_mul Complex.I).cexp

/-! ## The two derivatives of a twisted real taper -/

/-- The first derivative of `u ↦ h(u) e^{icu}`. -/
def twistDeriv (h : ℝ → ℝ) (c : ℝ) : ℝ → ℂ := fun u =>
  (((deriv h u : ℝ) : ℂ) + ((h u : ℝ) : ℂ) * (Complex.I * c)) * twist c u

/-- The second derivative of `u ↦ h(u) e^{icu}`. -/
def twistDeriv2 (h : ℝ → ℝ) (c : ℝ) : ℝ → ℂ := fun u =>
  (((deriv (deriv h) u : ℝ) : ℂ) + 2 * ((deriv h u : ℝ) : ℂ) * (Complex.I * c)
      + ((h u : ℝ) : ℂ) * (Complex.I * c) ^ 2) * twist c u

theorem hasDerivAt_twistMul {h : ℝ → ℝ} {u : ℝ} (hh : DifferentiableAt ℝ h u) (c : ℝ) :
    HasDerivAt (fun v : ℝ => ((h v : ℝ) : ℂ) * twist c v) (twistDeriv h c u) u := by
  have hd := (hh.hasDerivAt.ofReal_comp).mul (hasDerivAt_twist c u)
  have hrw : ((deriv h u : ℝ) : ℂ) * twist c u
      + ((h u : ℝ) : ℂ) * (twist c u * (Complex.I * c)) = twistDeriv h c u := by
    unfold twistDeriv; ring
  rwa [hrw] at hd

theorem hasDerivAt_twistDeriv {h : ℝ → ℝ} {u : ℝ} (h1 : DifferentiableAt ℝ h u)
    (h2 : DifferentiableAt ℝ (deriv h) u) (c : ℝ) :
    HasDerivAt (twistDeriv h c) (twistDeriv2 h c u) u := by
  have hF : HasDerivAt (fun v : ℝ => ((deriv h v : ℝ) : ℂ) + ((h v : ℝ) : ℂ) * (Complex.I * c))
      (((deriv (deriv h) u : ℝ) : ℂ) + ((deriv h u : ℝ) : ℂ) * (Complex.I * c)) u :=
    (h2.hasDerivAt.ofReal_comp).add ((h1.hasDerivAt.ofReal_comp).mul_const _)
  have hd := hF.mul (hasDerivAt_twist c u)
  have hrw : (((deriv (deriv h) u : ℝ) : ℂ) + ((deriv h u : ℝ) : ℂ) * (Complex.I * c))
        * twist c u
      + (((deriv h u : ℝ) : ℂ) + ((h u : ℝ) : ℂ) * (Complex.I * c))
        * (twist c u * (Complex.I * c)) = twistDeriv2 h c u := by
    unfold twistDeriv2; ring
  rw [hrw] at hd
  exact hd

theorem deriv_twistMul {h : ℝ → ℝ} (hh : Differentiable ℝ h) (c : ℝ) :
    deriv (fun v : ℝ => ((h v : ℝ) : ℂ) * twist c v) = twistDeriv h c :=
  funext fun u => (hasDerivAt_twistMul (hh u) c).deriv

theorem deriv2_twistMul {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) (c : ℝ) :
    deriv (deriv (fun v : ℝ => ((h v : ℝ) : ℂ) * twist c v)) = twistDeriv2 h c := by
  have hdiff : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hdiff2 : Differentiable ℝ (deriv h) := hh.differentiable_deriv_two
  rw [deriv_twistMul hdiff c]
  exact funext fun u => (hasDerivAt_twistDeriv (hdiff u) (hdiff2 u) c).deriv

/-! ## Pointwise norms -/

theorem norm_twistMul (h : ℝ → ℝ) (c u : ℝ) : ‖((h u : ℝ) : ℂ) * twist c u‖ = |h u| := by
  rw [norm_mul, norm_twist, Complex.norm_real, Real.norm_eq_abs, mul_one]

theorem norm_twistDeriv2_le (h : ℝ → ℝ) (c u : ℝ) :
    ‖twistDeriv2 h c u‖
      ≤ |deriv (deriv h) u| + 2 * |c| * |deriv h u| + c ^ 2 * |h u| := by
  have hIc : ‖(Complex.I * (c : ℂ))‖ = |c| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have e1 : ‖((deriv (deriv h) u : ℝ) : ℂ)‖ = |deriv (deriv h) u| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have e2 : ‖2 * ((deriv h u : ℝ) : ℂ) * (Complex.I * c)‖ = 2 * |c| * |deriv h u| := by
    rw [norm_mul, norm_mul, hIc, Complex.norm_real, Real.norm_eq_abs,
      show ‖(2 : ℂ)‖ = 2 by norm_num]
    ring
  have e3 : ‖((h u : ℝ) : ℂ) * (Complex.I * (c : ℂ)) ^ 2‖ = c ^ 2 * |h u| := by
    rw [norm_mul, norm_pow, hIc, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  unfold twistDeriv2
  rw [norm_mul, norm_twist, mul_one]
  calc ‖((deriv (deriv h) u : ℝ) : ℂ) + 2 * ((deriv h u : ℝ) : ℂ) * (Complex.I * c)
          + ((h u : ℝ) : ℂ) * (Complex.I * c) ^ 2‖
      ≤ ‖((deriv (deriv h) u : ℝ) : ℂ) + 2 * ((deriv h u : ℝ) : ℂ) * (Complex.I * c)‖
          + ‖((h u : ℝ) : ℂ) * (Complex.I * (c : ℂ)) ^ 2‖ := norm_add_le _ _
    _ ≤ (‖((deriv (deriv h) u : ℝ) : ℂ)‖ + ‖2 * ((deriv h u : ℝ) : ℂ) * (Complex.I * c)‖)
          + ‖((h u : ℝ) : ℂ) * (Complex.I * (c : ℂ)) ^ 2‖ := by
        gcongr
        exact norm_add_le _ _
    _ = |deriv (deriv h) u| + 2 * |c| * |deriv h u| + c ^ 2 * |h u| := by
        rw [e1, e2, e3]


/-! ## Support radii, compact support and integrability -/

/-- A support radius forces compact support. -/
theorem hasCompactSupport_of_radius {E : Type*} [Zero E] [TopologicalSpace E] {f : ℝ → E} {Λ : ℝ}
    (h : ∀ u, f u ≠ 0 → |u| ≤ Λ) : HasCompactSupport f := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -Λ) (b := Λ))
  intro x hx
  by_contra hne
  have hb := abs_le.mp (h x hne)
  exact hx ⟨hb.1, hb.2⟩

/-- The derivative inherits the support radius. -/
theorem support_radius_deriv {f : ℝ → ℝ} {Λ : ℝ} (h : ∀ u, f u ≠ 0 → |u| ≤ Λ) :
    ∀ u, deriv f u ≠ 0 → |u| ≤ Λ := by
  intro u hu
  have hsub : Function.support f ⊆ {v : ℝ | |v| ≤ Λ} := fun v hv => h v hv
  have hclosed : IsClosed {v : ℝ | |v| ≤ Λ} := isClosed_le continuous_abs continuous_const
  have hts : tsupport f ⊆ {v : ℝ | |v| ≤ Λ} := closure_minimal hsub hclosed
  exact hts (support_deriv_subset (Function.mem_support.mpr hu))

theorem contDiff_one_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) : ContDiff ℝ 1 (deriv g) :=
  hg.deriv'

theorem continuous_deriv2 {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) : Continuous (deriv (deriv g)) :=
  (contDiff_one_deriv hg).continuous_deriv_one

/-! ## The two derivatives of the projective taper -/

/-- The first derivative of `h_r = g B_r`. -/
def projTaperDeriv (g : ℝ → ℝ) (r : ℝ) : ℝ → ℝ := fun u =>
  deriv g u * twoRadiusBracket g r u + g u * bracketDeriv g r u

/-- The closed form of the second derivative of the bracket. -/
def bracketDeriv2 (g : ℝ → ℝ) (r : ℝ) : ℝ → ℝ := fun u =>
  evenResp g 0 r * (-(Real.cos (2 * r * u) * (2 * r)) * (2 * r))
    - evenResp g 0 (2 * r) * (-(Real.cos (r * u) * r) * r)

theorem deriv2_twoRadiusBracket (g : ℝ → ℝ) (r : ℝ) :
    deriv (deriv (twoRadiusBracket g r)) = bracketDeriv2 g r := by
  rw [deriv_twoRadiusBracket]
  exact funext fun u => (hasDerivAt_bracketDeriv g r u).deriv

theorem bracketDeriv_continuous (g : ℝ → ℝ) (r : ℝ) : Continuous (bracketDeriv g r) := by
  unfold bracketDeriv; fun_prop

theorem bracketDeriv2_continuous (g : ℝ → ℝ) (r : ℝ) : Continuous (bracketDeriv2 g r) := by
  unfold bracketDeriv2; fun_prop

/-- The second derivative of `h_r = g B_r`. -/
def projTaperDeriv2 (g : ℝ → ℝ) (r : ℝ) : ℝ → ℝ := fun u =>
  deriv (deriv g) u * twoRadiusBracket g r u + 2 * (deriv g u * bracketDeriv g r u)
    + g u * bracketDeriv2 g r u

theorem deriv_projTaper {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (r : ℝ) :
    deriv (projTaper g r) = projTaperDeriv g r := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  refine funext fun u => ?_
  exact ((hd u).hasDerivAt.mul (hasDerivAt_twoRadiusBracket g r u)).deriv

theorem deriv2_projTaper {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (r : ℝ) :
    deriv (deriv (projTaper g r)) = projTaperDeriv2 g r := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv g) := hg.differentiable_deriv_two
  rw [deriv_projTaper hg r]
  refine funext fun u => ?_
  have hval : HasDerivAt (projTaperDeriv g r)
      (deriv (deriv g) u * twoRadiusBracket g r u + deriv g u * bracketDeriv g r u
        + (deriv g u * bracketDeriv g r u + g u * bracketDeriv2 g r u)) u :=
    ((hd2 u).hasDerivAt.mul (hasDerivAt_twoRadiusBracket g r u)).add
      ((hd u).hasDerivAt.mul (hasDerivAt_bracketDeriv g r u))
  rw [hval.deriv]
  unfold projTaperDeriv2
  ring

/-! ## The quadratic mass bounds for the projective taper -/

/-- The uniform quadratic bracket bound `β = 5 r² (1+Λ)² ‖g‖₁`. -/
def bracketBound (g : ℝ → ℝ) (Λ r : ℝ) : ℝ := 5 * r ^ 2 * (1 + Λ) ^ 2 * taperMass g

theorem bracketBound_nonneg (g : ℝ → ℝ) (Λ r : ℝ) (hΛ : 0 ≤ Λ) : 0 ≤ bracketBound g Λ r := by
  have := taperMass_nonneg g
  unfold bracketBound
  positivity

theorem abs_bracket_le_bound {g : ℝ → ℝ} {Λ : ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (r : ℝ) {u : ℝ} (hu : |u| ≤ Λ) :
    |twoRadiusBracket g r u| ≤ bracketBound g Λ r := by
  have hM := taperMass_nonneg g
  have h := abs_twoRadiusBracket_le hg hgc hsupp r hu
  have : 5 * r ^ 2 * Λ ^ 2 * taperMass g ≤ bracketBound g Λ r := by
    unfold bracketBound
    nlinarith [mul_nonneg (sq_nonneg r) hM, mul_nonneg (mul_nonneg (sq_nonneg r) hM) hΛ,
      mul_nonneg (mul_nonneg (sq_nonneg r) hM) (sq_nonneg Λ)]
  linarith

theorem abs_bracketDeriv_le_bound {g : ℝ → ℝ} {Λ : ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hΛ : 0 ≤ Λ) (r : ℝ) {u : ℝ} (hu : |u| ≤ Λ) :
    |bracketDeriv g r u| ≤ bracketBound g Λ r := by
  have hM := taperMass_nonneg g
  have h := abs_deriv_twoRadiusBracket_le hg hgc r hu
  rw [deriv_twoRadiusBracket] at h
  have : 5 * r ^ 2 * Λ * taperMass g ≤ bracketBound g Λ r := by
    unfold bracketBound
    nlinarith [mul_nonneg (sq_nonneg r) hM, mul_nonneg (mul_nonneg (sq_nonneg r) hM) hΛ,
      mul_nonneg (mul_nonneg (sq_nonneg r) hM) (sq_nonneg Λ)]
  linarith

theorem abs_bracketDeriv2_le_bound {g : ℝ → ℝ} {Λ : ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hΛ : 0 ≤ Λ) (r u : ℝ) :
    |bracketDeriv2 g r u| ≤ bracketBound g Λ r := by
  have hM := taperMass_nonneg g
  have h := abs_deriv2_twoRadiusBracket_le hg hgc r u
  rw [deriv2_twoRadiusBracket] at h
  have : 5 * r ^ 2 * taperMass g ≤ bracketBound g Λ r := by
    unfold bracketBound
    nlinarith [mul_nonneg (sq_nonneg r) hM, mul_nonneg (mul_nonneg (sq_nonneg r) hM) hΛ,
      mul_nonneg (mul_nonneg (sq_nonneg r) hM) (sq_nonneg Λ)]
  linarith


/-! ### Pointwise quadratic bounds -/

theorem abs_projTaper_le {g : ℝ → ℝ} {Λ : ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (r u : ℝ) :
    |projTaper g r u| ≤ bracketBound g Λ r * |g u| := by
  by_cases hu : |u| ≤ Λ
  · have hB := abs_bracket_le_bound hg hgc hsupp hΛ r hu
    unfold projTaper
    rw [abs_mul]
    calc |g u| * |twoRadiusBracket g r u| ≤ |g u| * bracketBound g Λ r :=
          mul_le_mul_of_nonneg_left hB (abs_nonneg _)
      _ = bracketBound g Λ r * |g u| := by ring
  · have h1 : g u = 0 := by by_contra h; exact hu (hsupp u h)
    simp [projTaper, h1]

theorem abs_projTaperDeriv_le {g : ℝ → ℝ} {Λ : ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (r u : ℝ) :
    |projTaperDeriv g r u| ≤ bracketBound g Λ r * (|deriv g u| + |g u|) := by
  by_cases hu : |u| ≤ Λ
  · have hB := abs_bracket_le_bound hg hgc hsupp hΛ r hu
    have hB' := abs_bracketDeriv_le_bound hg hgc hΛ r hu
    have hβ := bracketBound_nonneg g Λ r hΛ
    have e1 : |deriv g u * twoRadiusBracket g r u| ≤ bracketBound g Λ r * |deriv g u| := by
      rw [abs_mul]
      calc |deriv g u| * |twoRadiusBracket g r u| ≤ |deriv g u| * bracketBound g Λ r :=
            mul_le_mul_of_nonneg_left hB (abs_nonneg _)
        _ = bracketBound g Λ r * |deriv g u| := by ring
    have e2 : |g u * bracketDeriv g r u| ≤ bracketBound g Λ r * |g u| := by
      rw [abs_mul]
      calc |g u| * |bracketDeriv g r u| ≤ |g u| * bracketBound g Λ r :=
            mul_le_mul_of_nonneg_left hB' (abs_nonneg _)
        _ = bracketBound g Λ r * |g u| := by ring
    have hadd := abs_add_le (deriv g u * twoRadiusBracket g r u) (g u * bracketDeriv g r u)
    unfold projTaperDeriv
    nlinarith [hadd, e1, e2]
  · have h1 : g u = 0 := by by_contra h; exact hu (hsupp u h)
    have h2 : deriv g u = 0 := by by_contra h; exact hu (support_radius_deriv hsupp u h)
    simp [projTaperDeriv, h1, h2]

theorem abs_projTaperDeriv2_le {g : ℝ → ℝ} {Λ : ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (r u : ℝ) :
    |projTaperDeriv2 g r u|
      ≤ bracketBound g Λ r * (|deriv (deriv g) u| + 2 * |deriv g u| + |g u|) := by
  by_cases hu : |u| ≤ Λ
  · have hB := abs_bracket_le_bound hg hgc hsupp hΛ r hu
    have hB' := abs_bracketDeriv_le_bound hg hgc hΛ r hu
    have hB'' := abs_bracketDeriv2_le_bound hg hgc hΛ r u
    have hβ := bracketBound_nonneg g Λ r hΛ
    have e1 : |deriv (deriv g) u * twoRadiusBracket g r u|
        ≤ bracketBound g Λ r * |deriv (deriv g) u| := by
      rw [abs_mul]
      calc |deriv (deriv g) u| * |twoRadiusBracket g r u|
          ≤ |deriv (deriv g) u| * bracketBound g Λ r :=
            mul_le_mul_of_nonneg_left hB (abs_nonneg _)
        _ = bracketBound g Λ r * |deriv (deriv g) u| := by ring
    have e2 : |2 * (deriv g u * bracketDeriv g r u)|
        ≤ bracketBound g Λ r * (2 * |deriv g u|) := by
      rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
      calc 2 * (|deriv g u| * |bracketDeriv g r u|) ≤ 2 * (|deriv g u| * bracketBound g Λ r) := by
            have := mul_le_mul_of_nonneg_left hB' (abs_nonneg (deriv g u))
            linarith
        _ = bracketBound g Λ r * (2 * |deriv g u|) := by ring
    have e3 : |g u * bracketDeriv2 g r u| ≤ bracketBound g Λ r * |g u| := by
      rw [abs_mul]
      calc |g u| * |bracketDeriv2 g r u| ≤ |g u| * bracketBound g Λ r :=
            mul_le_mul_of_nonneg_left hB'' (abs_nonneg _)
        _ = bracketBound g Λ r * |g u| := by ring
    have hadd1 := abs_add_le (deriv (deriv g) u * twoRadiusBracket g r u
      + 2 * (deriv g u * bracketDeriv g r u)) (g u * bracketDeriv2 g r u)
    have hadd2 := abs_add_le (deriv (deriv g) u * twoRadiusBracket g r u)
      (2 * (deriv g u * bracketDeriv g r u))
    unfold projTaperDeriv2
    nlinarith [hadd1, hadd2, e1, e2, e3]
  · have h1 : g u = 0 := by by_contra h; exact hu (hsupp u h)
    have h2 : deriv g u = 0 := by by_contra h; exact hu (support_radius_deriv hsupp u h)
    have h3 : deriv (deriv g) u = 0 := by
      by_contra h; exact hu (support_radius_deriv (support_radius_deriv hsupp) u h)
    simp [projTaperDeriv2, h1, h2, h3]

/-! ### The `L¹` mass bounds -/

theorem taperMass_le_of_pointwise {f w : ℝ → ℝ} {C : ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hw : Continuous w) (hwc : HasCompactSupport w)
    (hpt : ∀ u, |f u| ≤ C * |w u|) : taperMass f ≤ C * taperMass w := by
  have hi : Integrable (fun u : ℝ => |f u|) := hf.abs.integrable_of_hasCompactSupport hfc.abs
  have hj : Integrable (fun u : ℝ => C * |w u|) :=
    (hw.abs.integrable_of_hasCompactSupport hwc.abs).const_mul _
  unfold taperMass
  calc (∫ u : ℝ, |f u|) ≤ ∫ u : ℝ, C * |w u| := integral_mono hi hj hpt
    _ = C * ∫ u : ℝ, |w u| := integral_const_mul _ _


/-! ## The `L¹` data of a twisted taper -/

theorem twist_continuous (c : ℝ) : Continuous (twist c) := by
  unfold twist; fun_prop

theorem integral_norm_twistMul (h : ℝ → ℝ) (c : ℝ) :
    (∫ u : ℝ, ‖((h u : ℝ) : ℂ) * twist c u‖) = taperMass h := by
  unfold taperMass
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => norm_twistMul h c u)

theorem twistDeriv2_continuous {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) (c : ℝ) :
    Continuous (twistDeriv2 h c) := by
  have hc0 : Continuous h := hh.continuous
  have hc1 : Continuous (deriv h) := (contDiff_one_deriv hh).continuous
  have hc2 : Continuous (deriv (deriv h)) := continuous_deriv2 hh
  have hct : Continuous (twist c) := twist_continuous c
  unfold twistDeriv2
  fun_prop

theorem twistDeriv2_support {h : ℝ → ℝ} {Λ : ℝ} (hsupp : ∀ u, h u ≠ 0 → |u| ≤ Λ) (c : ℝ) :
    ∀ u, twistDeriv2 h c u ≠ 0 → |u| ≤ Λ := by
  intro u hne
  by_contra hu
  refine hne ?_
  have h1 : h u = 0 := by by_contra hx; exact hu (hsupp u hx)
  have h2 : deriv h u = 0 := by by_contra hx; exact hu (support_radius_deriv hsupp u hx)
  have h3 : deriv (deriv h) u = 0 := by
    by_contra hx; exact hu (support_radius_deriv (support_radius_deriv hsupp) u hx)
  simp [twistDeriv2, h1, h2, h3]

/-- **The `L¹` norm of the second derivative of a twisted taper.** -/
theorem integral_norm_twistDeriv2_le {h : ℝ → ℝ} {Λ : ℝ} (hh : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ Λ) (c : ℝ) :
    (∫ u : ℝ, ‖twistDeriv2 h c u‖)
      ≤ taperMass (deriv (deriv h)) + 2 * |c| * taperMass (deriv h) + c ^ 2 * taperMass h := by
  have hc0 : Continuous h := hh.continuous
  have hc1 : Continuous (deriv h) := (contDiff_one_deriv hh).continuous
  have hc2 : Continuous (deriv (deriv h)) := continuous_deriv2 hh
  have hk0 : HasCompactSupport h := hasCompactSupport_of_radius hsupp
  have hk1 : HasCompactSupport (deriv h) := hasCompactSupport_of_radius (support_radius_deriv hsupp)
  have hk2 : HasCompactSupport (deriv (deriv h)) :=
    hasCompactSupport_of_radius (support_radius_deriv (support_radius_deriv hsupp))
  have hL : Integrable (fun u : ℝ => ‖twistDeriv2 h c u‖) :=
    (twistDeriv2_continuous hh c).norm.integrable_of_hasCompactSupport
      (hasCompactSupport_of_radius (twistDeriv2_support hsupp c)).norm
  have hi0 : Integrable (fun u : ℝ => c ^ 2 * |h u|) :=
    (hc0.abs.integrable_of_hasCompactSupport hk0.abs).const_mul _
  have hi1 : Integrable (fun u : ℝ => 2 * |c| * |deriv h u|) :=
    (hc1.abs.integrable_of_hasCompactSupport hk1.abs).const_mul _
  have hi2 : Integrable (fun u : ℝ => |deriv (deriv h) u|) :=
    hc2.abs.integrable_of_hasCompactSupport hk2.abs
  have hi12 : Integrable (fun u : ℝ => |deriv (deriv h) u| + 2 * |c| * |deriv h u|) :=
    hi2.add hi1
  have hb : Integrable (fun u : ℝ =>
      |deriv (deriv h) u| + 2 * |c| * |deriv h u| + c ^ 2 * |h u|) := hi12.add hi0
  have hval : (∫ u : ℝ, (|deriv (deriv h) u| + 2 * |c| * |deriv h u| + c ^ 2 * |h u|))
      = taperMass (deriv (deriv h)) + 2 * |c| * taperMass (deriv h) + c ^ 2 * taperMass h := by
    rw [integral_add hi12 hi0, integral_add hi2 hi1, integral_const_mul, integral_const_mul]
    rfl
  calc (∫ u : ℝ, ‖twistDeriv2 h c u‖)
      ≤ ∫ u : ℝ, (|deriv (deriv h) u| + 2 * |c| * |deriv h u| + c ^ 2 * |h u|) :=
        integral_mono hL hb (fun u => norm_twistDeriv2_le h c u)
    _ = taperMass (deriv (deriv h)) + 2 * |c| * taperMass (deriv h) + c ^ 2 * taperMass h := hval

/-- **The strip constant of a twisted taper.** -/
theorem stripConst_sampleTest_le {h : ℝ → ℝ} {Λ : ℝ} (hh : ContDiff ℝ 2 h)
    (hsupp : ∀ u, h u ≠ 0 → |u| ≤ Λ) (t s : ℝ) :
    stripConst (sampleTest h t s) Λ
      ≤ Real.exp (Λ / 2) * (taperMass h + (taperMass (deriv (deriv h))
          + 2 * |s - t| * taperMass (deriv h) + (s - t) ^ 2 * taperMass h)) := by
  have h1 : (∫ u : ℝ, ‖sampleTest h t s u‖) = taperMass h := by
    rw [sampleTest_eq_twist]
    exact integral_norm_twistMul h (s - t)
  have h2 : (∫ u : ℝ, ‖deriv (deriv (sampleTest h t s)) u‖)
      ≤ taperMass (deriv (deriv h)) + 2 * |s - t| * taperMass (deriv h)
        + (s - t) ^ 2 * taperMass h := by
    rw [sampleTest_eq_twist, deriv2_twistMul hh (s - t)]
    exact integral_norm_twistDeriv2_le hh hsupp (s - t)
  unfold stripConst
  rw [h1]
  have hexp : (0 : ℝ) < Real.exp (Λ / 2) := Real.exp_pos _
  nlinarith [h2, hexp]


/-! ## The mass bounds for the projective taper -/

theorem taperMass_le_of_bound {f b : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hb : Integrable b) (hpt : ∀ u, |f u| ≤ b u) : taperMass f ≤ ∫ u : ℝ, b u := by
  have hi : Integrable (fun u : ℝ => |f u|) := hf.abs.integrable_of_hasCompactSupport hfc.abs
  exact integral_mono hi hb hpt

theorem taperMass_projTaper_le {g : ℝ → ℝ} {Λ : ℝ} (hgs : ContDiff ℝ 2 g)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (r : ℝ) :
    taperMass (projTaper g r) ≤ bracketBound g Λ r * taperMass g := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_radius hsupp
  exact taperMass_le_of_pointwise (projTaper_continuous hgs.continuous r)
    (projTaper_hasCompactSupport hgc r) hgs.continuous hgc
    (abs_projTaper_le hgs.continuous hgc hsupp hΛ r)

theorem taperMass_deriv_projTaper_le {g : ℝ → ℝ} {Λ : ℝ} (hgs : ContDiff ℝ 2 g)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (r : ℝ) :
    taperMass (deriv (projTaper g r))
      ≤ bracketBound g Λ r * (taperMass (deriv g) + taperMass g) := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_radius hsupp
  have hpd : ContDiff ℝ 2 (projTaper g r) := projTaper_contDiff hgs r
  have hpk : HasCompactSupport (projTaper g r) := projTaper_hasCompactSupport hgc r
  have hi0 : Integrable (fun u : ℝ => |g u|) :=
    hgs.continuous.abs.integrable_of_hasCompactSupport hgc.abs
  have hi1 : Integrable (fun u : ℝ => |deriv g u|) :=
    (contDiff_one_deriv hgs).continuous.abs.integrable_of_hasCompactSupport
      (hasCompactSupport_of_radius (support_radius_deriv hsupp) : HasCompactSupport (deriv g)).abs
  have hsum : Integrable (fun u : ℝ => |deriv g u| + |g u|) := hi1.add hi0
  have hb : Integrable (fun u : ℝ => bracketBound g Λ r * (|deriv g u| + |g u|)) :=
    hsum.const_mul _
  have hpt : ∀ u, |deriv (projTaper g r) u| ≤ bracketBound g Λ r * (|deriv g u| + |g u|) := by
    intro u
    rw [deriv_projTaper hgs r]
    exact abs_projTaperDeriv_le hgs.continuous hgc hsupp hΛ r u
  have hval : (∫ u : ℝ, bracketBound g Λ r * (|deriv g u| + |g u|))
      = bracketBound g Λ r * (taperMass (deriv g) + taperMass g) := by
    rw [integral_const_mul, integral_add hi1 hi0]
    rfl
  calc taperMass (deriv (projTaper g r))
      ≤ ∫ u : ℝ, bracketBound g Λ r * (|deriv g u| + |g u|) :=
        taperMass_le_of_bound (contDiff_one_deriv hpd).continuous hpk.deriv hb hpt
    _ = bracketBound g Λ r * (taperMass (deriv g) + taperMass g) := hval

theorem taperMass_deriv2_projTaper_le {g : ℝ → ℝ} {Λ : ℝ} (hgs : ContDiff ℝ 2 g)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (r : ℝ) :
    taperMass (deriv (deriv (projTaper g r)))
      ≤ bracketBound g Λ r
          * (taperMass (deriv (deriv g)) + 2 * taperMass (deriv g) + taperMass g) := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_radius hsupp
  have hpd : ContDiff ℝ 2 (projTaper g r) := projTaper_contDiff hgs r
  have hpk : HasCompactSupport (projTaper g r) := projTaper_hasCompactSupport hgc r
  have hi0 : Integrable (fun u : ℝ => |g u|) :=
    hgs.continuous.abs.integrable_of_hasCompactSupport hgc.abs
  have hi1 : Integrable (fun u : ℝ => 2 * |deriv g u|) :=
    ((contDiff_one_deriv hgs).continuous.abs.integrable_of_hasCompactSupport
      (hasCompactSupport_of_radius (support_radius_deriv hsupp) :
        HasCompactSupport (deriv g)).abs).const_mul _
  have hi1' : Integrable (fun u : ℝ => |deriv g u|) :=
    (contDiff_one_deriv hgs).continuous.abs.integrable_of_hasCompactSupport
      (hasCompactSupport_of_radius (support_radius_deriv hsupp) : HasCompactSupport (deriv g)).abs
  have hi2 : Integrable (fun u : ℝ => |deriv (deriv g) u|) :=
    (continuous_deriv2 hgs).abs.integrable_of_hasCompactSupport
      (hasCompactSupport_of_radius (support_radius_deriv (support_radius_deriv hsupp)) :
        HasCompactSupport (deriv (deriv g))).abs
  have hi21 : Integrable (fun u : ℝ => |deriv (deriv g) u| + 2 * |deriv g u|) := hi2.add hi1
  have hsum : Integrable (fun u : ℝ => |deriv (deriv g) u| + 2 * |deriv g u| + |g u|) :=
    hi21.add hi0
  have hb : Integrable
      (fun u : ℝ => bracketBound g Λ r * (|deriv (deriv g) u| + 2 * |deriv g u| + |g u|)) :=
    hsum.const_mul _
  have hpt : ∀ u, |deriv (deriv (projTaper g r)) u|
      ≤ bracketBound g Λ r * (|deriv (deriv g) u| + 2 * |deriv g u| + |g u|) := by
    intro u
    rw [deriv2_projTaper hgs r]
    exact abs_projTaperDeriv2_le hgs.continuous hgc hsupp hΛ r u
  have hval : (∫ u : ℝ, bracketBound g Λ r * (|deriv (deriv g) u| + 2 * |deriv g u| + |g u|))
      = bracketBound g Λ r
          * (taperMass (deriv (deriv g)) + 2 * taperMass (deriv g) + taperMass g) := by
    rw [integral_const_mul, integral_add hi21 hi0, integral_add hi2 hi1, integral_const_mul]
    rfl
  calc taperMass (deriv (deriv (projTaper g r)))
      ≤ ∫ u : ℝ, bracketBound g Λ r * (|deriv (deriv g) u| + 2 * |deriv g u| + |g u|) :=
        taperMass_le_of_bound (continuous_deriv2 hpd) hpk.deriv.deriv hb hpt
    _ = bracketBound g Λ r
          * (taperMass (deriv (deriv g)) + 2 * taperMass (deriv g) + taperMass g) := hval

/-! ## The quadratic strip constant -/

/-- **The projective strip coefficient**: the `r`-independent factor in the quadratic
bound for the strip constant of the projective taper. -/
def projStripCoeff (g : ℝ → ℝ) (Λ t : ℝ) : ℝ :=
  Real.exp (Λ / 2) * (5 * (1 + Λ) ^ 2 * taperMass g)
    * ((2 + 2 * |t| + t ^ 2) * taperMass g + (2 + 2 * |t|) * taperMass (deriv g)
        + taperMass (deriv (deriv g)))

/-- **`stripConst_projTaper_le`.**  The strip constant of the projective taper is
quadratically small in the sampling radius. -/
theorem stripConst_projTaper_le {g : ℝ → ℝ} {Λ : ℝ} (hgs : ContDiff ℝ 2 g)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (t r : ℝ) :
    stripConst (sampleTest (projTaper g r) t 0) Λ ≤ r ^ 2 * projStripCoeff g Λ t := by
  set h := projTaper g r with hh
  have hpd : ContDiff ℝ 2 h := projTaper_contDiff hgs r
  have hps : ∀ u, h u ≠ 0 → |u| ≤ Λ := projTaper_support hsupp r
  have hbase := stripConst_sampleTest_le hpd hps t 0
  have habs : |(0 : ℝ) - t| = |t| := by rw [zero_sub, abs_neg]
  have hsq : ((0 : ℝ) - t) ^ 2 = t ^ 2 := by ring
  rw [habs, hsq] at hbase
  have hb := bracketBound_nonneg g Λ r hΛ
  have h1 := taperMass_projTaper_le hgs hsupp hΛ r
  have h2 := taperMass_deriv_projTaper_le hgs hsupp hΛ r
  have h3 := taperMass_deriv2_projTaper_le hgs hsupp hΛ r
  have h2' : 2 * |t| * taperMass (deriv h)
      ≤ 2 * |t| * (bracketBound g Λ r * (taperMass (deriv g) + taperMass g)) := by
    have : (0 : ℝ) ≤ 2 * |t| := by positivity
    exact mul_le_mul_of_nonneg_left h2 this
  have h3' : t ^ 2 * taperMass h ≤ t ^ 2 * (bracketBound g Λ r * taperMass g) :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg t)
  have hE : (0 : ℝ) < Real.exp (Λ / 2) := Real.exp_pos _
  have hinner : taperMass h + (taperMass (deriv (deriv h)) + 2 * |t| * taperMass (deriv h)
        + t ^ 2 * taperMass h)
      ≤ bracketBound g Λ r * taperMass g
        + (bracketBound g Λ r
            * (taperMass (deriv (deriv g)) + 2 * taperMass (deriv g) + taperMass g)
          + 2 * |t| * (bracketBound g Λ r * (taperMass (deriv g) + taperMass g))
          + t ^ 2 * (bracketBound g Λ r * taperMass g)) := by linarith
  have hstep : Real.exp (Λ / 2) * (taperMass h + (taperMass (deriv (deriv h))
        + 2 * |t| * taperMass (deriv h) + t ^ 2 * taperMass h))
      ≤ Real.exp (Λ / 2) * (bracketBound g Λ r * taperMass g
        + (bracketBound g Λ r
            * (taperMass (deriv (deriv g)) + 2 * taperMass (deriv g) + taperMass g)
          + 2 * |t| * (bracketBound g Λ r * (taperMass (deriv g) + taperMass g))
          + t ^ 2 * (bracketBound g Λ r * taperMass g))) :=
    mul_le_mul_of_nonneg_left hinner (le_of_lt hE)
  have hfin : Real.exp (Λ / 2) * (bracketBound g Λ r * taperMass g
        + (bracketBound g Λ r
            * (taperMass (deriv (deriv g)) + 2 * taperMass (deriv g) + taperMass g)
          + 2 * |t| * (bracketBound g Λ r * (taperMass (deriv g) + taperMass g))
          + t ^ 2 * (bracketBound g Λ r * taperMass g)))
      = r ^ 2 * projStripCoeff g Λ t := by
    unfold projStripCoeff bracketBound
    ring
  linarith [hbase, hstep, hfin.le, hfin.ge]


/-! ## The quadratic off-ordinate projective envelope -/

/-- **`offOrdProjectiveTailQuadratic`.**  Combining the determinant-level transport of
`LiteralWeilOffOrdinateProjectiveTail` with the quadratic strip constant, the whole
off-ordinate zero tail contributes only `O(r²)` to the two-radius determinant.  This
is the gain that the radiuswise absolute envelope `|Z(2r)||A₀(r)| + |Z(r)||A₀(2r)|`
— which is `O(1)` — throws away. -/
theorem offOrdProjectiveTailQuadratic {g : ℝ → ℝ} {Λ : ℝ} (hgs : ContDiff ℝ 2 g)
    (heven : ∀ u, g (-u) = g u) (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (t r : ℝ) :
    |Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect g t r|
      ≤ r ^ 2 * (4 * projStripCoeff g Λ t * offOrdWeight t) := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_radius hsupp
  have henv := Zeta23Bridge.LiteralWeilOffOrdinateProjectiveTail.offOrdProjectiveTailEnvelope
    hgs hgc heven hsupp hΛ t r
  have hstrip := stripConst_projTaper_le hgs hsupp hΛ t r
  have hw := offOrdWeight_nonneg t
  nlinarith [henv, hstrip, hw, stripConst_nonneg (sampleTest (projTaper g r) t 0) Λ]

end LiteralWeilProjectiveStripConstant
end Zeta23Bridge
