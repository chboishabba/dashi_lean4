/-
# Parity is blind to height, but the two-radius even profile is not

`LiteralWeilEvenChannelTaper.reflectionPair_parity_blindness` proved that a
reflection pair contributes a *purely even* four-sample pattern at every height,
on-line heights included.  That theorem must be read carefully.  It says

    parity alone cannot distinguish an off-line pair from an on-line pair,

and **not**

    the four sampled values contain no off-line height information.

The height is still there — in the *radial shape*.  For the even response

    A_a(s) = ∫ g(u) cosh(au) cos(su) du

the natural two-radius invariant is the projective defect

    D(a, b) = A_a(r) A_b(2r) - A_a(2r) A_b(r),

the determinant of the two profiles `(A_a(r), A_a(2r))` and `(A_b(r), A_b(2r))`.
This module proves the negative/positive pair:

* `pairParityCannotDetectHeight` — for every height the pair vector lies in the
  even subspace `{v 0 = v 1, v 2 = v 3}`, the very same subspace as at height `0`;
  every linear functional that annihilates even patterns annihilates every pair.

* `twoRadiusEvenProfileDetectsHeight` — for a nonnegative taper whose support is
  radially admissible for the doubled radius, and which is positive at two points
  of different modulus,

      a ≠ 0  ⟹  D(a, 0) > 0.

  So the two-radius profile of an off-line pair is *never* proportional to the
  on-line profile: `twoRadiusProfile_not_proportional`.

The mechanism is an exact factorisation of the radial kernel,

    cos(ru)cos(2rv) - cos(2ru)cos(rv) = (cos(rv) - cos(ru)) (2 cos(ru) cos(rv) + 1),

whose sign — on the radially admissible range — is exactly the sign of `|u| - |v|`,
matched against the sign of `cosh(au) - cosh(av)`, which is the same sign for every
`a ≠ 0` and identically zero for `a = 0`.  Antisymmetrising the double integral
turns `D(a,0)` into the integral of a pointwise nonnegative function which is
strictly positive on a nonempty open set.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

noncomputable section

open MeasureTheory Set
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilTwoRadiusHeightDetector

open Zeta23Bridge.LiteralWeilParityBalance Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilEvenChannelTaper

/-! ## The negative half: parity is blind to height -/

/-- The even subspace of the four-sample space: equal values at `±r` and at `±2r`. -/
def evenSubspace : Submodule ℝ (Fin 4 → ℝ) where
  carrier := {v | v 0 = v 1 ∧ v 2 = v 3}
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by simp only [Pi.add_apply, h1, h3], by simp only [Pi.add_apply, h2, h4]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := by
    rintro c v ⟨h1, h2⟩
    exact ⟨by simp only [Pi.smul_apply, h1], by simp only [Pi.smul_apply, h2]⟩

theorem evenPattern_mem_evenSubspace (x y : ℝ) : evenPattern x y ∈ evenSubspace :=
  ⟨rfl, rfl⟩

/-- **`pairParityCannotDetectHeight`.**  For *every* height `a` — on-line included
— the reflection-pair four-sample vector is an even pattern, hence lies in the
same two-dimensional even subspace.  No parity coordinate can separate heights. -/
theorem pairParityCannotDetectHeight (g : ℝ → ℝ) (r m a : ℝ) :
    m • targetParityVec g a r + m • targetParityVec g (-a) r ∈ evenSubspace
      ∧ m • targetParityVec g a r + m • targetParityVec g (-a) r
        = evenPattern (m * (2 * evenResp g a r)) (m * (2 * evenResp g a (2 * r))) := by
  have h := reflectionPair_parity_blindness g a r m
  exact ⟨h ▸ evenPattern_mem_evenSubspace _ _, h⟩

/-- Any linear functional that annihilates the even patterns annihilates the
reflection pair at *every* height: parity functionals carry no height
information. -/
theorem parityFunctional_blind_to_height (L : (Fin 4 → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ x y : ℝ, L (evenPattern x y) = 0) (g : ℝ → ℝ) (r m a : ℝ) :
    L (m • targetParityVec g a r + m • targetParityVec g (-a) r) = 0 := by
  rw [(pairParityCannotDetectHeight g r m a).2]
  exact hL _ _

/-! ## The positive half: the two-radius even profile -/

/-- The two-radius even profile of a height: the pair `(A_a(r), A_a(2r))`. -/
def evenProfile (g : ℝ → ℝ) (r a : ℝ) : ℝ × ℝ := (evenResp g a r, evenResp g a (2 * r))

/-- The **height defect**: the determinant of the two-radius profiles of two
heights.  It vanishes exactly when the two profiles are projectively equal. -/
def heightDefect (g : ℝ → ℝ) (r a b : ℝ) : ℝ :=
  evenResp g a r * evenResp g b (2 * r) - evenResp g a (2 * r) * evenResp g b r

theorem heightDefect_self (g : ℝ → ℝ) (r a : ℝ) : heightDefect g r a a = 0 := by
  unfold heightDefect; ring

theorem heightDefect_swap (g : ℝ → ℝ) (r a b : ℝ) :
    heightDefect g r b a = -heightDefect g r a b := by
  unfold heightDefect; ring

/-! ### The radial kernel and its sign -/

theorem cos_mul_abs {r u : ℝ} (hr : 0 < r) : Real.cos (r * u) = Real.cos (r * |u|) := by
  rw [← Real.cos_abs (r * u), abs_mul, abs_of_pos hr]

/-- The exact factorisation of the two-radius radial kernel. -/
theorem radialKernel_factor (r u v : ℝ) :
    Real.cos (r * u) * Real.cos (2 * r * v) - Real.cos (2 * r * u) * Real.cos (r * v)
      = (Real.cos (r * v) - Real.cos (r * u)) * (2 * Real.cos (r * u) * Real.cos (r * v) + 1) := by
  rw [show 2 * r * v = 2 * (r * v) by ring, show 2 * r * u = 2 * (r * u) by ring,
    Real.cos_two_mul, Real.cos_two_mul]
  ring

theorem cos_pos_of_radial {r u : ℝ} (hr : 0 < r) (hu : 2 * r * |u| < π / 2) :
    0 < Real.cos (r * u) := by
  have hpi := Real.pi_pos
  have habs : |r * u| = r * |u| := by rw [abs_mul, abs_of_pos hr]
  have hlt : |r * u| < π / 2 := by rw [habs]; nlinarith [abs_nonneg u]
  have h := abs_lt.mp hlt
  exact Real.cos_pos_of_mem_Ioo ⟨h.1, h.2⟩

/-! ### The two-height `cosh` comparison (strict TP₂ in the height) -/

/-- The product-to-sum identity for `cosh`. -/
theorem cosh_mul_cosh (x y : ℝ) :
    2 * (Real.cosh x * Real.cosh y) = Real.cosh (x + y) + Real.cosh (x - y) := by
  rw [Real.cosh_add, Real.cosh_sub]; ring

theorem cosh_abs_mul (a u : ℝ) : Real.cosh (a * u) = Real.cosh (|a| * |u|) := by
  rw [← abs_mul, Real.cosh_abs]

/-- **Strict total positivity of `cosh` in the two-height variables.**  For
`|b| < |a|` and `|u| < |v|` the `2 × 2` minor of `cosh` is strictly negative:

    cosh(au) cosh(bv) < cosh(av) cosh(bu). -/
theorem cosh_two_height_lt {a b u v : ℝ} (hab : |b| < |a|) (huv : |u| < |v|) :
    Real.cosh (a * u) * Real.cosh (b * v) < Real.cosh (a * v) * Real.cosh (b * u) := by
  set A := |a|; set B := |b|; set U := |u|; set V := |v|
  have hB : 0 ≤ B := abs_nonneg b
  have hU : 0 ≤ U := abs_nonneg u
  have hA : 0 < A := lt_of_le_of_lt hB hab
  have hV : 0 < V := lt_of_le_of_lt hU huv
  have h1 : Real.cosh (A * U + B * V) < Real.cosh (A * V + B * U) := by
    rw [Real.cosh_lt_cosh, abs_of_nonneg (by positivity : (0:ℝ) ≤ A * U + B * V),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ A * V + B * U)]
    nlinarith
  have h2 : Real.cosh (A * U - B * V) ≤ Real.cosh (A * V - B * U) := by
    rw [Real.cosh_le_cosh]
    refine abs_le_abs ?_ ?_
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ A + B) (by linarith : (0:ℝ) ≤ V - U)]
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ A - B) (by linarith : (0:ℝ) ≤ U + V)]
  have e1 := cosh_mul_cosh (A * U) (B * V)
  have e2 := cosh_mul_cosh (A * V) (B * U)
  rw [cosh_abs_mul a u, cosh_abs_mul b v, cosh_abs_mul a v, cosh_abs_mul b u]
  linarith

/-- The non-strict companion of `cosh_two_height_lt`. -/
theorem cosh_two_height_le {a b u v : ℝ} (hab : |b| ≤ |a|) (huv : |u| ≤ |v|) :
    Real.cosh (a * u) * Real.cosh (b * v) ≤ Real.cosh (a * v) * Real.cosh (b * u) := by
  set A := |a|; set B := |b|; set U := |u|; set V := |v|
  have hB : 0 ≤ B := abs_nonneg b
  have hU : 0 ≤ U := abs_nonneg u
  have hA : 0 ≤ A := le_trans hB hab
  have hV : 0 ≤ V := le_trans hU huv
  have h1 : Real.cosh (A * U + B * V) ≤ Real.cosh (A * V + B * U) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity : (0:ℝ) ≤ A * U + B * V),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ A * V + B * U)]
    nlinarith
  have h2 : Real.cosh (A * U - B * V) ≤ Real.cosh (A * V - B * U) := by
    rw [Real.cosh_le_cosh]
    refine abs_le_abs ?_ ?_
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ A + B) (by linarith : (0:ℝ) ≤ V - U)]
    · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ A - B) (by linarith : (0:ℝ) ≤ U + V)]
  have e1 := cosh_mul_cosh (A * U) (B * V)
  have e2 := cosh_mul_cosh (A * V) (B * U)
  rw [cosh_abs_mul a u, cosh_abs_mul b v, cosh_abs_mul a v, cosh_abs_mul b u]
  linarith

/-! ### The two-height kernel -/

/-- **The sign of the two-height kernel.**  For `|b| ≤ |a|` the product of the
two-height `cosh` minor and the radial kernel is nonnegative on the radially
admissible range. -/
theorem heightKernel2_nonneg {r a b u v : ℝ} (hr : 0 < r) (hab : |b| ≤ |a|)
    (hu : 2 * r * |u| < π / 2) (hv : 2 * r * |v| < π / 2) :
    0 ≤ (Real.cosh (a * u) * Real.cosh (b * v) - Real.cosh (a * v) * Real.cosh (b * u))
      * (Real.cos (r * u) * Real.cos (2 * r * v) - Real.cos (2 * r * u) * Real.cos (r * v)) := by
  have hpi := Real.pi_pos
  have hcu : 0 < Real.cos (r * u) := cos_pos_of_radial hr hu
  have hcv : 0 < Real.cos (r * v) := cos_pos_of_radial hr hv
  have hfac : 0 < 2 * Real.cos (r * u) * Real.cos (r * v) + 1 := by positivity
  rw [radialKernel_factor]
  rcases lt_trichotomy |u| |v| with h | h | h
  · have hcos : Real.cos (r * v) < Real.cos (r * u) := by
      rw [cos_mul_abs hr (u := u), cos_mul_abs hr (u := v)]
      refine Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) ?_
        (mul_lt_mul_of_pos_left h hr)
      have h2 : 2 * (r * |v|) = 2 * r * |v| := by ring
      linarith
    have hch := cosh_two_height_le hab h.le
    have hsecond : (Real.cos (r * v) - Real.cos (r * u))
        * (2 * Real.cos (r * u) * Real.cos (r * v) + 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hfac.le
    nlinarith [mul_nonneg (by linarith :
      (0:ℝ) ≤ -(Real.cosh (a * u) * Real.cosh (b * v)
        - Real.cosh (a * v) * Real.cosh (b * u)))
      (by linarith : (0:ℝ) ≤ -((Real.cos (r * v) - Real.cos (r * u))
        * (2 * Real.cos (r * u) * Real.cos (r * v) + 1)))]
  · have hcos : Real.cos (r * v) = Real.cos (r * u) := by
      rw [cos_mul_abs hr (u := u), cos_mul_abs hr (u := v), h]
    rw [hcos]; simp
  · have hcos : Real.cos (r * u) < Real.cos (r * v) := by
      rw [cos_mul_abs hr (u := u), cos_mul_abs hr (u := v)]
      refine Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) ?_
        (mul_lt_mul_of_pos_left h hr)
      have h2 : 2 * (r * |u|) = 2 * r * |u| := by ring
      linarith
    have hch := cosh_two_height_le hab h.le
    have hsecond : (0:ℝ) ≤ (Real.cos (r * v) - Real.cos (r * u))
        * (2 * Real.cos (r * u) * Real.cos (r * v) + 1) :=
      mul_nonneg (by linarith) hfac.le
    nlinarith [mul_nonneg (by linarith :
      (0:ℝ) ≤ Real.cosh (a * u) * Real.cosh (b * v)
        - Real.cosh (a * v) * Real.cosh (b * u)) hsecond]

/-- **The strict sign of the two-height kernel** for `|b| < |a|` at unequal
moduli. -/
theorem heightKernel2_pos {r a b u v : ℝ} (hr : 0 < r) (hab : |b| < |a|)
    (hu : 2 * r * |u| < π / 2) (hv : 2 * r * |v| < π / 2) (hne : |u| ≠ |v|) :
    0 < (Real.cosh (a * u) * Real.cosh (b * v) - Real.cosh (a * v) * Real.cosh (b * u))
      * (Real.cos (r * u) * Real.cos (2 * r * v) - Real.cos (2 * r * u) * Real.cos (r * v)) := by
  have hpi := Real.pi_pos
  have hcu : 0 < Real.cos (r * u) := cos_pos_of_radial hr hu
  have hcv : 0 < Real.cos (r * v) := cos_pos_of_radial hr hv
  have hfac : 0 < 2 * Real.cos (r * u) * Real.cos (r * v) + 1 := by positivity
  rw [radialKernel_factor]
  rcases lt_or_gt_of_ne hne with h | h
  · have hcos : Real.cos (r * v) < Real.cos (r * u) := by
      rw [cos_mul_abs hr (u := u), cos_mul_abs hr (u := v)]
      refine Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) ?_
        (mul_lt_mul_of_pos_left h hr)
      have h2 : 2 * (r * |v|) = 2 * r * |v| := by ring
      linarith
    have hch := cosh_two_height_lt hab h
    have h1 : Real.cosh (a * u) * Real.cosh (b * v)
        - Real.cosh (a * v) * Real.cosh (b * u) < 0 := by linarith
    have h3 : (Real.cos (r * v) - Real.cos (r * u))
        * (2 * Real.cos (r * u) * Real.cos (r * v) + 1) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hfac
    exact mul_pos_of_neg_of_neg h1 h3
  · have hcos : Real.cos (r * u) < Real.cos (r * v) := by
      rw [cos_mul_abs hr (u := u), cos_mul_abs hr (u := v)]
      refine Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) ?_
        (mul_lt_mul_of_pos_left h hr)
      have h2 : 2 * (r * |u|) = 2 * r * |u| := by ring
      linarith
    have hch := cosh_two_height_lt hab h
    have h1 : 0 < Real.cosh (a * u) * Real.cosh (b * v)
        - Real.cosh (a * v) * Real.cosh (b * u) := by linarith
    exact mul_pos h1 (mul_pos (by linarith) hfac)

/-- **The sign of the height kernel.**  On the radially admissible range the
product of the `cosh` difference and the radial kernel is nonnegative, for every
height. -/
theorem heightKernel_nonneg {r a u v : ℝ} (hr : 0 < r)
    (hu : 2 * r * |u| < π / 2) (hv : 2 * r * |v| < π / 2) :
    0 ≤ (Real.cosh (a * u) - Real.cosh (a * v))
      * (Real.cos (r * u) * Real.cos (2 * r * v) - Real.cos (2 * r * u) * Real.cos (r * v)) := by
  have hpi := Real.pi_pos
  have hcu : 0 < Real.cos (r * u) := cos_pos_of_radial hr hu
  have hcv : 0 < Real.cos (r * v) := cos_pos_of_radial hr hv
  have hfac : 0 < 2 * Real.cos (r * u) * Real.cos (r * v) + 1 := by positivity
  rw [radialKernel_factor]
  rcases lt_trichotomy |u| |v| with h | h | h
  · have hcos : Real.cos (r * v) < Real.cos (r * u) := by
      rw [cos_mul_abs hr (u := u), cos_mul_abs hr (u := v)]
      refine Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) ?_
        (mul_lt_mul_of_pos_left h hr)
      have h2 : 2 * (r * |v|) = 2 * r * |v| := by ring
      linarith
    have hcosh : Real.cosh (a * u) ≤ Real.cosh (a * v) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left h.le (abs_nonneg a)
    have h1 : Real.cosh (a * u) - Real.cosh (a * v) ≤ 0 := by linarith
    have h2 : Real.cos (r * v) - Real.cos (r * u) ≤ 0 := by linarith
    have := mul_nonneg (neg_nonneg.mpr h1) (neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg h2 hfac.le))
    nlinarith [mul_nonneg (neg_nonneg.mpr h1) (neg_nonneg.mpr h2), hfac.le]
  · have hcos : Real.cos (r * v) = Real.cos (r * u) := by
      rw [cos_mul_abs hr (u := u), cos_mul_abs hr (u := v), h]
    rw [hcos]
    simp
  · have hcos : Real.cos (r * u) < Real.cos (r * v) := by
      rw [cos_mul_abs hr (u := u), cos_mul_abs hr (u := v)]
      refine Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) ?_
        (mul_lt_mul_of_pos_left h hr)
      have h2 : 2 * (r * |u|) = 2 * r * |u| := by ring
      linarith
    have hcosh : Real.cosh (a * v) ≤ Real.cosh (a * u) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left h.le (abs_nonneg a)
    have h1 : 0 ≤ Real.cosh (a * u) - Real.cosh (a * v) := by linarith
    have h2 : 0 ≤ Real.cos (r * v) - Real.cos (r * u) := by linarith
    exact mul_nonneg h1 (mul_nonneg h2 hfac.le)

/-- **The strict sign of the height kernel** at a nonzero height and unequal
moduli. -/
theorem heightKernel_pos {r a u v : ℝ} (hr : 0 < r) (ha : a ≠ 0)
    (hu : 2 * r * |u| < π / 2) (hv : 2 * r * |v| < π / 2) (hne : |u| ≠ |v|) :
    0 < (Real.cosh (a * u) - Real.cosh (a * v))
      * (Real.cos (r * u) * Real.cos (2 * r * v) - Real.cos (2 * r * u) * Real.cos (r * v)) := by
  have hpi := Real.pi_pos
  have hcu : 0 < Real.cos (r * u) := cos_pos_of_radial hr hu
  have hcv : 0 < Real.cos (r * v) := cos_pos_of_radial hr hv
  have hfac : 0 < 2 * Real.cos (r * u) * Real.cos (r * v) + 1 := by positivity
  have haa : 0 < |a| := abs_pos.mpr ha
  rw [radialKernel_factor]
  rcases lt_or_gt_of_ne hne with h | h
  · have hcos : Real.cos (r * v) < Real.cos (r * u) := by
      rw [cos_mul_abs hr (u := u), cos_mul_abs hr (u := v)]
      refine Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) ?_
        (mul_lt_mul_of_pos_left h hr)
      have h2 : 2 * (r * |v|) = 2 * r * |v| := by ring
      linarith
    have hcosh : Real.cosh (a * u) < Real.cosh (a * v) := by
      rw [Real.cosh_lt_cosh, abs_mul, abs_mul]
      exact mul_lt_mul_of_pos_left h haa
    have h1 : Real.cosh (a * u) - Real.cosh (a * v) < 0 := by linarith
    have h2 : Real.cos (r * v) - Real.cos (r * u) < 0 := by linarith
    have h3 : (Real.cos (r * v) - Real.cos (r * u))
        * (2 * Real.cos (r * u) * Real.cos (r * v) + 1) < 0 :=
      mul_neg_of_neg_of_pos h2 hfac
    exact mul_pos_of_neg_of_neg h1 h3
  · have hcos : Real.cos (r * u) < Real.cos (r * v) := by
      rw [cos_mul_abs hr (u := u), cos_mul_abs hr (u := v)]
      refine Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) ?_
        (mul_lt_mul_of_pos_left h hr)
      have h2 : 2 * (r * |u|) = 2 * r * |u| := by ring
      linarith
    have hcosh : Real.cosh (a * v) < Real.cosh (a * u) := by
      rw [Real.cosh_lt_cosh, abs_mul, abs_mul]
      exact mul_lt_mul_of_pos_left h haa
    have h1 : 0 < Real.cosh (a * u) - Real.cosh (a * v) := by linarith
    have h2 : 0 < Real.cos (r * v) - Real.cos (r * u) := by linarith
    exact mul_pos h1 (mul_pos h2 hfac)

/-! ### The detector -/

/-- The antisymmetrised two-dimensional integrand: its integral over `ℝ × ℝ` is
twice the height defect `D(a, b)`. -/
def heightIntegrand (g : ℝ → ℝ) (r a b : ℝ) : ℝ × ℝ → ℝ := fun z =>
  g z.1 * g z.2 * ((Real.cosh (a * z.1) * Real.cosh (b * z.2)
      - Real.cosh (a * z.2) * Real.cosh (b * z.1))
    * (Real.cos (r * z.1) * Real.cos (2 * r * z.2)
      - Real.cos (2 * r * z.1) * Real.cos (r * z.2)))

theorem continuous_heightIntegrand {g : ℝ → ℝ} (hg : Continuous g) (r a b : ℝ) :
    Continuous (heightIntegrand g r a b) := by
  unfold heightIntegrand
  fun_prop

theorem hasCompactSupport_heightIntegrand {g : ℝ → ℝ} (hgc : HasCompactSupport g) (r a b : ℝ) :
    HasCompactSupport (heightIntegrand g r a b) := by
  have hK : IsCompact ((tsupport g) ×ˢ (tsupport g)) := hgc.prod hgc
  apply HasCompactSupport.intro hK
  intro z hz
  have h : g z.1 = 0 ∨ g z.2 = 0 := by
    by_contra hcon
    push_neg at hcon
    exact hz ⟨subset_tsupport g hcon.1, subset_tsupport g hcon.2⟩
  rcases h with h | h <;> simp [heightIntegrand, h]

theorem integrable_heightIntegrand {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (r a b : ℝ) : Integrable (heightIntegrand g r a b) :=
  (continuous_heightIntegrand hg r a b).integrable_of_hasCompactSupport
    (hasCompactSupport_heightIntegrand hgc r a b)

/-- **The integral representation of the height defect.**  Antisymmetrising the
product of the two one-dimensional integrals turns the `2 × 2` determinant of the
two-radius profiles into a single two-dimensional integral. -/
theorem heightDefect_two_mul {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (r a b : ℝ) :
    2 * heightDefect g r a b = ∫ z : ℝ × ℝ, heightIntegrand g r a b z := by
  classical
  set f1 : ℝ → ℝ := fun u => g u * (Real.cosh (a * u) * Real.cos (r * u)) with hf1
  set f2 : ℝ → ℝ := fun u => g u * (Real.cosh (b * u) * Real.cos (2 * r * u)) with hf2
  set f3 : ℝ → ℝ := fun u => g u * (Real.cosh (a * u) * Real.cos (2 * r * u)) with hf3
  set f4 : ℝ → ℝ := fun u => g u * (Real.cosh (b * u) * Real.cos (r * u)) with hf4
  have hc1 : Continuous f1 := by rw [hf1]; fun_prop
  have hc2 : Continuous f2 := by rw [hf2]; fun_prop
  have hc3 : Continuous f3 := by rw [hf3]; fun_prop
  have hc4 : Continuous f4 := by rw [hf4]; fun_prop
  set Ψ : ℝ × ℝ → ℝ := fun z => f1 z.1 * f2 z.2 - f3 z.1 * f4 z.2 with hΨ
  have hΨc : Continuous Ψ := by
    rw [hΨ]
    exact ((hc1.comp continuous_fst).mul (hc2.comp continuous_snd)).sub
      ((hc3.comp continuous_fst).mul (hc4.comp continuous_snd))
  have hK : IsCompact ((tsupport g) ×ˢ (tsupport g)) := hgc.prod hgc
  have hvanish : ∀ z : ℝ × ℝ, z ∉ (tsupport g) ×ˢ (tsupport g) → g z.1 = 0 ∨ g z.2 = 0 := by
    intro z hz
    by_contra hcon
    push_neg at hcon
    exact hz ⟨subset_tsupport g hcon.1, subset_tsupport g hcon.2⟩
  have hΨsupp : HasCompactSupport Ψ := by
    apply HasCompactSupport.intro hK
    intro z hz
    rcases hvanish z hz with h | h <;> simp [hΨ, hf1, hf2, hf3, hf4, h]
  have hΨswapc : Continuous (fun z : ℝ × ℝ => Ψ z.swap) := hΨc.comp continuous_swap
  have hΨswapsupp : HasCompactSupport (fun z : ℝ × ℝ => Ψ z.swap) := by
    apply HasCompactSupport.intro hK
    intro z hz
    rcases hvanish z hz with h | h <;> simp [hΨ, hf1, hf2, hf3, hf4, h]
  have hΨi : Integrable Ψ := hΨc.integrable_of_hasCompactSupport hΨsupp
  have hΨswapi : Integrable (fun z : ℝ × ℝ => Ψ z.swap) :=
    hΨswapc.integrable_of_hasCompactSupport hΨswapsupp
  have hprod1 : ∫ z : ℝ × ℝ, f1 z.1 * f2 z.2 = (∫ u, f1 u) * ∫ u, f2 u := by
    have := MeasureTheory.integral_prod_mul (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ)) f1 f2
    rwa [← MeasureTheory.Measure.volume_eq_prod] at this
  have hprod2 : ∫ z : ℝ × ℝ, f3 z.1 * f4 z.2 = (∫ u, f3 u) * ∫ u, f4 u := by
    have := MeasureTheory.integral_prod_mul (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ)) f3 f4
    rwa [← MeasureTheory.Measure.volume_eq_prod] at this
  have hi12 : Integrable (fun z : ℝ × ℝ => f1 z.1 * f2 z.2) := by
    apply Continuous.integrable_of_hasCompactSupport
      ((hc1.comp continuous_fst).mul (hc2.comp continuous_snd))
    apply HasCompactSupport.intro hK
    intro z hz
    rcases hvanish z hz with h | h <;> simp [hf1, hf2, h]
  have hi34 : Integrable (fun z : ℝ × ℝ => f3 z.1 * f4 z.2) := by
    apply Continuous.integrable_of_hasCompactSupport
      ((hc3.comp continuous_fst).mul (hc4.comp continuous_snd))
    apply HasCompactSupport.intro hK
    intro z hz
    rcases hvanish z hz with h | h <;> simp [hf3, hf4, h]
  have hD : heightDefect g r a b = ∫ z : ℝ × ℝ, Ψ z := by
    have hsub : ∫ z : ℝ × ℝ, Ψ z
        = (∫ z : ℝ × ℝ, f1 z.1 * f2 z.2) - ∫ z : ℝ × ℝ, f3 z.1 * f4 z.2 := by
      rw [hΨ]
      exact integral_sub hi12 hi34
    rw [hsub, hprod1, hprod2]
    rfl
  have hswap : ∫ z : ℝ × ℝ, Ψ z.swap = ∫ z : ℝ × ℝ, Ψ z := by
    have := MeasureTheory.integral_prod_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ)) Ψ
    rwa [← MeasureTheory.Measure.volume_eq_prod] at this
  have hdouble : 2 * heightDefect g r a b = ∫ z : ℝ × ℝ, (Ψ z + Ψ z.swap) := by
    rw [integral_add hΨi hΨswapi, hswap, hD]
    ring
  have hΘeq : (fun z : ℝ × ℝ => Ψ z + Ψ z.swap) = heightIntegrand g r a b := by
    funext z
    simp only [hΨ, hf1, hf2, hf3, hf4, Prod.fst_swap, Prod.snd_swap, heightIntegrand]
    ring
  rw [hdouble, hΘeq]

/-- Pointwise nonnegativity of the antisymmetrised integrand for `|b| ≤ |a|`. -/
theorem heightIntegrand_nonneg {g : ℝ → ℝ} (hnn : ∀ u, 0 ≤ g u) {r : ℝ} (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) {a b : ℝ} (hab : |b| ≤ |a|) (z : ℝ × ℝ) :
    0 ≤ heightIntegrand g r a b z := by
  unfold heightIntegrand
  by_cases h1 : g z.1 = 0
  · simp [h1]
  by_cases h2 : g z.2 = 0
  · simp [h2]
  exact mul_nonneg (mul_nonneg (hnn _) (hnn _))
    (heightKernel2_nonneg hr hab (hrad _ h1) (hrad _ h2))

/-- **The nonstrict two-height detector.**  For a nonnegative radially admissible
taper the height defect is monotone in the height:

    |b| ≤ |a|  ⟹  D(a, b) ≥ 0. -/
theorem heightDefect_nonneg {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u) {r : ℝ} (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) {a b : ℝ} (hab : |b| ≤ |a|) :
    0 ≤ heightDefect g r a b := by
  have hrep := heightDefect_two_mul hg hgc r a b
  have hI : 0 ≤ ∫ z : ℝ × ℝ, heightIntegrand g r a b z :=
    integral_nonneg (heightIntegrand_nonneg hnn hr hrad hab)
  linarith

/-- **`twoRadiusEvenProfileDetectsHeightPair`.**  The two-height form of the
detector.  For a nonnegative, radially admissible taper that is strictly positive
at two points of different modulus, the two-radius even profiles of two heights
are strictly ordered by the size of the height:

    |b| < |a|  ⟹  D(a, b) = A_a(r) A_b(2r) - A_a(2r) A_b(r) > 0.

Parity is blind to the height; the two-radius projective shape is not. -/
theorem twoRadiusEvenProfileDetectsHeightPair {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hnn : ∀ u, 0 ≤ g u) {r : ℝ} (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
    {u₀ v₀ : ℝ} (hu₀ : 0 < g u₀) (hv₀ : 0 < g v₀) (hne : |u₀| ≠ |v₀|)
    {a b : ℝ} (hab : |b| < |a|) : 0 < heightDefect g r a b := by
  have hrep := heightDefect_two_mul hg hgc r a b
  have hΘnn : ∀ z : ℝ × ℝ, 0 ≤ heightIntegrand g r a b z :=
    heightIntegrand_nonneg hnn hr hrad hab.le
  have hWopen : IsOpen {z : ℝ × ℝ | 0 < g z.1 ∧ 0 < g z.2 ∧ |z.1| - |z.2| ≠ 0} := by
    have h1 : IsOpen {z : ℝ × ℝ | 0 < g z.1} :=
      isOpen_lt continuous_const (hg.comp continuous_fst)
    have h2 : IsOpen {z : ℝ × ℝ | 0 < g z.2} :=
      isOpen_lt continuous_const (hg.comp continuous_snd)
    have h3 : IsOpen {z : ℝ × ℝ | |z.1| - |z.2| ≠ 0} :=
      IsOpen.preimage (by fun_prop) isOpen_ne
    exact h1.inter (h2.inter h3)
  have hWne : ((u₀, v₀) : ℝ × ℝ) ∈ {z : ℝ × ℝ | 0 < g z.1 ∧ 0 < g z.2 ∧ |z.1| - |z.2| ≠ 0} :=
    ⟨hu₀, hv₀, sub_ne_zero.mpr hne⟩
  have hWsub : {z : ℝ × ℝ | 0 < g z.1 ∧ 0 < g z.2 ∧ |z.1| - |z.2| ≠ 0}
      ⊆ Function.support (heightIntegrand g r a b) := by
    rintro z ⟨h1, h2, h3⟩
    have hk := heightKernel2_pos hr hab (hrad _ (ne_of_gt h1)) (hrad _ (ne_of_gt h2))
      (sub_ne_zero.mp h3)
    have hz : 0 < heightIntegrand g r a b z := by
      unfold heightIntegrand
      exact mul_pos (mul_pos h1 h2) hk
    exact ne_of_gt hz
  have hpos : 0 < ∫ z : ℝ × ℝ, heightIntegrand g r a b z := by
    rw [integral_pos_iff_support_of_nonneg hΘnn (integrable_heightIntegrand hg hgc r a b)]
    exact lt_of_lt_of_le (hWopen.measure_pos volume ⟨(u₀, v₀), hWne⟩) (measure_mono hWsub)
  linarith

/-- **`twoRadiusEvenProfileDetectsHeight`.**  The `b = 0` case of
`twoRadiusEvenProfileDetectsHeightPair`: the two-radius even profile of a nonzero
height is strictly on one side of the on-line profile,

    a ≠ 0  ⟹  A_a(r) A_0(2r) - A_a(2r) A_0(r) > 0. -/
theorem twoRadiusEvenProfileDetectsHeight {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hnn : ∀ u, 0 ≤ g u) {r : ℝ} (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
    {u₀ v₀ : ℝ} (hu₀ : 0 < g u₀) (hv₀ : 0 < g v₀) (hne : |u₀| ≠ |v₀|)
    {a : ℝ} (ha : a ≠ 0) : 0 < heightDefect g r a 0 :=
  twoRadiusEvenProfileDetectsHeightPair hg hgc hnn hr hrad hu₀ hv₀ hne
    (by simpa using abs_pos.mpr ha)

/-- **`twoRadiusProfile_not_proportional`.**  Consequently the two-radius even
profile of an off-line height is never a multiple of the on-line profile: the four
sampled values *do* carry the height, in their radial shape. -/
theorem twoRadiusProfile_not_proportional {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hnn : ∀ u, 0 ≤ g u) {r : ℝ} (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
    {u₀ v₀ : ℝ} (hu₀ : 0 < g u₀) (hv₀ : 0 < g v₀) (hne : |u₀| ≠ |v₀|)
    {a : ℝ} (ha : a ≠ 0) :
    ¬ ∃ c : ℝ, evenProfile g r a = c • evenProfile g r 0 := by
  rintro ⟨c, hc⟩
  have h1 : evenResp g a r = c * evenResp g 0 r := congrArg Prod.fst hc
  have h2 : evenResp g a (2 * r) = c * evenResp g 0 (2 * r) := congrArg Prod.snd hc
  have hD := twoRadiusEvenProfileDetectsHeight hg hgc hnn hr hrad hu₀ hv₀ hne ha
  unfold heightDefect at hD
  rw [h1, h2] at hD
  nlinarith [hD]

/-- The two negative/positive halves side by side, for the strengthened positive
taper: parity cannot see the height, the two-radius profile can. -/
theorem parityBlind_but_twoRadiusDetects {t : ℝ} (ht : t ≠ 0) {a : ℝ} (ha : a ≠ 0) :
    ∃ (g : ℝ → ℝ) (r : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ poleEvenResp g t r = 0
      ∧ (∀ m : ℝ, m • targetParityVec g a r + m • targetParityVec g (-a) r ∈ evenSubspace)
      ∧ 0 < heightDefect g r a 0 := by
  obtain ⟨g, r, hgs, hgc, heven, hrpos, hnn, hrad, ⟨u₀, v₀, hu₀, hv₀, hne⟩, hpole, -, -⟩ :=
    exists_positive_taper_poleEven_zero ht
  refine ⟨g, r, hgs, hgc, heven, hrpos, hpole,
    fun m => (pairParityCannotDetectHeight g r m a).1, ?_⟩
  exact twoRadiusEvenProfileDetectsHeight hgs.continuous hgc hnn hrpos hrad hu₀ hv₀ hne ha


/-! ### The cluster-level detector

A same-ordinate cluster contributes a *positive* combination of the two-radius
profiles of the heights of its members.  Because the height defect is bilinear in
the two profiles and nonnegative in the height, the whole cluster inherits the
detector: if a single member of the cluster is off-line, then the cluster's own
two-radius profile is strictly on the off-line side of the on-line profile. -/

/-- The bilinear determinant of two two-radius profiles. -/
def profileDefect (p q : ℝ × ℝ) : ℝ := p.1 * q.2 - p.2 * q.1

theorem heightDefect_eq_profileDefect (g : ℝ → ℝ) (r a b : ℝ) :
    heightDefect g r a b = profileDefect (evenProfile g r a) (evenProfile g r b) := rfl

/-- The two-radius profile of a finite cluster of heights with weights. -/
def clusterProfile {ι : Type*} (g : ℝ → ℝ) (r : ℝ) (s : Finset ι) (m a : ι → ℝ) : ℝ × ℝ :=
  ∑ i ∈ s, m i • evenProfile g r (a i)

theorem profileDefect_sum_left {ι : Type*} (s : Finset ι) (p : ι → ℝ × ℝ) (m : ι → ℝ)
    (q : ℝ × ℝ) :
    profileDefect (∑ i ∈ s, m i • p i) q = ∑ i ∈ s, m i * profileDefect (p i) q := by
  classical
  induction s using Finset.induction with
  | empty => simp [profileDefect]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
      simp only [profileDefect, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
      ring

/-- **`clusterTwoRadiusProfileDetectsOffLine`.**  A positively weighted cluster of
heights cannot hide an off-line member from the two-radius even profile: if some
member has nonzero height and positive weight, the cluster profile is strictly on
the off-line side of the on-line profile.

This is the projective counterpart of the same-ordinate cone positivity: parity
cannot see the height of *any* member, but the two-radius shape of the whole
cluster does. -/
theorem clusterTwoRadiusProfileDetectsOffLine {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hnn : ∀ u, 0 ≤ g u) {r : ℝ} (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
    {u₀ v₀ : ℝ} (hu₀ : 0 < g u₀) (hv₀ : 0 < g v₀) (hne : |u₀| ≠ |v₀|)
    {ι : Type*} (s : Finset ι) (m a : ι → ℝ) (hm : ∀ i ∈ s, 0 ≤ m i)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hm₀ : 0 < m i₀) (ha₀ : a i₀ ≠ 0) :
    0 < profileDefect (clusterProfile g r s m a) (evenProfile g r 0) := by
  rw [clusterProfile, profileDefect_sum_left]
  refine Finset.sum_pos' (fun i hi => ?_) ⟨i₀, hi₀, ?_⟩
  · exact mul_nonneg (hm i hi)
      (heightDefect_nonneg hg hgc hnn hr hrad (by simp [abs_nonneg]))
  · exact mul_pos hm₀ (twoRadiusEvenProfileDetectsHeight hg hgc hnn hr hrad hu₀ hv₀ hne ha₀)

/-- If every member of a positively weighted cluster is on the critical line, the
cluster profile is exactly proportional to the on-line profile: the defect
vanishes.  Together with `clusterTwoRadiusProfileDetectsOffLine` this makes the
two-radius profile a *sharp* on-line/off-line discriminator for finite clusters. -/
theorem clusterProfileDefect_eq_zero_of_onLine {g : ℝ → ℝ} (r : ℝ)
    {ι : Type*} (s : Finset ι) (m a : ι → ℝ) (ha : ∀ i ∈ s, a i = 0) :
    profileDefect (clusterProfile g r s m a) (evenProfile g r 0) = 0 := by
  rw [clusterProfile, profileDefect_sum_left]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  rw [ha i hi]
  have : profileDefect (evenProfile g r 0) (evenProfile g r 0) = 0 := by
    simp [profileDefect]; ring
  rw [this, mul_zero]

end LiteralWeilTwoRadiusHeightDetector
end Zeta23Bridge
