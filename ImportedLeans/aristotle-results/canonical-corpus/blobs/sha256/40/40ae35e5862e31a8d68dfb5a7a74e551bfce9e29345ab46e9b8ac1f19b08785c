/-
# The three-window seed: two genuinely different pole-null gate tapers

The Schur programme of `MultiTaperSchurCore` / `LiteralWeilTwoTaperCoefficientGate`
needs *several* independently admissible tapers: no signed combination of the final
tapers may be used to manufacture positivity after the fact.  This module supplies
the first literal instance, with two.

The existing even-channel construction uses two windows,

    c₋ = π/t   (where `cos(tu) < 0`)   and   c₊ = 2π/t   (where `cos(tu) > 0`),

and forms `g = g₋ + λ g₊` with `λ = -P(g₋)/P(g₊) > 0`, which is nonnegative and kills
the even pole response exactly.  Here a **third** window is added,

    c₊' = 15π/(8t),   of radius   π/(16t),

which also has `cos(tu) > 0` but is disjoint from the second one.  Running the same
balancing construction against each positive window separately produces two tapers

    g₀ = g₋ + λ₀ g₊,     g₁ = g₋ + λ₁ g₊',

each of which is individually `GateData` — `C²`, compactly supported, even,
nonnegative, radially admissible at the doubled radius, short enough to annihilate
the prime channel, pole-null at the base radius, and positive at two points of
different modulus — and which are **distinct**, since `g₀` is strictly positive at
`2π/t` while `g₁` vanishes there.

The sampling radius is no longer locked to the maximal value `t/16`: the construction
accepts any `0 < r ≤ t/16`, and the high-ordinate wrapper takes `r = min 1 (|t|/16)`,
which is what the radius-free coefficient gate of
`LiteralWeilTwoTaperCoefficientGate` requires (`r ≤ 1`).

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

noncomputable section

open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilThreeWindowPoleNullSeed

open Zeta23Bridge.LiteralWeilParityBalance Zeta23Bridge.LiteralWeilOddChannelTaper
open Zeta23Bridge.LiteralWeilEvenChannelTaper Zeta23Bridge.LiteralWeilPrimeEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

/-! ## A symmetrised localized window taper -/

/-- A symmetrised bump localized in the window `|u - c| < R` (and its mirror image):
smooth, even, nonnegative, strictly positive at `c`, supported in `|u| < |c| + R`,
identically zero off the two windows, and with strictly positive integral against any
continuous even weight that is strictly positive on the window. -/
theorem exists_window_taper (c : ℝ) {R : ℝ} (hR : 0 < R) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ Continuous g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ (∀ u, 0 ≤ g u) ∧ 0 < g c
      ∧ (∀ u, g u ≠ 0 → |u| < |c| + R)
      ∧ (∀ u, R ≤ |u - c| → R ≤ |u + c| → g u = 0)
      ∧ (∀ w : ℝ → ℝ, Continuous w → (∀ u, w (-u) = w u) →
          (∀ u, |u - c| < R → 0 < w u) → 0 < ∫ u : ℝ, g u * w u) := by
  obtain ⟨φ, hφd, hφc, hφs, hφn, hφsupp, hφpos, hφc₀⟩ := exists_bump_localized c hR
  refine ⟨symmetrize φ, symmetrize_contDiff hφd, symmetrize_continuous hφc,
    symmetrize_hasCompactSupport hφs, symmetrize_even φ, fun u => add_nonneg (hφn u) (hφn (-u)),
    ?_, ?_, ?_, ?_⟩
  · have : 0 ≤ φ (-c) := hφn (-c)
    show 0 < φ c + φ (-c)
    linarith
  · intro u hu
    have hcases : φ u ≠ 0 ∨ φ (-u) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hu (by show φ u + φ (-u) = 0; rw [hcon.1, hcon.2]; ring)
    rcases hcases with h | h
    · have hb := hφsupp u h
      have := abs_sub_abs_le_abs_sub u c
      linarith
    · have hb := hφsupp (-u) h
      have habs : |(-u) - c| = |u + c| := by
        rw [show (-u) - c = -(u + c) by ring, abs_neg]
      rw [habs] at hb
      have h1 : |u| = |-u| := (abs_neg u).symm
      have h2 := abs_sub_abs_le_abs_sub (-u) c
      rw [habs] at h2
      have h3 : |-u| = |u| := abs_neg u
      linarith [h2, hb]
  · intro u h1 h2
    have hu : φ u = 0 := by
      by_contra hcon
      exact absurd (hφsupp u hcon) (by linarith)
    have hu' : φ (-u) = 0 := by
      by_contra hcon
      have := hφsupp (-u) hcon
      have habs : |(-u) - c| = |u + c| := by
        rw [show (-u) - c = -(u + c) by ring, abs_neg]
      rw [habs] at this
      linarith
    show φ u + φ (-u) = 0
    rw [hu, hu']; ring
  · intro w hw hweven hwpos
    rw [integral_symmetrize hφc hφs hw hweven]
    have := hφpos w hw hwpos
    linarith

/-! ## The three windows -/

section Windows

variable {t : ℝ}

/-- The taper weight of the even pole response. -/
def poleWeight (t r : ℝ) : ℝ → ℝ := fun u => Real.cosh (u / 2) * Real.cos (t * u) * Real.cos (r * u)

/-- The taper weight of the even response at height `a`. -/
def heightWeight (a r : ℝ) : ℝ → ℝ := fun u => Real.cosh (a * u) * Real.cos (r * u)

theorem poleWeight_continuous (t r : ℝ) : Continuous (poleWeight t r) := by
  unfold poleWeight; fun_prop

theorem heightWeight_continuous (a r : ℝ) : Continuous (heightWeight a r) := by
  unfold heightWeight; fun_prop

theorem poleWeight_even (t r : ℝ) (u : ℝ) : poleWeight t r (-u) = poleWeight t r u := by
  unfold poleWeight
  rw [show -u / 2 = -(u / 2) by ring, Real.cosh_neg, show t * -u = -(t * u) by ring,
    show r * -u = -(r * u) by ring, Real.cos_neg, Real.cos_neg]

theorem heightWeight_even (a r : ℝ) (u : ℝ) : heightWeight a r (-u) = heightWeight a r u := by
  unfold heightWeight
  rw [show a * -u = -(a * u) by ring, show r * -u = -(r * u) by ring, Real.cosh_neg, Real.cos_neg]

theorem poleEvenResp_eq_integral (g : ℝ → ℝ) (t r : ℝ) :
    poleEvenResp g t r = ∫ u : ℝ, g u * poleWeight t r u := rfl

theorem evenResp_eq_integral (g : ℝ → ℝ) (a r : ℝ) :
    evenResp g a r = ∫ u : ℝ, g u * heightWeight a r u := rfl

end Windows

/-! ## Elementary window-geometry inequalities

These are separated out so that the main construction never has to run a
decision procedure inside its large context. -/

theorem frac_le_frac {a b c d : ℝ} (hc : 0 < c) (hd : 0 < d) (h : a * d ≤ b * c) :
    a / c ≤ b / d :=
  (div_le_div_iff₀ hc hd).mpr h

variable {t : ℝ}

theorem five_le_nine (ht : 0 < t) : 5 * π / (4 * t) ≤ 9 * π / (4 * t) := by
  have hpi := Real.pi_pos
  exact frac_le_frac (by positivity) (by positivity) (by nlinarith [mul_pos hpi ht])

theorem thirtyone_le_nine (ht : 0 < t) : 31 * π / (16 * t) ≤ 9 * π / (4 * t) := by
  have hpi := Real.pi_pos
  exact frac_le_frac (by positivity) (by positivity) (by nlinarith [mul_pos hpi ht])

theorem quarter_le_one (ht : 0 < t) : π / (4 * t) ≤ π / t := by
  have hpi := Real.pi_pos
  exact frac_le_frac (by positivity) (by positivity) (by nlinarith [mul_pos hpi ht])

theorem quarter_le_three (ht : 0 < t) : π / (4 * t) ≤ 3 * π / t := by
  have hpi := Real.pi_pos
  exact frac_le_frac (by positivity) (by positivity) (by nlinarith [mul_pos hpi ht])

theorem sixteenth_le_eighth (ht : 0 < t) : π / (16 * t) ≤ π / (8 * t) := by
  have hpi := Real.pi_pos
  exact frac_le_frac (by positivity) (by positivity) (by nlinarith [mul_pos hpi ht])

theorem sixteenth_le_thirtyone_eighth (ht : 0 < t) : π / (16 * t) ≤ 31 * π / (8 * t) := by
  have hpi := Real.pi_pos
  exact frac_le_frac (by positivity) (by positivity) (by nlinarith [mul_pos hpi ht])

/-! ## The pair of pole-null gate tapers, for a positive ordinate -/

/-- **The three-window seed.**  For a positive ordinate high enough that the literal
prime frequencies fall outside the taper support, and for *any* sampling radius
`0 < r ≤ t/16`, there are two **distinct** tapers, each of which is admissible gate
data with the same radius and the same support radius `Λ = 9π/(4t)`. -/
theorem exists_gateData_pair_pos {t : ℝ} (ht : 0 < t) (hheight : 9 * π ≤ 4 * t * Real.log 2)
    {r : ℝ} (hrpos : 0 < r) (hrle : r ≤ t / 16) :
    ∃ g₀ g₁ : ℝ → ℝ, GateData g₀ t r (9 * π / (4 * t)) ∧ GateData g₁ t r (9 * π / (4 * t))
      ∧ g₀ ≠ g₁ := by
  have hpi := Real.pi_pos
  have htne : t ≠ 0 := ne_of_gt ht
  -- the three window centres and the two radii
  obtain ⟨cm, hcm⟩ : ∃ x : ℝ, x = π / t := ⟨_, rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ x : ℝ, x = 2 * π / t := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ x : ℝ, x = 15 * π / (8 * t) := ⟨_, rfl⟩
  obtain ⟨Rm, hRm⟩ : ∃ x : ℝ, x = π / (4 * t) := ⟨_, rfl⟩
  obtain ⟨R2, hR2⟩ : ∃ x : ℝ, x = π / (16 * t) := ⟨_, rfl⟩
  have hRmpos : 0 < Rm := by rw [hRm]; positivity
  have hR2pos : 0 < R2 := by rw [hR2]; positivity
  -- scaling helpers
  have hcancel : ∀ x : ℝ, t * (x / t) = x := fun x => by field_simp
  have hmul1 : ∀ x u : ℝ, x / t < u → x < t * u := by
    intro x u h
    have h2 := mul_lt_mul_of_pos_left h ht
    rwa [hcancel] at h2
  have hmul2 : ∀ x u : ℝ, u < x / t → t * u < x := by
    intro x u h
    have h2 := mul_lt_mul_of_pos_left h ht
    rwa [hcancel] at h2
  -- the support radius bound, from a bound on `t u`
  have habsu : ∀ u : ℝ, 0 < t * u → t * u < 9 * π / 4 → |u| < 9 * π / (4 * t) := by
    intro u h1 h2
    have hu0 : 0 < u := by nlinarith
    rw [abs_of_pos hu0, lt_div_iff₀ (by positivity : (0:ℝ) < 4 * t)]
    nlinarith
  -- positivity of `cos (r u)` on the whole support
  have hcosr : ∀ u : ℝ, |u| < 9 * π / (4 * t) → 0 < Real.cos (r * u) := by
    intro u hu
    have habs : |r * u| < π / 2 := by
      have h1 : |r * u| = r * |u| := by
        rw [abs_mul, abs_of_pos hrpos]
      have h2 : r * |u| ≤ t / 16 * |u| := mul_le_mul_of_nonneg_right hrle (abs_nonneg u)
      have h3 : t / 16 * |u| < t / 16 * (9 * π / (4 * t)) :=
        mul_lt_mul_of_pos_left hu (by positivity)
      have h4 : t / 16 * (9 * π / (4 * t)) = 9 * π / 64 := by field_simp; ring
      rw [h1]
      rw [h4] at h3
      linarith
    rw [abs_lt] at habs
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [habs.1], habs.2⟩
  -- the three windows, in terms of `t u`
  have hwinm : ∀ u : ℝ, |u - cm| < Rm → 3 * π / 4 < t * u ∧ t * u < 5 * π / 4 := by
    intro u hu
    rw [abs_lt] at hu
    have hlow : (3 * π / 4) / t < u := by
      have : cm - Rm = (3 * π / 4) / t := by rw [hcm, hRm]; field_simp; ring
      linarith [hu.1, this ▸ (by linarith [hu.1] : cm - Rm < u)]
    have hhigh : u < (5 * π / 4) / t := by
      have : cm + Rm = (5 * π / 4) / t := by rw [hcm, hRm]; field_simp; ring
      linarith [hu.2, this ▸ (by linarith [hu.2] : u < cm + Rm)]
    exact ⟨hmul1 _ _ hlow, hmul2 _ _ hhigh⟩
  have hwin1 : ∀ u : ℝ, |u - c1| < Rm → 7 * π / 4 < t * u ∧ t * u < 9 * π / 4 := by
    intro u hu
    rw [abs_lt] at hu
    have hlow : (7 * π / 4) / t < u := by
      have : c1 - Rm = (7 * π / 4) / t := by rw [hc1, hRm]; field_simp; ring
      linarith [hu.1, this ▸ (by linarith [hu.1] : c1 - Rm < u)]
    have hhigh : u < (9 * π / 4) / t := by
      have : c1 + Rm = (9 * π / 4) / t := by rw [hc1, hRm]; field_simp; ring
      linarith [hu.2, this ▸ (by linarith [hu.2] : u < c1 + Rm)]
    exact ⟨hmul1 _ _ hlow, hmul2 _ _ hhigh⟩
  have hwin2 : ∀ u : ℝ, |u - c2| < R2 → 29 * π / 16 < t * u ∧ t * u < 31 * π / 16 := by
    intro u hu
    rw [abs_lt] at hu
    have hlow : (29 * π / 16) / t < u := by
      have : c2 - R2 = (29 * π / 16) / t := by rw [hc2, hR2]; field_simp; ring
      linarith [hu.1, this ▸ (by linarith [hu.1] : c2 - R2 < u)]
    have hhigh : u < (31 * π / 16) / t := by
      have : c2 + R2 = (31 * π / 16) / t := by rw [hc2, hR2]; field_simp; ring
      linarith [hu.2, this ▸ (by linarith [hu.2] : u < c2 + R2)]
    exact ⟨hmul1 _ _ hlow, hmul2 _ _ hhigh⟩
  -- sign of `cos (t u)` on each window
  have hcospos : ∀ u : ℝ, 7 * π / 4 < t * u → t * u < 9 * π / 4 → 0 < Real.cos (t * u) := by
    intro u h1 h2
    rw [← Real.cos_sub_two_pi]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcosneg : ∀ u : ℝ, 3 * π / 4 < t * u → t * u < 5 * π / 4 → Real.cos (t * u) < 0 := by
    intro u h1 h2
    have hshift : 0 < Real.cos (t * u - π) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    rw [Real.cos_sub_pi] at hshift
    linarith
  -- the three window tapers
  obtain ⟨gm, hgmd, hgmc, hgms, hgme, hgmn, hgmc₀, hgmsupp, hgmzero, hgmpos⟩ :=
    exists_window_taper cm hRmpos
  obtain ⟨h1, hh1d, hh1c, hh1s, hh1e, hh1n, hh1c₀, hh1supp, hh1zero, hh1pos⟩ :=
    exists_window_taper c1 hRmpos
  obtain ⟨h2, hh2d, hh2c, hh2s, hh2e, hh2n, hh2c₀, hh2supp, hh2zero, hh2pos⟩ :=
    exists_window_taper c2 hR2pos
  -- support radii
  have hcmabs : |cm| = cm := abs_of_pos (by rw [hcm]; positivity)
  have hc1abs : |c1| = c1 := abs_of_pos (by rw [hc1]; positivity)
  have hc2abs : |c2| = c2 := abs_of_pos (by rw [hc2]; positivity)
  have hgmsupp' : ∀ u, gm u ≠ 0 → |u| < 9 * π / (4 * t) := by
    intro u hu
    have := hgmsupp u hu
    rw [hcmabs] at this
    have hval : cm + Rm ≤ 9 * π / (4 * t) := by
      have h5 : cm + Rm = 5 * π / (4 * t) := by rw [hcm, hRm]; field_simp; ring
      rw [h5]
      exact five_le_nine ht
    linarith
  have hh1supp' : ∀ u, h1 u ≠ 0 → |u| < 9 * π / (4 * t) := by
    intro u hu
    have := hh1supp u hu
    rw [hc1abs] at this
    have hval : c1 + Rm = 9 * π / (4 * t) := by rw [hc1, hRm]; field_simp; ring
    linarith [hval ▸ this]
  have hh2supp' : ∀ u, h2 u ≠ 0 → |u| < 9 * π / (4 * t) := by
    intro u hu
    have := hh2supp u hu
    rw [hc2abs] at this
    have hval : c2 + R2 ≤ 9 * π / (4 * t) := by
      have h31 : c2 + R2 = 31 * π / (16 * t) := by rw [hc2, hR2]; field_simp; ring
      rw [h31]
      exact thirtyone_le_nine ht
    linarith
  -- pole responses
  have hPm : poleEvenResp gm t r < 0 := by
    have hpos := hgmpos (fun u => -poleWeight t r u) ((poleWeight_continuous t r).neg)
      (fun u => by simp [poleWeight_even t r u]) ?_
    · have hrw : (fun u : ℝ => gm u * -poleWeight t r u)
          = fun u : ℝ => -(gm u * poleWeight t r u) := by funext u; ring
      rw [hrw, MeasureTheory.integral_neg] at hpos
      rw [poleEvenResp_eq_integral]
      linarith
    · intro u hu
      obtain ⟨h1', h2'⟩ := hwinm u hu
      have hcr : 0 < Real.cos (r * u) := hcosr u (habsu u (by linarith) (by linarith))
      have hct : Real.cos (t * u) < 0 := hcosneg u h1' h2'
      have hch : 0 < Real.cosh (u / 2) := Real.cosh_pos _
      have hneg : poleWeight t r u < 0 := by
        unfold poleWeight
        exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hch hct) hcr
      simpa using neg_pos.mpr hneg
  have hP1 : 0 < poleEvenResp h1 t r := by
    rw [poleEvenResp_eq_integral]
    refine hh1pos (poleWeight t r) (poleWeight_continuous t r) (poleWeight_even t r) ?_
    intro u hu
    obtain ⟨ha, hb⟩ := hwin1 u hu
    have hcr : 0 < Real.cos (r * u) := hcosr u (habsu u (by linarith) (by linarith))
    have hct : 0 < Real.cos (t * u) := hcospos u ha hb
    have hch : 0 < Real.cosh (u / 2) := Real.cosh_pos _
    unfold poleWeight
    positivity
  have hP2 : 0 < poleEvenResp h2 t r := by
    rw [poleEvenResp_eq_integral]
    refine hh2pos (poleWeight t r) (poleWeight_continuous t r) (poleWeight_even t r) ?_
    intro u hu
    obtain ⟨ha, hb⟩ := hwin2 u hu
    have hcr : 0 < Real.cos (r * u) := hcosr u (habsu u (by linarith) (by linarith))
    have hct : 0 < Real.cos (t * u) := hcospos u (by linarith) (by linarith)
    have hch : 0 < Real.cosh (u / 2) := Real.cosh_pos _
    unfold poleWeight
    positivity
  -- height responses
  have hQm : ∀ a : ℝ, 0 < evenResp gm a r := by
    intro a
    rw [evenResp_eq_integral]
    refine hgmpos (heightWeight a r) (heightWeight_continuous a r) (heightWeight_even a r) ?_
    intro u hu
    obtain ⟨ha, hb⟩ := hwinm u hu
    have hcr : 0 < Real.cos (r * u) := hcosr u (habsu u (by linarith) (by linarith))
    have hch : 0 < Real.cosh (a * u) := Real.cosh_pos _
    unfold heightWeight
    positivity
  have hQ1 : ∀ a : ℝ, 0 < evenResp h1 a r := by
    intro a
    rw [evenResp_eq_integral]
    refine hh1pos (heightWeight a r) (heightWeight_continuous a r) (heightWeight_even a r) ?_
    intro u hu
    obtain ⟨ha, hb⟩ := hwin1 u hu
    have hcr : 0 < Real.cos (r * u) := hcosr u (habsu u (by linarith) (by linarith))
    have hch : 0 < Real.cosh (a * u) := Real.cosh_pos _
    unfold heightWeight
    positivity
  have hQ2 : ∀ a : ℝ, 0 < evenResp h2 a r := by
    intro a
    rw [evenResp_eq_integral]
    refine hh2pos (heightWeight a r) (heightWeight_continuous a r) (heightWeight_even a r) ?_
    intro u hu
    obtain ⟨ha, hb⟩ := hwin2 u hu
    have hcr : 0 < Real.cos (r * u) := hcosr u (habsu u (by linarith) (by linarith))
    have hch : 0 < Real.cosh (a * u) := Real.cosh_pos _
    unfold heightWeight
    positivity
  -- the two balancing coefficients
  set lam1 : ℝ := -poleEvenResp gm t r / poleEvenResp h1 t r with hlam1
  set lam2 : ℝ := -poleEvenResp gm t r / poleEvenResp h2 t r with hlam2
  have hlam1pos : 0 < lam1 := div_pos (by linarith) hP1
  have hlam2pos : 0 < lam2 := div_pos (by linarith) hP2
  set g₀ : ℝ → ℝ := fun u => gm u + lam1 * h1 u with hg₀
  set g₁ : ℝ → ℝ := fun u => gm u + lam2 * h2 u with hg₁
  -- a uniform packaging of the two gate data
  have hbuild : ∀ (h : ℝ → ℝ) (lam : ℝ), ContDiff ℝ 2 h → Continuous h → HasCompactSupport h →
      (∀ u, h (-u) = h u) → (∀ u, 0 ≤ h u) → (∀ u, h u ≠ 0 → |u| < 9 * π / (4 * t)) →
      0 < lam → poleEvenResp gm t r + lam * poleEvenResp h t r = 0 →
      (∃ v : ℝ, 0 < h v ∧ |v| ≠ |cm|) →
      GateData (fun u => gm u + lam * h u) t r (9 * π / (4 * t)) := by
    intro h lam hhd hhc hhs hhe hhn hhsupp hlampos hbal hwit
    have hsupp : ∀ u, (fun u => gm u + lam * h u) u ≠ 0 → |u| < 9 * π / (4 * t) := by
      intro u hu
      have hcases : gm u ≠ 0 ∨ h u ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hu (by show gm u + lam * h u = 0; rw [hcon.1, hcon.2]; ring)
      rcases hcases with hc | hc
      · exact hgmsupp' u hc
      · exact hhsupp u hc
    refine ⟨hgmd.add (contDiff_const.mul hhd), hgms.add hhs.mul_left, ?_, ?_, hrpos, ?_,
      fun u hu => (hsupp u hu).le, by positivity, ?_, ?_, ?_⟩
    · intro u
      show gm (-u) + lam * h (-u) = gm u + lam * h u
      rw [hgme, hhe]
    · intro u
      have := hgmn u
      have := mul_nonneg hlampos.le (hhn u)
      show 0 ≤ gm u + lam * h u
      linarith
    · intro u hu
      have hb := hsupp u hu
      have hkey : 2 * r * |u| < 2 * (t / 16) * (9 * π / (4 * t)) := by
        have h1' : 2 * r * |u| ≤ 2 * (t / 16) * |u| := by
          have := mul_le_mul_of_nonneg_right hrle (abs_nonneg u)
          nlinarith [abs_nonneg u]
        have h2' : 2 * (t / 16) * |u| < 2 * (t / 16) * (9 * π / (4 * t)) :=
          mul_lt_mul_of_pos_left hb (by positivity)
        linarith
      have hval : 2 * (t / 16) * (9 * π / (4 * t)) = 9 * π / 32 := by field_simp; ring
      rw [hval] at hkey
      linarith
    · intro u hu
      have hb := hsupp u hu
      have hle : 9 * π / (4 * t) ≤ Real.log 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    · rw [poleEvenResp_add_smul hgmc hgms hhc hhs]
      exact hbal
    · obtain ⟨v, hv, hvne⟩ := hwit
      refine ⟨cm, v, ?_, ?_, ?_⟩
      · have h1' : 0 ≤ lam * h cm := mul_nonneg hlampos.le (hhn cm)
        show 0 < gm cm + lam * h cm
        linarith [hgmc₀]
      · have h1' : 0 ≤ gm v := hgmn v
        have h2' : 0 < lam * h v := mul_pos hlampos hv
        show 0 < gm v + lam * h v
        linarith
      · exact Ne.symm hvne
  -- balance identities
  have hbal1 : poleEvenResp gm t r + lam1 * poleEvenResp h1 t r = 0 := by
    have hcancel1 : lam1 * poleEvenResp h1 t r = -poleEvenResp gm t r := by
      rw [hlam1]; field_simp
    rw [hcancel1]; ring
  have hbal2 : poleEvenResp gm t r + lam2 * poleEvenResp h2 t r = 0 := by
    have hcancel2 : lam2 * poleEvenResp h2 t r = -poleEvenResp gm t r := by
      rw [hlam2]; field_simp
    rw [hcancel2]; ring
  have hcmne1 : |c1| ≠ |cm| := by
    rw [hc1abs, hcmabs, hc1, hcm]
    intro hcon
    have : π / t = 0 := by
      have h2 : 2 * π / t - π / t = π / t := by field_simp; ring
      linarith [hcon, h2]
    have : (0:ℝ) < π / t := by positivity
    linarith
  have hcmne2 : |c2| ≠ |cm| := by
    rw [hc2abs, hcmabs, hc2, hcm]
    intro hcon
    have hgap : 15 * π / (8 * t) - π / t = 7 * π / (8 * t) := by field_simp; ring
    have : (0:ℝ) < 7 * π / (8 * t) := by positivity
    linarith
  refine ⟨g₀, g₁, hbuild h1 lam1 hh1d hh1c hh1s hh1e hh1n hh1supp' hlam1pos hbal1 ⟨c1, hh1c₀, hcmne1⟩,
    hbuild h2 lam2 hh2d hh2c hh2s hh2e hh2n hh2supp' hlam2pos hbal2 ⟨c2, hh2c₀, hcmne2⟩, ?_⟩
  -- distinctness: `g₀` is positive at `c1`, `g₁` vanishes there
  have hgmc1 : gm c1 = 0 := by
    refine hgmzero c1 ?_ ?_
    · have : |c1 - cm| = π / t := by
        rw [hc1, hcm, show 2 * π / t - π / t = π / t by field_simp; ring]
        exact abs_of_pos (by positivity)
      rw [this, hRm]
      exact quarter_le_one ht
    · have : |c1 + cm| = 3 * π / t := by
        rw [hc1, hcm, show 2 * π / t + π / t = 3 * π / t by field_simp; ring]
        exact abs_of_pos (by positivity)
      rw [this, hRm]
      exact quarter_le_three ht
  have hh2c1 : h2 c1 = 0 := by
    refine hh2zero c1 ?_ ?_
    · have : |c1 - c2| = π / (8 * t) := by
        rw [hc1, hc2, show 2 * π / t - 15 * π / (8 * t) = π / (8 * t) by field_simp; ring]
        exact abs_of_pos (by positivity)
      rw [this, hR2]
      exact sixteenth_le_eighth ht
    · have : |c1 + c2| = 31 * π / (8 * t) := by
        rw [hc1, hc2, show 2 * π / t + 15 * π / (8 * t) = 31 * π / (8 * t) by field_simp; ring]
        exact abs_of_pos (by positivity)
      rw [this, hR2]
      exact sixteenth_le_thirtyone_eighth ht
  intro hcon
  have hval := congrFun hcon c1
  have hg₀c1 : 0 < g₀ c1 := by
    have : 0 < lam1 * h1 c1 := mul_pos hlam1pos hh1c₀
    show 0 < gm c1 + lam1 * h1 c1
    rw [hgmc1]
    linarith
  have hg₁c1 : g₁ c1 = 0 := by
    show gm c1 + lam2 * h2 c1 = 0
    rw [hgmc1, hh2c1]; ring
  rw [hval, hg₁c1] at hg₀c1
  exact lt_irrefl 0 hg₀c1

/-- **The high-ordinate wrapper.**  For an arbitrary nonzero high ordinate there are
two distinct gate tapers sharing a sampling radius `r ≤ 1` — the regime in which the
radius-free coefficient gate of `LiteralWeilTwoTaperCoefficientGate` applies. -/
theorem exists_gateData_pair {t : ℝ} (ht : t ≠ 0) (hheight : 9 * π ≤ 4 * |t| * Real.log 2) :
    ∃ (g₀ g₁ : ℝ → ℝ) (r : ℝ), 0 < r ∧ r ≤ 1
      ∧ GateData g₀ t r (9 * π / (4 * |t|)) ∧ GateData g₁ t r (9 * π / (4 * |t|))
      ∧ g₀ ≠ g₁ := by
  have habs : 0 < |t| := abs_pos.mpr ht
  set r : ℝ := min 1 (|t| / 16) with hr
  have hrpos : 0 < r := lt_min one_pos (by positivity)
  have hrle1 : r ≤ 1 := min_le_left _ _
  have hrle : r ≤ |t| / 16 := min_le_right _ _
  obtain ⟨g₀, g₁, hd₀, hd₁, hne⟩ := exists_gateData_pair_pos habs hheight hrpos hrle
  have htransfer : ∀ g : ℝ → ℝ, GateData g |t| r (9 * π / (4 * |t|)) →
      GateData g t r (9 * π / (4 * |t|)) := by
    intro g hd
    refine ⟨hd.smooth, hd.compactSupport, hd.isEven, hd.nonneg, hd.radiusPos, hd.radial,
      hd.supportRadius, hd.lambdaNonneg, hd.short, ?_, hd.twoPoint⟩
    rcases abs_cases t with ⟨he, -⟩ | ⟨he, -⟩
    · rw [← he]; exact hd.poleKilled
    · rw [show t = -|t| by rw [he]; ring, poleEvenResp_neg_ordinate]
      exact hd.poleKilled
  exact ⟨g₀, g₁, r, hrpos, hrle1, htransfer g₀ hd₀, htransfer g₁ hd₁, hne⟩

end LiteralWeilThreeWindowPoleNullSeed
end Zeta23Bridge
