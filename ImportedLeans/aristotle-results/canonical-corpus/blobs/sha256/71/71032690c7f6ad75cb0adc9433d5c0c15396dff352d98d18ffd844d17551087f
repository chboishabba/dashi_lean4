/-
# The even channel: a taper that survives the reflection partner

`LiteralWeilOtherZerosChannel.lean` showed that the *odd* four-sample coordinates
of a zero and of its functional-equation partner cancel exactly, so the odd-channel
transversality of `LiteralWeilOddChannelTaper.lean` cannot by itself produce a
contradiction.  What survives the pairing is the *even* coordinate: the pair
contributes `evenPattern (2 A_a(r)) (2 A_a(2r))`, which is generally nonzero.

This module constructs, unconditionally, a taper killing the ordinate-modulated
*even* pole response while keeping the even target response strictly positive.
The mechanism is the same window trick as in the odd channel, with the roles of
`sin` and `cos` exchanged: fix the sample radius `r = t/8` and use the windows
centred at `u = 2π/t` and `u = π/t`, on which `cos(tu)` is respectively strictly
positive and strictly negative while `cos(ru)` stays strictly positive; the target
weight `cosh(au) cos(ru)` is strictly positive on both, for *every* height `a`.

Consequences, all unconditional:

* `exists_taper_poleEven_zero_evenResp_ne_zero` — the construction.
* `evenPattern_quotient_ne_zero_of_poleEven_zero` — such a taper makes every
  nonzero multiple of the even target pattern transverse to the pole space.
* `literalWeilOffLineReflectionPairTransverse` — for an actual off-line zero of
  `riemannZeta` with nonzero ordinate, the literal Weil explicit formula supplies a
  four-sample balance relation in which the *whole reflection pair* is split off,
  the pole part is killed by the parity quotient, and

    `Q_rest + Q_prime + Q_Γ ≠ 0`,   `Q_pair = -(Q_rest + Q_prime + Q_Γ)`,

  where `Q_rest` now excludes both the target zero *and* its partner.

* `reflectionPair_parity_blindness` — and the honest limitation: for *every*
  height `a`, on-line (`a = 0`) included, the pair contribution is purely even.
  So no four-sample parity coordinate distinguishes an off-line reflection pair
  from an on-line one by parity alone; only the *value* of the even response `A_a`
  can.  Pure quotient geometry is therefore genuinely exhausted, and the remaining
  obligation is quantitative, not structural.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilOddChannelTaper
import Zeta23Bridge.LiteralWeilOtherZerosChannel

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilEvenChannelTaper

open Zeta23 Zeta23.EF Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilOddChannelTaper Zeta23Bridge.LiteralWeilOtherZerosChannel

/-! ## Linearity of the even responses in the taper -/

theorem evenResp_add_smul {a b : ℝ → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) (hbc : HasCompactSupport b) (lam y s : ℝ) :
    evenResp (fun u => a u + lam * b u) y s = evenResp a y s + lam * evenResp b y s := by
  unfold evenResp
  have h1 : Integrable (fun u : ℝ => a u * (Real.cosh (y * u) * Real.cos (s * u))) :=
    taper_integrable ha hac (by fun_prop)
  have h2 : Integrable (fun u : ℝ => lam * (b u * (Real.cosh (y * u) * Real.cos (s * u)))) :=
    ((taper_integrable hb hbc (by fun_prop)).const_mul lam)
  rw [show (fun u : ℝ => (a u + lam * b u) * (Real.cosh (y * u) * Real.cos (s * u)))
      = fun u : ℝ => a u * (Real.cosh (y * u) * Real.cos (s * u))
        + lam * (b u * (Real.cosh (y * u) * Real.cos (s * u))) by funext u; ring]
  rw [integral_add h1 h2, integral_const_mul]

theorem poleEvenResp_add_smul {a b : ℝ → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) (hbc : HasCompactSupport b) (lam t s : ℝ) :
    poleEvenResp (fun u => a u + lam * b u) t s
      = poleEvenResp a t s + lam * poleEvenResp b t s := by
  unfold poleEvenResp
  have h1 : Integrable
      (fun u : ℝ => a u * (Real.cosh (u / 2) * Real.cos (t * u) * Real.cos (s * u))) :=
    taper_integrable ha hac (by fun_prop)
  have h2 : Integrable
      (fun u : ℝ => lam * (b u * (Real.cosh (u / 2) * Real.cos (t * u) * Real.cos (s * u)))) :=
    ((taper_integrable hb hbc (by fun_prop)).const_mul lam)
  rw [show (fun u : ℝ => (a u + lam * b u)
        * (Real.cosh (u / 2) * Real.cos (t * u) * Real.cos (s * u)))
      = fun u : ℝ => a u * (Real.cosh (u / 2) * Real.cos (t * u) * Real.cos (s * u))
        + lam * (b u * (Real.cosh (u / 2) * Real.cos (t * u) * Real.cos (s * u))) by
    funext u; ring]
  rw [integral_add h1 h2, integral_const_mul]

/-- The even pole response is even in the ordinate. -/
theorem poleEvenResp_neg_ordinate (g : ℝ → ℝ) (t s : ℝ) :
    poleEvenResp g (-t) s = poleEvenResp g t s := by
  unfold poleEvenResp
  congr 1
  funext u
  rw [show -t * u = -(t * u) by ring, Real.cos_neg]

/-! ## The construction -/

/-- **The explicit even-channel taper, in strengthened positive form**, for a
positive ordinate `t`.

The taper is a *nonnegative* combination of two symmetrised bumps supported in the
two sampling windows `|u| ≈ π/t` and `|u| ≈ 2π/t`, and the sample radius is
`r = t/16`, small enough that `cos(ru)` *and* `cos(2ru)` stay strictly positive on
the support.  Consequently the even response `A_a(r) = ∫ g(u) cosh(au) cos(ru) du`
is strictly positive **at every height `a` simultaneously**, while the
ordinate-modulated even pole response still vanishes.  The support and two-point
positivity clauses are what later lets the same taper serve as a *positive even
cone*: every reflection pair, whatever its height, responds with the same sign. -/
theorem exists_positive_taper_poleEven_zero_pos {t : ℝ} (ht : 0 < t) :
    ∃ (g : ℝ → ℝ) (r : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ (∀ u, 0 ≤ g u)
      ∧ (∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
      ∧ (∃ u v : ℝ, 0 < g u ∧ 0 < g v ∧ |u| ≠ |v|)
      ∧ poleEvenResp g t r = 0
      ∧ (∀ a : ℝ, 0 < evenResp g a r)
      ∧ (∀ u, g u ≠ 0 → |u| < 9 * π / (4 * t)) := by
  have hpi := Real.pi_pos
  have htne : t ≠ 0 := ne_of_gt ht
  set r : ℝ := t / 16 with hr
  have hrpos : 0 < r := by positivity
  set R : ℝ := π / (4 * t) with hRdef
  have hRpos : 0 < R := by positivity
  set c₁ : ℝ := 2 * π / t with hc₁
  set c₂ : ℝ := π / t with hc₂
  have hc₂pos : 0 < c₂ := by rw [hc₂]; positivity
  have hc₂lt : c₂ < c₁ := by
    rw [hc₁, hc₂]
    have : 2 * π / t - π / t = π / t := by field_simp; ring
    linarith [hc₂pos, this]
  have hc₂R : 0 < c₂ - R := by
    have h : c₂ - R = 3 * π / (4 * t) := by rw [hc₂, hRdef]; field_simp; ring
    rw [h]; positivity
  set wp : ℝ → ℝ := fun u => Real.cosh (u / 2) * Real.cos (t * u) * Real.cos (r * u) with hwp
  set wt : ℝ → ℝ → ℝ := fun a u => Real.cosh (a * u) * Real.cos (r * u) with hwt
  have hwpc : Continuous wp := by rw [hwp]; fun_prop
  have hwtc : ∀ a : ℝ, Continuous (wt a) := by intro a; rw [hwt]; fun_prop
  have hwpe : ∀ u, wp (-u) = wp u := by
    intro u
    simp only [hwp]
    rw [show -u / 2 = -(u / 2) by ring, Real.cosh_neg, show t * -u = -(t * u) by ring,
      show r * -u = -(r * u) by ring, Real.cos_neg, Real.cos_neg]
  have hwte : ∀ a : ℝ, ∀ u, wt a (-u) = wt a u := by
    intro a u
    simp only [hwt]
    rw [show a * -u = -(a * u) by ring, show r * -u = -(r * u) by ring, Real.cosh_neg,
      Real.cos_neg]
  have hwtpos : ∀ a u : ℝ, 0 < Real.cos (r * u) → 0 < wt a u := by
    intro a u hu
    have hc : 0 < Real.cosh (a * u) := Real.cosh_pos _
    simp only [hwt]
    positivity
  -- `cos (r u) > 0` whenever `0 < t u < 3π`, since `r u = t u / 16 < 3π/16 < π/2`
  have hcosr : ∀ u : ℝ, 0 < t * u → t * u < 3 * π → 0 < Real.cos (r * u) := by
    intro u h1 h2
    have hru : r * u = t * u / 16 := by rw [hr]; ring
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · rw [hru]; linarith
    · rw [hru]; linarith
  -- window 1 : `cos (t u) > 0`
  have hwin₁ : ∀ u : ℝ, |u - c₁| < R → 0 < wp u ∧ 0 < Real.cos (r * u) := by
    intro u hu
    rw [abs_lt] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hlow : 7 * π / (4 * t) < u := by
      have h : c₁ - R < u := by linarith
      rw [hc₁, hRdef] at h
      calc 7 * π / (4 * t) = 2 * π / t - π / (4 * t) := by field_simp; ring
        _ < u := h
    have hhigh : u < 9 * π / (4 * t) := by
      have h : u < c₁ + R := by linarith
      rw [hc₁, hRdef] at h
      calc u < 2 * π / t + π / (4 * t) := h
        _ = 9 * π / (4 * t) := by field_simp; ring
    have htu_low : 7 * π / 4 < t * u := by
      have hlt : t * (7 * π / (4 * t)) < t * u := mul_lt_mul_of_pos_left hlow ht
      have h7 : t * (7 * π / (4 * t)) = 7 * π / 4 := by field_simp
      rw [h7] at hlt
      exact hlt
    have htu_high : t * u < 9 * π / 4 := by
      have hlt : t * u < t * (9 * π / (4 * t)) := mul_lt_mul_of_pos_left hhigh ht
      have h9 : t * (9 * π / (4 * t)) = 9 * π / 4 := by field_simp
      rw [h9] at hlt
      exact hlt
    have hcr : 0 < Real.cos (r * u) := hcosr u (by linarith) (by linarith)
    have hct : 0 < Real.cos (t * u) := by
      rw [← Real.cos_sub_two_pi]
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> [linarith; linarith]
    refine ⟨?_, hcr⟩
    rw [hwp]
    have : 0 < Real.cosh (u / 2) := Real.cosh_pos _
    positivity
  -- window 2 : `cos (t u) < 0`
  have hwin₂ : ∀ u : ℝ, |u - c₂| < R → 0 < -wp u ∧ 0 < Real.cos (r * u) := by
    intro u hu
    rw [abs_lt] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hlow : 3 * π / (4 * t) < u := by
      have h : c₂ - R < u := by linarith
      rw [hc₂, hRdef] at h
      calc 3 * π / (4 * t) = π / t - π / (4 * t) := by field_simp; ring
        _ < u := h
    have hhigh : u < 5 * π / (4 * t) := by
      have h : u < c₂ + R := by linarith
      rw [hc₂, hRdef] at h
      calc u < π / t + π / (4 * t) := h
        _ = 5 * π / (4 * t) := by field_simp; ring
    have htu_low : 3 * π / 4 < t * u := by
      have hlt : t * (3 * π / (4 * t)) < t * u := mul_lt_mul_of_pos_left hlow ht
      have h3 : t * (3 * π / (4 * t)) = 3 * π / 4 := by field_simp
      rw [h3] at hlt
      exact hlt
    have htu_high : t * u < 5 * π / 4 := by
      have hlt : t * u < t * (5 * π / (4 * t)) := mul_lt_mul_of_pos_left hhigh ht
      have h5 : t * (5 * π / (4 * t)) = 5 * π / 4 := by field_simp
      rw [h5] at hlt
      exact hlt
    have hcr : 0 < Real.cos (r * u) := hcosr u (by linarith) (by linarith)
    have hct : Real.cos (t * u) < 0 := by
      have hshift : 0 < Real.cos (t * u - π) := by
        apply Real.cos_pos_of_mem_Ioo
        constructor <;> [linarith; linarith]
      rw [Real.cos_sub_pi] at hshift
      linarith
    refine ⟨?_, hcr⟩
    rw [hwp]
    have hc : 0 < Real.cosh (u / 2) := Real.cosh_pos _
    have hn : 0 < -Real.cos (t * u) := by linarith
    have hprod := mul_pos (mul_pos hc hn) hcr
    linarith [hprod]
  -- the two bumps
  obtain ⟨φ₁, hφ₁d, hφ₁c, hφ₁s, hφ₁n, hφ₁supp, hφ₁pos, hφ₁c₀⟩ := exists_bump_localized c₁ hRpos
  obtain ⟨φ₂, hφ₂d, hφ₂c, hφ₂s, hφ₂n, hφ₂supp, hφ₂pos, hφ₂c₀⟩ := exists_bump_localized c₂ hRpos
  set g₁ : ℝ → ℝ := symmetrize φ₁ with hg₁
  set g₂ : ℝ → ℝ := symmetrize φ₂ with hg₂
  have hg₁c : Continuous g₁ := symmetrize_continuous hφ₁c
  have hg₂c : Continuous g₂ := symmetrize_continuous hφ₂c
  have hg₁s : HasCompactSupport g₁ := symmetrize_hasCompactSupport hφ₁s
  have hg₂s : HasCompactSupport g₂ := symmetrize_hasCompactSupport hφ₂s
  have hg₁n : ∀ u, 0 ≤ g₁ u := by
    intro u; rw [hg₁]; exact add_nonneg (hφ₁n u) (hφ₁n (-u))
  have hg₂n : ∀ u, 0 ≤ g₂ u := by
    intro u; rw [hg₂]; exact add_nonneg (hφ₂n u) (hφ₂n (-u))
  -- support localisation of the symmetrised bumps
  have hsym_supp : ∀ (φ : ℝ → ℝ) (c : ℝ), (∀ u, 0 ≤ φ u) → (∀ u, φ u ≠ 0 → |u - c| < R) →
      0 < c - R → ∀ u, symmetrize φ u ≠ 0 → |u| < c + R := by
    intro φ c hn hsupp hcR u hu
    have hcases : φ u ≠ 0 ∨ φ (-u) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hu
      show φ u + φ (-u) = 0
      rw [hcon.1, hcon.2]; ring
    rcases hcases with h | h
    · have hb := hsupp u h
      rw [abs_lt] at hb ⊢
      constructor <;> linarith
    · have hb := hsupp (-u) h
      rw [abs_lt] at hb ⊢
      constructor <;> linarith
  have hg₁supp : ∀ u, g₁ u ≠ 0 → |u| < c₁ + R := by
    intro u hu
    exact hsym_supp φ₁ c₁ hφ₁n hφ₁supp (by linarith) u hu
  have hg₂supp : ∀ u, g₂ u ≠ 0 → |u| < c₂ + R := hsym_supp φ₂ c₂ hφ₂n hφ₂supp hc₂R
  have hP₁ : 0 < poleEvenResp g₁ t r := by
    have heq : poleEvenResp g₁ t r = 2 * ∫ u : ℝ, φ₁ u * wp u := by
      rw [poleEvenResp]
      exact integral_symmetrize hφ₁c hφ₁s hwpc hwpe
    have := hφ₁pos wp hwpc (fun u hu => (hwin₁ u hu).1)
    rw [heq]; linarith
  have hQ₁ : ∀ a : ℝ, 0 < evenResp g₁ a r := by
    intro a
    have heq : evenResp g₁ a r = 2 * ∫ u : ℝ, φ₁ u * wt a u := by
      rw [evenResp]
      exact integral_symmetrize hφ₁c hφ₁s (hwtc a) (hwte a)
    have := hφ₁pos (wt a) (hwtc a) (fun u hu => hwtpos a u (hwin₁ u hu).2)
    rw [heq]; linarith
  have hP₂ : poleEvenResp g₂ t r < 0 := by
    have heq : poleEvenResp g₂ t r = 2 * ∫ u : ℝ, φ₂ u * wp u := by
      rw [poleEvenResp]
      exact integral_symmetrize hφ₂c hφ₂s hwpc hwpe
    have hneg := hφ₂pos (fun u => -wp u) (by fun_prop) (fun u hu => (hwin₂ u hu).1)
    have hlt : ∫ u : ℝ, φ₂ u * wp u < 0 := by
      have hrw : (fun u : ℝ => φ₂ u * -wp u) = fun u : ℝ => -(φ₂ u * wp u) := by
        funext u; ring
      rw [hrw, integral_neg] at hneg
      linarith
    rw [heq]; linarith
  have hQ₂ : ∀ a : ℝ, 0 < evenResp g₂ a r := by
    intro a
    have heq : evenResp g₂ a r = 2 * ∫ u : ℝ, φ₂ u * wt a u := by
      rw [evenResp]
      exact integral_symmetrize hφ₂c hφ₂s (hwtc a) (hwte a)
    have := hφ₂pos (wt a) (hwtc a) (fun u hu => hwtpos a u (hwin₂ u hu).2)
    rw [heq]; linarith
  set lam : ℝ := -poleEvenResp g₂ t r / poleEvenResp g₁ t r with hlam
  have hlampos : 0 < lam := by
    rw [hlam]
    exact div_pos (by linarith) hP₁
  refine ⟨fun u => g₂ u + lam * g₁ u, r, ?_, ?_, ?_, hrpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (symmetrize_contDiff hφ₂d).add (contDiff_const.mul (symmetrize_contDiff hφ₁d))
  · have hsc : HasCompactSupport (fun u : ℝ => lam * g₁ u) := hg₁s.mul_left
    exact hg₂s.add hsc
  · intro u
    show g₂ (-u) + lam * g₁ (-u) = g₂ u + lam * g₁ u
    rw [hg₁, hg₂, symmetrize_even, symmetrize_even]
  · intro u
    have h₁ : 0 ≤ lam * g₁ u := mul_nonneg hlampos.le (hg₁n u)
    have h₂ := hg₂n u
    show 0 ≤ g₂ u + lam * g₁ u
    linarith
  · intro u hu
    have hcases : g₂ u ≠ 0 ∨ g₁ u ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hu
      show g₂ u + lam * g₁ u = 0
      rw [hcon.1, hcon.2]; ring
    have habs : |u| < c₁ + R := by
      rcases hcases with h | h
      · have := hg₂supp u h; linarith
      · exact hg₁supp u h
    have hkey : 2 * r * |u| < 2 * r * (c₁ + R) := by
      apply mul_lt_mul_of_pos_left habs (by positivity)
    have hval : 2 * r * (c₁ + R) = 9 * π / 32 := by
      rw [hr, hc₁, hRdef]; field_simp; ring
    rw [hval] at hkey
    linarith
  · refine ⟨c₁, c₂, ?_, ?_, ?_⟩
    · have h1 : 0 < g₁ c₁ := by
        rw [hg₁]
        show 0 < φ₁ c₁ + φ₁ (-c₁)
        linarith [hφ₁c₀, hφ₁n (-c₁)]
      have h2 := hg₂n c₁
      have h3 : 0 < lam * g₁ c₁ := mul_pos hlampos h1
      show 0 < g₂ c₁ + lam * g₁ c₁
      linarith
    · have h1 : 0 < g₂ c₂ := by
        rw [hg₂]
        show 0 < φ₂ c₂ + φ₂ (-c₂)
        linarith [hφ₂c₀, hφ₂n (-c₂)]
      have h2 : 0 ≤ lam * g₁ c₂ := mul_nonneg hlampos.le (hg₁n c₂)
      show 0 < g₂ c₂ + lam * g₁ c₂
      linarith
    · rw [abs_of_pos (by linarith : (0:ℝ) < c₁), abs_of_pos hc₂pos]
      exact ne_of_gt hc₂lt
  · rw [poleEvenResp_add_smul hg₂c hg₂s hg₁c hg₁s, hlam]
    field_simp
    ring
  · intro a
    rw [evenResp_add_smul hg₂c hg₂s hg₁c hg₁s]
    have h1 := hQ₂ a
    have h2 : 0 < lam * evenResp g₁ a r := mul_pos hlampos (hQ₁ a)
    linarith
  · intro u hu
    have hcases : g₂ u ≠ 0 ∨ g₁ u ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hu
      show g₂ u + lam * g₁ u = 0
      rw [hcon.1, hcon.2]; ring
    have habs : |u| < c₁ + R := by
      rcases hcases with h | h
      · have := hg₂supp u h; linarith
      · exact hg₁supp u h
    have hval : c₁ + R = 9 * π / (4 * t) := by
      rw [hc₁, hRdef]; field_simp; ring
    linarith [hval ▸ habs]

/-- **The explicit even-channel taper**, for a positive ordinate: the special case
of `exists_positive_taper_poleEven_zero_pos` used by the earlier development. -/
theorem exists_taper_poleEven_zero_evenResp_ne_zero_pos {a t : ℝ} (ht : 0 < t) :
    ∃ (g : ℝ → ℝ) (r : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ poleEvenResp g t r = 0 ∧ evenResp g a r ≠ 0 := by
  obtain ⟨g, r, h1, h2, h3, h4, -, -, -, h5, h6, -⟩ := exists_positive_taper_poleEven_zero_pos ht
  exact ⟨g, r, h1, h2, h3, h4, h5, (h6 a).ne'⟩


/-- The strengthened positive construction, for an arbitrary nonzero ordinate. -/
theorem exists_positive_taper_poleEven_zero {t : ℝ} (ht : t ≠ 0) :
    ∃ (g : ℝ → ℝ) (r : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ (∀ u, 0 ≤ g u)
      ∧ (∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
      ∧ (∃ u v : ℝ, 0 < g u ∧ 0 < g v ∧ |u| ≠ |v|)
      ∧ poleEvenResp g t r = 0
      ∧ (∀ a : ℝ, 0 < evenResp g a r)
      ∧ (∀ u, g u ≠ 0 → |u| < 9 * π / (4 * |t|)) := by
  obtain ⟨g, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    exists_positive_taper_poleEven_zero_pos (t := |t|) (abs_pos.mpr ht)
  refine ⟨g, r, h1, h2, h3, h4, h5, h6, h7, ?_, h9, h10⟩
  rcases abs_cases t with ⟨he, -⟩ | ⟨he, -⟩
  · rwa [← he]
  · have hneg : t = -|t| := by rw [he]; ring
    rw [hneg, poleEvenResp_neg_ordinate, h8]

/-- The construction for an arbitrary nonzero ordinate and an arbitrary height. -/
theorem exists_taper_poleEven_zero_evenResp_ne_zero {a t : ℝ} (ht : t ≠ 0) :
    ∃ (g : ℝ → ℝ) (r : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ poleEvenResp g t r = 0 ∧ evenResp g a r ≠ 0 := by
  obtain ⟨g, r, h1, h2, h3, h4, h5, h6⟩ :=
    exists_taper_poleEven_zero_evenResp_ne_zero_pos (a := a) (t := |t|) (abs_pos.mpr ht)
  refine ⟨g, r, h1, h2, h3, h4, ?_, h6⟩
  rcases abs_cases t with ⟨he, -⟩ | ⟨he, -⟩
  · rwa [← he]
  · have hneg : t = -|t| := by rw [he]; ring
    rw [hneg, poleEvenResp_neg_ordinate, h5]

/-! ## Transversality of the even pattern -/

theorem smul_evenPattern (c x y : ℝ) : c • evenPattern x y = evenPattern (c * x) (c * y) := by
  funext i
  fin_cases i <;> rfl

/-- **A vanishing even pole response makes every nonzero multiple of the even
target pattern transverse to the pole space.** -/
theorem evenPattern_quotient_ne_zero_of_poleEven_zero {g : ℝ → ℝ} {a t r c : ℝ}
    (hpole : poleEvenResp g t r = 0) (hA : evenResp g a r ≠ 0) (hc : c ≠ 0) :
    qcls g t r (evenPattern (c * evenResp g a r) (c * evenResp g a (2 * r))) ≠ 0 := by
  intro hzero
  rw [qcls_eq_zero_iff, poleSpace, Submodule.mem_span_pair] at hzero
  obtain ⟨c₁, c₂, hc'⟩ := hzero
  have e0 := congrFun hc' 0
  have e1 := congrFun hc' 1
  simp only [evenPattern, oddPattern, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
  rw [hpole] at e0 e1
  exact hA (by
    have hz : c * evenResp g a r = 0 := by linarith
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h hc
    · exact h)

/-! ## The reflection pair -/

/-- The remaining zeros, with both the target and its partner removed. -/
def restZerosTerm (k : ℝ → ℂ) (ρstar ρ' : Zeros) : ℂ :=
  ∑' ρ : Zeros, if ρ = ρ' then 0 else (if ρ = ρstar then 0 else zeroTerm k ρ)

/-- The four-sample vector of the remaining zeros. -/
def restVec (kFam : Fin 4 → ℝ → ℂ) (ρstar ρ' : Zeros) : Fin 4 → ℝ :=
  fun i => reim (restZerosTerm (kFam i) ρstar ρ')

theorem otherVec_split (kFam : Fin 4 → ℝ → ℂ) (hk : ∀ i, ContDiff ℝ 2 (kFam i))
    (hkc : ∀ i, HasCompactSupport (kFam i)) (ρstar ρ' : Zeros) (hne : ρ' ≠ ρstar) :
    otherVec kFam ρstar = targetVec kFam ρ' + restVec kFam ρstar ρ' := by
  funext i
  show reim (otherZerosTerm (kFam i) ρstar) = _
  rw [otherZerosTerm_split_at_partner (hk i) (hkc i) ρstar ρ' hne, reim_add]
  rfl

/-- **The pair contribution is purely even, for every height.**  This is the
structural limitation of the four-sample parity geometry: pairing a zero with its
functional-equation partner leaves an even vector whether or not the zero is on
the critical line. -/
theorem reflectionPair_parity_blindness (g : ℝ → ℝ) (a r : ℝ) (m : ℝ) :
    m • targetParityVec g a r + m • targetParityVec g (-a) r
      = evenPattern (m * (2 * evenResp g a r)) (m * (2 * evenResp g a (2 * r))) := by
  rw [← smul_add, targetParityVec_add_reflect, smul_evenPattern]

/-! ## The capstone -/

/-- **`literalWeilOffLineReflectionPairTransverse`.**  For an actual nontrivial
zero `ρ* = 1/2 + a + it` of `riemannZeta` off the critical line and with nonzero
ordinate, there are an even `C²` compactly supported taper, a positive sample
radius and the functional-equation partner `ρ'` such that the literal zeta Weil
explicit formula supplies a four-sample balance relation in which the *whole
reflection pair* is split off, the pole part is killed exactly by the parity
quotient, the pair class equals minus the class of everything else, and

  `Q_rest + Q_prime + Q_Γ ≠ 0`,

where `Q_rest` excludes both the target zero and its partner.  Nothing is assumed:
the balance relation comes from the explicit formula, the splitting from the
summability it provides, and the transversality from the explicit taper. -/
theorem literalWeilOffLineReflectionPairTransverse {ρstar : Zeros} {a t : ℝ}
    (hre : (ρstar : ℂ).re = 1 / 2 + a) (him : (ρstar : ℂ).im = t)
    (ha : a ≠ 0) (ht : t ≠ 0) :
    ∃ (g : ℝ → ℝ) (r : ℝ) (ρ' : Zeros),
      ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u) ∧ 0 < r
      ∧ ρ' ≠ ρstar ∧ (ρ' : ℂ).re = 1 / 2 + -a ∧ (ρ' : ℂ).im = t
      ∧ (((Zeta23.zetaZeroConfig).mult ρstar : ℝ) • targetParityVec g a r
          + ((Zeta23.zetaZeroConfig).mult ρ' : ℝ) • targetParityVec g (-a) r
          + restVec (sampleFam g t r) ρstar ρ' + primeVec (sampleFam g t r)
          + gammaVec (sampleFam g t r) + poleVec (sampleFam g t r) = 0)
      ∧ qcls g t r (poleVec (sampleFam g t r)) = 0
      ∧ qcls g t r (restVec (sampleFam g t r) ρstar ρ' + primeVec (sampleFam g t r)
          + gammaVec (sampleFam g t r)) ≠ 0 := by
  obtain ⟨g, r, hgs, hgc, heven, hrpos, hpole, hA⟩ :=
    exists_taper_poleEven_zero_evenResp_ne_zero (a := a) ht
  have hcont : Continuous g := hgs.continuous
  -- the partner
  set ρ' : Zeros := reflectZero ρstar with hρ'
  have hne : ρ' ≠ ρstar := by
    intro hcontra
    have hval : ((ρ' : Zeros) : ℂ) = (ρstar : ℂ) := by rw [hcontra]
    have h1 : (1 : ℝ) - (ρstar : ℂ).re = (ρstar : ℂ).re := by
      rw [← Zeta23.reflect_re]
      exact congrArg Complex.re hval
    rw [hre] at h1
    exact ha (by linarith)
  have hre' : (ρ' : ℂ).re = 1 / 2 + -a := by
    show (Zeta23.reflect (ρstar : ℂ)).re = 1 / 2 + -a
    rw [Zeta23.reflect_re, hre]; ring
  have him' : (ρ' : ℂ).im = t := by
    show (Zeta23.reflect (ρstar : ℂ)).im = t
    rw [Zeta23.reflect_im, him]
  have hmulteq : (Zeta23.zetaZeroConfig).mult ρ' = (Zeta23.zetaZeroConfig).mult ρstar :=
    reflectZero_mult ρstar
  -- the balance, with the pair split off
  obtain ⟨hbal, hmem⟩ := literalWeilFourSampleParityBalance hgs hgc heven hre him r
  have hsplit : otherVec (sampleFam g t r) ρstar
      = targetVec (sampleFam g t r) ρ' + restVec (sampleFam g t r) ρstar ρ' :=
    otherVec_split _ (fun i => sampleFam_contDiff hgs t r i)
      (fun i => sampleFam_hasCompactSupport hgc t r i) ρstar ρ' hne
  have hpartner : targetVec (sampleFam g t r) ρ'
      = ((Zeta23.zetaZeroConfig).mult ρ' : ℝ) • targetParityVec g (-a) r :=
    literalWeilParityCoordinateIdentification hcont hgc heven hre' him' r
  rw [hsplit, hpartner] at hbal
  have hbal' : ((Zeta23.zetaZeroConfig).mult ρstar : ℝ) • targetParityVec g a r
      + ((Zeta23.zetaZeroConfig).mult ρ' : ℝ) • targetParityVec g (-a) r
      + restVec (sampleFam g t r) ρstar ρ' + primeVec (sampleFam g t r)
      + gammaVec (sampleFam g t r) + poleVec (sampleFam g t r) = 0 := by
    rw [← hbal]; abel
  -- the pair vector is a nonzero multiple of the even pattern
  have hmultpos : 1 ≤ (Zeta23.zetaZeroConfig).mult ρstar :=
    (Zeta23.zetaZeroConfig).one_le_mult (ρstar : ℂ) ρstar.2
  have hm : ((Zeta23.zetaZeroConfig).mult ρstar : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((Zeta23.zetaZeroConfig).mult ρstar : ℝ) := by exact_mod_cast hmultpos
    linarith
  set m : ℝ := ((Zeta23.zetaZeroConfig).mult ρstar : ℝ) with hmdef
  have hpair : m • targetParityVec g a r
      + ((Zeta23.zetaZeroConfig).mult ρ' : ℝ) • targetParityVec g (-a) r
      = evenPattern (2 * m * evenResp g a r) (2 * m * evenResp g a (2 * r)) := by
    have hswap : ∀ x : ℝ, m * (2 * x) = 2 * m * x := fun x => by ring
    rw [hmulteq, ← hmdef, reflectionPair_parity_blindness g a r m, hswap, hswap]
  have hpairne : qcls g t r (m • targetParityVec g a r
      + ((Zeta23.zetaZeroConfig).mult ρ' : ℝ) • targetParityVec g (-a) r) ≠ 0 := by
    rw [hpair]
    exact evenPattern_quotient_ne_zero_of_poleEven_zero hpole hA (by
      intro hzero
      rcases mul_eq_zero.mp hzero with h | h
      · norm_num at h
      · exact hm h)
  obtain ⟨h1, _, h3⟩ := parityQuotientBalance (vTarget := m • targetParityVec g a r
      + ((Zeta23.zetaZeroConfig).mult ρ' : ℝ) • targetParityVec g (-a) r)
    (vOther := restVec (sampleFam g t r) ρstar ρ')
    (vPrime := primeVec (sampleFam g t r)) (vGamma := gammaVec (sampleFam g t r))
    hmem (by rw [← hbal'])
  exact ⟨g, r, ρ', hgs, hgc, heven, hrpos, hne, hre', him', hbal', h1, h3 hpairne⟩

end LiteralWeilEvenChannelTaper
end Zeta23Bridge
