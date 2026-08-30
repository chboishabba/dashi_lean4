/-
Transverse (α²) coercivity of the complex bilinear extension of a real even
taper with a plateau.

The route audited in `RIEMANN_LITERAL_AUDIT.md` needs, for a hypothetical
off-line zero at transverse offset `α`, a strictly positive *excess*

  Φ(-2iα) - Φ(0)  =  ∫ φ(u)² (cosh (2αu) - 1) du,

together with an explicit quadratic-in-α lower bound coming from the plateau of
the taper.  This file proves both, at literal analytic strength:

* `PhiExt_ofReal_neg_two_mul_I` evaluates the complex extension of a real taper
  at the purely imaginary point `-2iα`;
* `PhiExt_excess_eq_taperExcess` identifies `Φ(-2iα) - Φ(0)` with the real
  integral `taperExcess`, for a real *even* compactly supported taper;
* `taperExcess_nonneg`, `taperExcess_ge_plateau_quadratic` and
  `taperExcess_pos_iff` give the sign, the explicit floor `(4/3)a³α²` produced
  by a plateau of half-width `a`, and the exact vanishing criterion;
* `transverseDefect_lower_source_regime` specialises the floor to the source
  regime `a ≥ 3L/8` (i.e. `a = L/2 - w` with `8w ≤ L`), giving the literal
  bound `D_L(α) = L·excess ≥ (9/128)·L⁴·α²`.

Nothing here is schematic: `φ` is an arbitrary continuous, even, compactly
supported real function with a plateau, and every constant is explicit.
-/
import RiemannAnalytic.PoissonExtension

namespace RiemannAnalytic

open MeasureTheory Complex intervalIntegral

/-! ### An elementary hyperbolic inequality -/

/-- `cosh x - 1 ≥ x²/2`. -/
theorem cosh_sub_one_ge_sq_div_two (x : ℝ) : x ^ 2 / 2 ≤ Real.cosh x - 1 := by
  have h : Real.cosh x = 1 + 2 * Real.sinh (x / 2) ^ 2 := by
    have h1 := Real.cosh_two_mul (x / 2)
    have hs := Real.cosh_sq (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h1
    rw [h1, hs]; ring
  have hk : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 := by
    rcases le_or_gt 0 (x / 2) with hx | hx
    · have := Real.self_le_sinh_iff.2 hx
      nlinarith
    · have h2 := Real.sinh_le_self_iff.2 hx.le
      nlinarith [Real.sinh_neg_iff.2 hx]
  rw [h]; nlinarith

/-! ### Compactly supported tapers -/

/-- A *compact taper of radius `R`*: a continuous real function vanishing
outside `[-R, R]`.  This is the shape of the Alpöge--Furman taper (support
`[-L/2, L/2]`). -/
structure CompactTaper (φ : ℝ → ℝ) (R : ℝ) : Prop where
  cont : Continuous φ
  supp : ∀ t, R < |t| → φ t = 0

/-- The product of the squared taper with any continuous function is
integrable. -/
theorem CompactTaper.integrable_sq_mul {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun u => φ u ^ 2 * g u) := by
  refine ((hφ.cont.pow 2).mul hg).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc ?_
  intro x hx
  have hR : R < |x| := by
    rcases lt_or_ge R |x| with h | h
    · exact h
    · exact absurd (Set.mem_Icc.2 ⟨by cases abs_le.1 h with | intro h1 _ => linarith,
        by cases abs_le.1 h with | intro _ h2 => linarith⟩) hx
  simp [hφ.supp x hR]

/-- Integrability of the squared taper itself. -/
theorem CompactTaper.integrable_sq {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R) :
    Integrable (fun u => φ u ^ 2) := by
  simpa using hφ.integrable_sq_mul (g := fun _ : ℝ => (1 : ℝ)) continuous_const

/-! ### Evaluating the complex extension at purely imaginary points -/

/-- At the origin the complex extension is the total mass. -/
theorem PhiExt_zero (ψ : ℝ → ℝ) : PhiExt ψ 0 = ((∫ t : ℝ, ψ t : ℝ) : ℂ) := by
  unfold PhiExt
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp

/-- At the purely imaginary point `-2iα` the complex extension of a real taper
is the real integral `∫ ψ(t) e^{-2αt} dt`. -/
theorem PhiExt_ofReal_neg_two_mul_I (ψ : ℝ → ℝ) (α : ℝ) :
    PhiExt ψ (-(2 * α : ℝ) * Complex.I)
      = ((∫ t : ℝ, ψ t * Real.exp (-(2 * α * t)) : ℝ) : ℂ) := by
  unfold PhiExt
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have harg : -(Complex.I * (-(2 * α : ℝ) * Complex.I) * (t : ℂ))
      = ((-(2 * α * t) : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  show ((ψ t : ℝ) : ℂ) * Complex.exp (-(Complex.I * (-(2 * α : ℝ) * Complex.I) * (t : ℂ)))
      = ((ψ t * Real.exp (-(2 * α * t)) : ℝ) : ℂ)
  rw [harg, ← Complex.ofReal_exp, ← Complex.ofReal_mul]

/-- For an *even* taper the two one-sided exponential moments agree. -/
theorem integral_even_mul_exp_symm (ψ : ℝ → ℝ) (hψ : ∀ t, ψ (-t) = ψ t) (α : ℝ) :
    ∫ t : ℝ, ψ t * Real.exp (-(2 * α * t)) = ∫ t : ℝ, ψ t * Real.exp (2 * α * t) := by
  have h := integral_neg_eq_self (fun t : ℝ => ψ t * Real.exp (2 * α * t)) volume
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show ψ t * Real.exp (-(2 * α * t)) = ψ (-t) * Real.exp (2 * α * -t)
  rw [hψ t]
  congr 1
  ring_nf

/-- Consequently the exponential moment of an even taper is a `cosh` moment. -/
theorem integral_even_mul_exp_eq_cosh {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R)
    (hev : ∀ t, φ (-t) = φ t) (α : ℝ) :
    ∫ t : ℝ, φ t ^ 2 * Real.exp (-(2 * α * t))
      = ∫ t : ℝ, φ t ^ 2 * Real.cosh (2 * α * t) := by
  have hsq_ev : ∀ t : ℝ, φ (-t) ^ 2 = φ t ^ 2 := fun t => by rw [hev t]
  have hsymm := integral_even_mul_exp_symm (fun t => φ t ^ 2) hsq_ev α
  have hint₁ : Integrable fun t : ℝ => φ t ^ 2 * Real.exp (-(2 * α * t)) :=
    hφ.integrable_sq_mul (by fun_prop)
  have hint₂ : Integrable fun t : ℝ => φ t ^ 2 * Real.exp (2 * α * t) :=
    hφ.integrable_sq_mul (by fun_prop)
  have hcosh : ∀ t : ℝ, φ t ^ 2 * Real.cosh (2 * α * t)
      = (φ t ^ 2 * Real.exp (2 * α * t) + φ t ^ 2 * Real.exp (-(2 * α * t))) / 2 := by
    intro t
    rw [Real.cosh_eq]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hcosh), MeasureTheory.integral_div,
    integral_add hint₂ hint₁, ← hsymm]
  ring

/-! ### The transverse excess -/

/-- The *transverse excess* of a taper at offset `α`:
`∫ φ(u)² (cosh (2αu) - 1) du`.  This is the quantity `Φ(-2iα) - Φ(0)`. -/
noncomputable def taperExcess (φ : ℝ → ℝ) (α : ℝ) : ℝ :=
  ∫ u : ℝ, φ u ^ 2 * (Real.cosh (2 * α * u) - 1)

/-- **The complex extension excess is the real transverse excess.**  For a real
even compactly supported taper,
`Φ_{φ²}(-2iα) - Φ_{φ²}(0) = ∫ φ(u)² (cosh(2αu) - 1) du`. -/
theorem PhiExt_excess_eq_taperExcess {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R)
    (hev : ∀ t, φ (-t) = φ t) (α : ℝ) :
    PhiExt (fun t => φ t ^ 2) (-(2 * α : ℝ) * Complex.I)
        - PhiExt (fun t => φ t ^ 2) 0
      = ((taperExcess φ α : ℝ) : ℂ) := by
  have hint₁ : Integrable fun t : ℝ => φ t ^ 2 * Real.cosh (2 * α * t) :=
    hφ.integrable_sq_mul (by fun_prop)
  have hsplit : taperExcess φ α
      = (∫ t : ℝ, φ t ^ 2 * Real.cosh (2 * α * t)) - ∫ t : ℝ, φ t ^ 2 := by
    unfold taperExcess
    rw [← integral_sub hint₁ hφ.integrable_sq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    ring
  rw [PhiExt_ofReal_neg_two_mul_I, PhiExt_zero,
    integral_even_mul_exp_eq_cosh hφ hev α, hsplit]
  push_cast
  ring

/-- The transverse excess is nonnegative. -/
theorem taperExcess_nonneg (φ : ℝ → ℝ) (α : ℝ) : 0 ≤ taperExcess φ α := by
  refine integral_nonneg fun u => ?_
  have h := Real.one_le_cosh (2 * α * u)
  have hnn : (0 : ℝ) ≤ Real.cosh (2 * α * u) - 1 := by linarith
  exact mul_nonneg (sq_nonneg _) hnn

/-- The excess vanishes at `α = 0`. -/
theorem taperExcess_zero (φ : ℝ → ℝ) : taperExcess φ 0 = 0 := by
  simp [taperExcess]

/-- **Plateau floor.**  If the taper equals `1` on `[-a, a]` with `a ≥ 0`, the
transverse excess is at least `(4/3)a³α²`. -/
theorem taperExcess_ge_plateau_quadratic {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R)
    {a : ℝ} (ha : 0 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) :
    4 / 3 * a ^ 3 * α ^ 2 ≤ taperExcess φ α := by
  set f : ℝ → ℝ := fun u => φ u ^ 2 * (Real.cosh (2 * α * u) - 1) with hf
  have hfint : Integrable f := hφ.integrable_sq_mul (by fun_prop)
  have hfnn : ∀ u, 0 ≤ f u := by
    intro u
    have h := Real.one_le_cosh (2 * α * u)
    have : (0 : ℝ) ≤ φ u ^ 2 := sq_nonneg _
    have : (0 : ℝ) ≤ Real.cosh (2 * α * u) - 1 := by linarith
    exact mul_nonneg (sq_nonneg _) this
  -- restrict to the plateau
  have hrestrict : ∫ u in Set.Icc (-a) a, f u ≤ taperExcess φ α := by
    have := setIntegral_le_integral (s := Set.Icc (-a) a) hfint
      (Filter.Eventually.of_forall hfnn)
    simpa [taperExcess, hf] using this
  -- on the plateau the integrand dominates the quadratic
  set g : ℝ → ℝ := fun u => 2 * α ^ 2 * u ^ 2 with hg
  have hgint : IntegrableOn g (Set.Icc (-a) a) :=
    (by fun_prop : Continuous g).continuousOn.integrableOn_compact isCompact_Icc
  have hfintOn : IntegrableOn f (Set.Icc (-a) a) := hfint.integrableOn
  have hmono : ∫ u in Set.Icc (-a) a, g u ≤ ∫ u in Set.Icc (-a) a, f u := by
    refine setIntegral_mono_on hgint hfintOn measurableSet_Icc fun u hu => ?_
    have hu' : |u| ≤ a := abs_le.2 ⟨(Set.mem_Icc.1 hu).1, (Set.mem_Icc.1 hu).2⟩
    have hφ1 : φ u = 1 := hplat u hu'
    have hcosh := cosh_sub_one_ge_sq_div_two (2 * α * u)
    simp only [hf, hg, hφ1]
    nlinarith
  -- evaluate the quadratic integral
  have hval : ∫ u in Set.Icc (-a) a, g u = 4 / 3 * a ^ 3 * α ^ 2 := by
    have hle : (-a : ℝ) ≤ a := by linarith
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    have : ∫ u in (-a)..a, g u = 2 * α ^ 2 * ∫ u in (-a)..a, u ^ 2 := by
      simp [hg, intervalIntegral.integral_const_mul]
    rw [this, integral_pow]
    push_cast
    ring
  linarith [hrestrict, hmono, hval.symm.le, hval.le]

/-- **Exact vanishing criterion.**  For a taper with a plateau of positive
half-width the transverse excess vanishes exactly at `α = 0`. -/
theorem taperExcess_pos_iff {φ : ℝ → ℝ} {R : ℝ} (hφ : CompactTaper φ R)
    {a : ℝ} (ha : 0 < a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) :
    0 < taperExcess φ α ↔ α ≠ 0 := by
  constructor
  · intro hpos hα
    rw [hα, taperExcess_zero] at hpos
    exact lt_irrefl _ hpos
  · intro hα
    have h := taperExcess_ge_plateau_quadratic hφ ha.le hplat α
    have hpos : 0 < 4 / 3 * a ^ 3 * α ^ 2 := by
      have : 0 < α ^ 2 := pow_pos (abs_pos.2 hα) 2 |>.trans_le (le_of_eq (by rw [sq_abs]))
      positivity
    linarith

/-- **Literal transverse defect bound in the source regime.**  Write
`D_L(α) = L · (Φ(-2iα) - Φ(0))` for the transverse defect produced by the
external `L` factor of the norm identity.  If the taper has a plateau of
half-width `a ≥ 3L/8` — which is exactly the source condition `a = L/2 - w`
with `8w ≤ L` — then

  `D_L(α) ≥ (9/128) · L⁴ · α²`. -/
theorem transverseDefect_lower_source_regime {φ : ℝ → ℝ} {R L : ℝ}
    (hφ : CompactTaper φ R) (hL : 0 < L) {a : ℝ} (ha : 3 * L / 8 ≤ a)
    (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) :
    9 / 128 * L ^ 4 * α ^ 2 ≤ L * taperExcess φ α := by
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  have hfloor := taperExcess_ge_plateau_quadratic hφ ha0 hplat α
  have hcube : (3 * L / 8) ^ 3 ≤ a ^ 3 := by
    have h0 : (0 : ℝ) ≤ 3 * L / 8 := by positivity
    exact pow_le_pow_left₀ h0 ha 3
  have hα : (0 : ℝ) ≤ α ^ 2 := sq_nonneg _
  have hstep : 4 / 3 * (3 * L / 8) ^ 3 * α ^ 2 ≤ 4 / 3 * a ^ 3 * α ^ 2 := by nlinarith
  have hval : 4 / 3 * (3 * L / 8) ^ 3 = 9 / 128 * L ^ 3 := by ring
  nlinarith [hfloor, hstep, hL.le]

end RiemannAnalytic
