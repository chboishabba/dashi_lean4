/-
**Lane A — the true uniform-in-`α` growth of the window energy bound `Bφ(α,L)`.**

`LocalRouteCapstone.lean` isolated the estimate the bounded-height route would
need on the zero side: an `α`-uniform quadratic bound

    `Bφ(α, L) ≤ Cb · L²`,

which would give `|α| ≤ (128/9)·Cb/L` and hence asymptotic critical-line
localization.  This file answers, adversarially, whether that estimate is true.

**It is false, and quantitatively so.**  The window energy bound contains the
twisted taper mass `taperMass φ α = ∫ |φ| e^{-αu}`, and for a *nonnegative* taper
with a plateau of half-width `a` the pairing of `u` with `-u` that the even
symmetry suggests produces `cosh(αu)`, not cancellation:

* `taperMass_eq_cosh_of_even` — for an even taper,
  `taperMass φ α = ∫ |φ(u)| cosh(α u) du`;  the twist enters through a
  *positive* even weight, so there is nothing to cancel;
* `taperMass_ge_plateau_exp` — hence, unconditionally,
  `(a/2)·e^{|α| a/2} ≤ taperMass φ α`;
* `windowEnergyBound_ge_exp_source` — in the source regime `a ≥ 3L/8`,
  `(9/256)·L²·e^{3|α|L/8} ≤ Bφ(α, L)`.

Two consequences, both proved:

* `abs_offset_le_of_uniform_quadratic_bound` — an `α`-uniform bound
  `Bφ(α,L) ≤ Cb L²` *already implies* `|α| ≤ (8/(3L))·log(256 Cb/9)`, with no
  use of the `L⁶` coercive floor at all.  The hypothesis is therefore not an
  auxiliary estimate feeding the capstone: it is a restatement of the desired
  conclusion, and cannot be assumed for free.
* `no_uniform_quadratic_bound_of_fixed_offset` — for any *fixed* off-line offset
  `α ≠ 0` and any constant `Cb`, every long enough source window violates
  `Bφ(α,L) ≤ Cb L²`.  The obstruction is exactly the `e^{3|α|L/8}` growth.

To make sure these statements are not vacuous, `exists_sourceTaper` constructs,
for every `L > 0`, an actual `C¹`, even, nonnegative taper with plateau
half-width `3L/8` and support in `[-L/2, L/2]` — i.e. the hypotheses used
throughout the source-regime results are satisfiable at every scale.

**Verdict for Lane A: negative.**  The present taper family does not admit an
`α`-uniform quadratic window energy bound; the twisted mass grows like
`e^{|α|L/2}`.  Any localization theorem of the form `|α| = O(1/L)` must come
from a different mechanism — e.g. a taper whose twisted mass is normalized, or
an estimate that does not pass through absolute values — and not from `Bφ`.

Nothing here refers to `ζ`, and nothing is assumed about the zeros.
-/
import RiemannAnalytic.LocalRouteCapstone

namespace RiemannAnalytic

open MeasureTheory Set

/-! ### A lower bound for an integral by a constant on a sub-interval -/

/-- If a nonnegative integrable function is at least `C` on `[c, d]`, its total
integral is at least `C · (d − c)`. -/
theorem integral_ge_const_mul_of_le_on_Icc {g : ℝ → ℝ} (hint : Integrable g)
    (hnn : ∀ u, 0 ≤ g u) {c d C : ℝ} (hcd : c ≤ d) (hC : ∀ u ∈ Set.Icc c d, C ≤ g u) :
    C * (d - c) ≤ ∫ u : ℝ, g u := by
  have hmeas : MeasurableSet (Set.Icc c d) := measurableSet_Icc
  have hvol : (volume (Set.Icc c d)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hIon : IntegrableOn g (Set.Icc c d) volume := hint.integrableOn
  have hlow := setIntegral_ge_of_const_le (μ := volume) (f := g) (c := C) hmeas hvol hC hIon
  have hvolr : (volume.real (Set.Icc c d)) = d - c := by
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  rw [hvolr, smul_eq_mul] at hlow
  have hup : ∫ u in Set.Icc c d, g u ≤ ∫ u : ℝ, g u :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
  linarith

/-! ### Integrability of the twisted taper mass integrand -/

/-- The integrand of `taperMass` is integrable for a `C¹` taper. -/
theorem integrable_taperMass_integrand {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) (α : ℝ) :
    Integrable (fun u : ℝ => |φ u| * Real.exp (-α * u)) := by
  have hcont : Continuous fun u : ℝ => |φ u| * Real.exp (-α * u) := by
    have h1 : Continuous fun u : ℝ => |φ u| := hφ.cont.abs
    have h2 : Continuous fun u : ℝ => Real.exp (-α * u) := by fun_prop
    exact h1.mul h2
  have hsupp : HasCompactSupport fun u : ℝ => |φ u| * Real.exp (-α * u) := by
    refine HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc ?_
    intro x hx
    have hxabs : R < |x| := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2⟩ := abs_le.mp hcon
      exact hx ⟨h1, h2⟩
    rw [hφ.supp x hxabs]
    simp
  exact hcont.integrable_of_hasCompactSupport hsupp

/-! ### The `cosh` form of the twisted taper mass -/

/-- **Evenness produces `cosh`, not cancellation.**  For an even taper the
twisted mass is the integral of `|φ|` against the positive even weight
`cosh(α u)`. -/
theorem taperMass_eq_cosh_of_even {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    (hev : ∀ t, φ (-t) = φ t) (α : ℝ) :
    taperMass φ α = ∫ u : ℝ, |φ u| * Real.cosh (α * u) := by
  have hint := integrable_taperMass_integrand hφ α
  have hint' := integrable_taperMass_integrand hφ (-α)
  have hrefl : ∫ u : ℝ, |φ u| * Real.exp (-α * u) = ∫ u : ℝ, |φ u| * Real.exp (α * u) := by
    have := integral_neg_eq_self (fun u : ℝ => |φ u| * Real.exp (-α * u)) volume
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show |φ (-u)| * Real.exp (-α * -u) = |φ u| * Real.exp (α * u)
    rw [hev u]
    ring_nf
  have hsum : (∫ u : ℝ, |φ u| * Real.exp (-α * u)) + ∫ u : ℝ, |φ u| * Real.exp (α * u)
      = ∫ u : ℝ, (|φ u| * Real.exp (-α * u) + |φ u| * Real.exp (α * u)) := by
    rw [← integral_add hint]
    have : (fun u : ℝ => |φ u| * Real.exp (α * u))
        = fun u : ℝ => |φ u| * Real.exp (-(-α) * u) := by
      funext u; ring_nf
    rw [this]
    exact hint'
  have hcosh : ∫ u : ℝ, (|φ u| * Real.exp (-α * u) + |φ u| * Real.exp (α * u))
      = 2 * ∫ u : ℝ, |φ u| * Real.cosh (α * u) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Real.cosh_eq, neg_mul]
    ring
  unfold taperMass
  rw [← hrefl] at hsum
  have h2 : 2 * ∫ u : ℝ, |φ u| * Real.exp (-α * u)
      = 2 * ∫ u : ℝ, |φ u| * Real.cosh (α * u) := by
    rw [← hcosh, ← hsum]; ring
  linarith

/-! ### The exponential lower bound -/

/-- **The twisted taper mass grows exponentially in `|α| a`.**  For a
nonnegative `C¹` taper equal to `1` on `|t| ≤ a`,

    `(a/2) · e^{|α| a / 2} ≤ taperMass φ α`. -/
theorem taperMass_ge_plateau_exp {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    {a : ℝ} (ha : 0 < a) (hplat : ∀ t, |t| ≤ a → φ t = 1) (α : ℝ) :
    a / 2 * Real.exp (|α| * a / 2) ≤ taperMass φ α := by
  set g : ℝ → ℝ := fun u => |φ u| * Real.exp (-α * u) with hg
  have hint := integrable_taperMass_integrand hφ α
  have hgnn : ∀ u, 0 ≤ g u := fun u => by positivity
  have key : ∀ c d : ℝ, c ≤ d → d - c = a / 2 →
      (∀ u ∈ Set.Icc c d, |u| ≤ a ∧ |α| * a / 2 ≤ -α * u) →
      a / 2 * Real.exp (|α| * a / 2) ≤ taperMass φ α := by
    intro c d hcd hlen hmem
    have hC : ∀ u ∈ Set.Icc c d, Real.exp (|α| * a / 2) ≤ g u := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := hmem u hu
      have hφ1 : |φ u| = 1 := by rw [hplat u hu1]; norm_num
      rw [hg]
      simp only [hφ1, one_mul]
      exact Real.exp_le_exp.2 hu2
    have := integral_ge_const_mul_of_le_on_Icc hint hgnn hcd hC
    rw [hlen] at this
    calc a / 2 * Real.exp (|α| * a / 2) = Real.exp (|α| * a / 2) * (a / 2) := by ring
      _ ≤ ∫ u : ℝ, g u := this
      _ = taperMass φ α := rfl
  rcases le_or_gt 0 α with hα | hα
  · refine key (-a) (-(a / 2)) (by linarith) (by ring) ?_
    intro u hu
    obtain ⟨h1, h2⟩ := hu
    refine ⟨abs_le.2 ⟨h1, by linarith⟩, ?_⟩
    rw [abs_of_nonneg hα]
    nlinarith
  · refine key (a / 2) a (by linarith) (by ring) ?_
    intro u hu
    obtain ⟨h1, h2⟩ := hu
    refine ⟨abs_le.2 ⟨by linarith, h2⟩, ?_⟩
    rw [abs_of_neg hα]
    nlinarith

/-- **The window energy bound grows exponentially in `|α| L`.**  In the source
regime `a ≥ 3L/8`,

    `(9/256) · L² · e^{3|α|L/8} ≤ Bφ(α, L)`. -/
theorem windowEnergyBound_ge_exp_source {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    {L : ℝ} (hL : 0 < L) {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1)
    (α : ℝ) :
    9 / 256 * L ^ 2 * Real.exp (3 * |α| * L / 8) ≤ windowEnergyBound φ L α := by
  have ha0 : 0 < a := by linarith
  have hmass := taperMass_ge_plateau_exp hφ ha0 hplat α
  have hstep : 3 * L / 16 * Real.exp (3 * |α| * L / 16) ≤ taperMass φ α := by
    refine le_trans ?_ hmass
    have hexp : Real.exp (3 * |α| * L / 16) ≤ Real.exp (|α| * a / 2) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith [abs_nonneg α]
    have h2 : 3 * L / 16 ≤ a / 2 := by linarith
    have hpos : (0 : ℝ) < Real.exp (3 * |α| * L / 16) := Real.exp_pos _
    have h3 : (0 : ℝ) ≤ 3 * L / 16 := by positivity
    calc 3 * L / 16 * Real.exp (3 * |α| * L / 16)
        ≤ a / 2 * Real.exp (3 * |α| * L / 16) := by nlinarith
      _ ≤ a / 2 * Real.exp (|α| * a / 2) := by nlinarith [ha, hL]
  have hsq : (3 * L / 16 * Real.exp (3 * |α| * L / 16)) ^ 2 ≤ taperMass φ α ^ 2 := by
    have hnn : (0 : ℝ) ≤ 3 * L / 16 * Real.exp (3 * |α| * L / 16) := by positivity
    nlinarith
  have hexp2 : Real.exp (3 * |α| * L / 16) ^ 2 = Real.exp (3 * |α| * L / 8) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hval : (3 * L / 16 * Real.exp (3 * |α| * L / 16)) ^ 2
      = 9 / 256 * L ^ 2 * Real.exp (3 * |α| * L / 8) := by
    rw [mul_pow, hexp2]
    ring
  unfold windowEnergyBound
  have hrest : (0 : ℝ) ≤ derivMass φ α ^ 2 * L ^ 2 / (2 * Real.pi ^ 2) := by
    have := Real.pi_pos; positivity
  linarith [hval ▸ hsq]

/-! ### The matching upper bound: the growth really is exponential -/

/-- **The twisted taper mass is at most exponential.**  For a taper bounded by
`1` and supported in `[-R, R]`,

    `taperMass φ α ≤ 2R · e^{|α| R}`.

Together with `taperMass_ge_plateau_exp` this pins the growth of the twisted
mass at `e^{Θ(|α| L)}` in the source regime `3L/8 ≤ a`, `2R ≤ L`: the exponential
is the truth, not an artefact of the lower bound. -/
theorem taperMass_le_exp_support {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R) (hR : 0 ≤ R)
    (hb : ∀ t, |φ t| ≤ 1) (α : ℝ) :
    taperMass φ α ≤ 2 * R * Real.exp (|α| * R) := by
  have hint := integrable_taperMass_integrand hφ α
  have hzero : ∀ u ∉ Set.Icc (-R) R, |φ u| * Real.exp (-α * u) = 0 := by
    intro u hu
    have hxabs : R < |u| := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2⟩ := abs_le.mp hcon
      exact hu ⟨h1, h2⟩
    rw [hφ.supp u hxabs]
    simp
  have hset : ∫ u in Set.Icc (-R) R, |φ u| * Real.exp (-α * u)
      = ∫ u : ℝ, |φ u| * Real.exp (-α * u) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  have hbound : ∀ u ∈ Set.Icc (-R) R,
      |φ u| * Real.exp (-α * u) ≤ Real.exp (|α| * R) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hu
    have hexp : Real.exp (-α * u) ≤ Real.exp (|α| * R) := by
      refine Real.exp_le_exp.2 ?_
      have habs : -α * u ≤ |(-α) * u| := le_abs_self _
      have hval : |(-α) * u| = |α| * |u| := by rw [abs_mul, abs_neg]
      have hu' : |u| ≤ R := abs_le.2 ⟨h1, h2⟩
      have : |α| * |u| ≤ |α| * R := by
        exact mul_le_mul_of_nonneg_left hu' (abs_nonneg α)
      rw [hval] at habs
      linarith
    have hφ1 : |φ u| ≤ 1 := hb u
    nlinarith [Real.exp_pos (-α * u), abs_nonneg (φ u), Real.exp_pos (|α| * R)]
  have hmono : ∫ u in Set.Icc (-R) R, |φ u| * Real.exp (-α * u)
      ≤ ∫ _u in Set.Icc (-R) R, Real.exp (|α| * R) := by
    have hvol : volume (Set.Icc (-R) R) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    exact setIntegral_mono_on hint.integrableOn (integrableOn_const (hs := hvol))
      measurableSet_Icc hbound
  have hconst : ∫ _u in Set.Icc (-R) R, Real.exp (|α| * R) = 2 * R * Real.exp (|α| * R) := by
    rw [setIntegral_const, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  unfold taperMass
  rw [← hset]
  calc ∫ u in Set.Icc (-R) R, |φ u| * Real.exp (-α * u)
      ≤ ∫ _u in Set.Icc (-R) R, Real.exp (|α| * R) := hmono
    _ = 2 * R * Real.exp (|α| * R) := hconst

/-! ### Consequence 1: the uniform bound already contains the conclusion -/

/-- **The `α`-uniform quadratic bound is not an auxiliary estimate — it is the
conclusion.**  If `Bφ(α, L) ≤ Cb L²` then, *without any use of the `L⁶` coercive
floor*,

    `|α| ≤ (8/(3L)) · log(256 Cb / 9)`.

So assuming the uniform bound is assuming a localization statement of exactly
the strength one is trying to prove. -/
theorem abs_offset_le_of_uniform_quadratic_bound {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    {L : ℝ} (hL : 0 < L) {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1)
    (α : ℝ) {Cb : ℝ} (hCb : 0 < Cb) (hbound : windowEnergyBound φ L α ≤ Cb * L ^ 2) :
    |α| ≤ 8 / (3 * L) * Real.log (256 * Cb / 9) := by
  have hlow := windowEnergyBound_ge_exp_source hφ hL ha hplat α
  have hL2 : (0 : ℝ) < L ^ 2 := by positivity
  have hexp : Real.exp (3 * |α| * L / 8) ≤ 256 * Cb / 9 := by
    have h1 : 9 / 256 * L ^ 2 * Real.exp (3 * |α| * L / 8) ≤ Cb * L ^ 2 := by linarith
    nlinarith [Real.exp_pos (3 * |α| * L / 8)]
  have hpos : (0 : ℝ) < 256 * Cb / 9 := by positivity
  have hlog : 3 * |α| * L / 8 ≤ Real.log (256 * Cb / 9) := by
    have := Real.log_le_log (Real.exp_pos _) hexp
    rwa [Real.log_exp] at this
  have hfac : (0 : ℝ) < 8 / (3 * L) := by positivity
  calc |α| = 8 / (3 * L) * (3 * |α| * L / 8) := by field_simp
    _ ≤ 8 / (3 * L) * Real.log (256 * Cb / 9) := by
        exact mul_le_mul_of_nonneg_left hlog hfac.le

/-! ### Consequence 2: no uniform bound at a fixed off-line offset -/

/-- **The `α`-uniform quadratic window energy bound is false.**  Fix any
off-line offset `α ≠ 0` and any constant `Cb > 0`.  Then for every long enough
source window — every `L` beyond an explicit threshold — *no* taper satisfying
the source-regime hypotheses obeys `Bφ(α, L) ≤ Cb L²`. -/
theorem no_uniform_quadratic_bound_of_fixed_offset {α : ℝ} (hα : α ≠ 0) {Cb : ℝ} (hCb : 0 < Cb) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ (φ : ℝ → ℝ) (R a : ℝ), C1Taper φ R →
      3 * L / 8 ≤ a → (∀ t, |t| ≤ a → φ t = 1) → Cb * L ^ 2 < windowEnergyBound φ L α := by
  have habs : 0 < |α| := abs_pos.2 hα
  refine ⟨max 1 (8 * |Real.log (256 * Cb / 9)| / (3 * |α|) + 1), by positivity, ?_⟩
  intro L hL φ R a hφ ha hplat
  have hL1 : (1 : ℝ) ≤ L := le_trans (le_max_left _ _) hL
  have hL0 : (0 : ℝ) < L := by linarith
  by_contra hcon
  push_neg at hcon
  have hkey := abs_offset_le_of_uniform_quadratic_bound hφ hL0 ha hplat α hCb hcon
  have hbig : 8 * |Real.log (256 * Cb / 9)| / (3 * |α|) + 1 ≤ L := le_trans (le_max_right _ _) hL
  have hlog : Real.log (256 * Cb / 9) ≤ |Real.log (256 * Cb / 9)| := le_abs_self _
  have h1 : |α| * (3 * L) ≤ 8 * Real.log (256 * Cb / 9) := by
    have h2 : 0 < 3 * L := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ h2] at hkey
    linarith [hkey]
  have h3 : 8 * |Real.log (256 * Cb / 9)| < |α| * (3 * L) := by
    have h4 : 8 * |Real.log (256 * Cb / 9)| / (3 * |α|) * (3 * |α|)
        = 8 * |Real.log (256 * Cb / 9)| := by
      field_simp
    nlinarith [habs, hbig]
  linarith

/-! ### Consequence 3: the taper-only constraint is vacuous beyond radius `18/L` -/

/-- **The zero-side self-constraint carries no information about offsets larger
than `18/L`.**  The capstone inequality `(81/16384) L⁶ α² ≤ Bφ(α,L)²` needs the
window, plateau and lattice-tail hypotheses to be proved; but once `|α| L ≥ 18`
it holds *outright*, from the exponential lower bound for `Bφ` alone.  So no
choice of arithmetic-free upper bound for `Bφ` can exclude such an offset: the
best conceivable outcome of the taper-only route is a tube of radius of order
`1/L`, and the `α`-uniform quadratic bound that would deliver it is false
(`no_uniform_quadratic_bound_of_fixed_offset`). -/
theorem source_constraint_vacuous_of_large_offset {φ : ℝ → ℝ} {R : ℝ} (hφ : C1Taper φ R)
    {L : ℝ} (hL : 0 < L) {a : ℝ} (ha : 3 * L / 8 ≤ a) (hplat : ∀ t, |t| ≤ a → φ t = 1)
    (α : ℝ) (hbig : 18 ≤ |α| * L) :
    81 / 16384 * L ^ 6 * α ^ 2 ≤ windowEnergyBound φ L α ^ 2 := by
  set x : ℝ := |α| * L with hx
  have hx18 : 18 ≤ x := hbig
  have hx0 : (0 : ℝ) < x := by linarith
  have hx2 : x ^ 2 = α ^ 2 * L ^ 2 := by rw [hx, mul_pow, sq_abs]
  have hlow := windowEnergyBound_ge_exp_source hφ hL ha hplat α
  have hYnn : (0 : ℝ) ≤ 9 / 256 * L ^ 2 * Real.exp (3 * |α| * L / 8) := by positivity
  have hsq : (9 / 256 * L ^ 2 * Real.exp (3 * |α| * L / 8)) ^ 2
      ≤ windowEnergyBound φ L α ^ 2 := by nlinarith [windowEnergyBound_nonneg φ L α]
  have hexpsq : Real.exp (3 * |α| * L / 8) ^ 2 = Real.exp (3 * x / 4) := by
    rw [sq, ← Real.exp_add, hx]
    ring_nf
  have hval : (9 / 256 * L ^ 2 * Real.exp (3 * |α| * L / 8)) ^ 2
      = 81 / 65536 * L ^ 4 * Real.exp (3 * x / 4) := by
    rw [mul_pow, hexpsq]
    ring
  have hquart : (3 * x / 4) ^ 4 / 24 ≤ Real.exp (3 * x / 4) := by
    have hy : (0 : ℝ) ≤ 3 * x / 4 := by linarith
    have h := Real.sum_le_exp_of_nonneg hy 5
    simp [Finset.sum_range_succ, Nat.factorial] at h
    nlinarith [pow_nonneg hy 2, pow_nonneg hy 3]
  have hcore : 4 * x ^ 2 ≤ Real.exp (3 * x / 4) := by
    have h324 : (324 : ℝ) ≤ x ^ 2 := by nlinarith
    have hx2pos : (0 : ℝ) < x ^ 2 := by positivity
    have hpoly : 4 * x ^ 2 ≤ (3 * x / 4) ^ 4 / 24 := by nlinarith [h324, hx2pos]
    linarith
  have hL4 : (0 : ℝ) < L ^ 4 := by positivity
  have hfinal : 81 / 16384 * L ^ 6 * α ^ 2
      ≤ 81 / 65536 * L ^ 4 * Real.exp (3 * x / 4) := by
    have hleft : 81 / 16384 * L ^ 6 * α ^ 2 = 81 / 16384 * L ^ 4 * x ^ 2 := by
      rw [hx2]; ring
    rw [hleft]
    nlinarith [hcore, hL4]
  calc 81 / 16384 * L ^ 6 * α ^ 2 ≤ 81 / 65536 * L ^ 4 * Real.exp (3 * x / 4) := hfinal
    _ = (9 / 256 * L ^ 2 * Real.exp (3 * |α| * L / 8)) ^ 2 := hval.symm
    _ ≤ windowEnergyBound φ L α ^ 2 := hsq

/-! ### Non-vacuity: source-regime tapers exist at every scale -/

/-- **The source-regime hypotheses are satisfiable at every scale.**  For every
`L > 0` there is a `C¹`, even, nonnegative taper, supported in `[-L/2, L/2]`
(so `2R ≤ L`), identically `1` on the plateau `|t| ≤ 3L/8`.  Hence the negative
results above are statements about a nonempty class. -/
theorem exists_sourceTaper (L : ℝ) (hL : 0 < L) :
    ∃ φ : ℝ → ℝ, C1Taper φ (L / 2) ∧ (∀ t, φ (-t) = φ t) ∧ (∀ t, 0 ≤ φ t) ∧
      (∀ t, |t| ≤ 3 * L / 8 → φ t = 1) := by
  set D : ℝ := (L / 2) ^ 2 - (3 * L / 8) ^ 2 with hD
  have hDpos : 0 < D := by rw [hD]; nlinarith
  refine ⟨fun t => Real.smoothTransition (((L / 2) ^ 2 - t ^ 2) / D), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · have h2 : ContDiff ℝ 2 fun t : ℝ => Real.smoothTransition (((L / 2) ^ 2 - t ^ 2) / D) :=
      Real.smoothTransition.contDiff.comp (by fun_prop)
    exact h2.differentiable (by norm_num)
  · have h2 : ContDiff ℝ 2 fun t : ℝ => Real.smoothTransition (((L / 2) ^ 2 - t ^ 2) / D) :=
      Real.smoothTransition.contDiff.comp (by fun_prop)
    exact ContDiff.continuous_deriv h2 (by norm_num)
  · intro t ht
    refine Real.smoothTransition.zero_of_nonpos ?_
    have habs : (L / 2) ^ 2 < t ^ 2 := by
      have h1 : L / 2 < |t| := ht
      nlinarith [abs_nonneg t, sq_abs t, hL]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hDpos.le
  · intro t
    simp
  · intro t
    exact Real.smoothTransition.nonneg _
  · intro t ht
    refine Real.smoothTransition.one_of_one_le ?_
    have habs : t ^ 2 ≤ (3 * L / 8) ^ 2 := by
      nlinarith [abs_nonneg t, sq_abs t, hL]
    rw [le_div_iff₀ hDpos, hD]
    linarith

end RiemannAnalytic
