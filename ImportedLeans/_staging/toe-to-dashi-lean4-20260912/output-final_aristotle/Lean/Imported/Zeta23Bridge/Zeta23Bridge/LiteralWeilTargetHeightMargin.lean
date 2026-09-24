/-
# An explicit margin for the target height defect, and an explicit ceiling

The separation gate of `LiteralWeilTwoRadiusSeparationGate` needs the two sides of

    E_red(t, r) < D_{ρ*}(r) = 2 m_{ρ*} D(a_*, 0; r)

to be estimated *quantitatively*.  Strict positivity `0 < D(a, 0)` — already proved
in `LiteralWeilTwoRadiusHeightDetector` — is not enough; a **margin** is needed.

This module supplies both a floor and a ceiling for the signal side.

* **Floor (rectangular lower bound).**  The height defect has the integral
  representation `2 D(a, 0) = ∫∫ g(u) g(v) K_r,a(u, v)` with a *pointwise
  nonnegative* integrand.  Discarding everything outside a rectangle
  `[p, q] × [p', q']` on which `g ≥ c` and `K_r,a ≥ κ` therefore gives the literal
  bound

      D(a, 0; r) ≥ c² κ (q − p)(q' − p') / 2.

  `heightDefect_ge_rectangle`.  This is much better behaved than trying to estimate
  the double integral globally.

* **Such a rectangle exists, with positive constants.**
  `exists_rectangle_margin` produces one by continuity around the two points of
  different modulus where the taper is positive, taking `κ` to be the minimum of the
  (continuous, strictly positive) kernel on the resulting compact rectangle.
  `targetHeightDefectLowerMargin` packages floor + existence, and
  `zeroHeightDefect_ge_margin` transports it to the literal per-zero defect
  `D_{ρ*} = 2 m_{ρ*} D(a_*, 0)` using `m_{ρ*} ≥ 1`.

* **Ceiling.**  `heightDefect_le_taperMass`: for a nonnegative taper supported in
  `|u| ≤ Λ`,

      D(a, 0; r) ≤ (∫ g)² (cosh(aΛ) − 1).

  This is the *scaling audit* input on the signal side: as the high-ordinate lane
  forces `Λ → 0` (the taper of `exists_positive_taper_poleEven_zero` has
  `Λ ≤ 9π/(4|t|)`), the target signal is at most `(∫g)² (cosh(aΛ) − 1) = O(a²Λ²)(∫g)²`,
  i.e. it decays quadratically in `1/|t|` relative to the taper mass.

* **Consequence for the gate.**  `gate_forces_small_pole_channel`: any proof of the
  gate inequality must in particular force the doubled-radius pole penalty below the
  signal ceiling,

      4 |P_t(2r)| |A₀(r)| < 2 m_{ρ*} (∫ g)² (cosh(a_*Λ) − 1).

  That is the precise quantitative demand the pole channel now has to meet; no claim
  is made here that it can.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

noncomputable section

open MeasureTheory
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilTargetHeightMargin

open Zeta23Bridge.LiteralWeilParityBalance Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilEvenChannelTaper Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilOffOrdinateTail Zeta23Bridge.LiteralWeilGammaConeBound
open Zeta23Bridge.LiteralWeilTwoRadiusResidualEnvelope
open Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

/-! ## The two-radius kernel at the on-line comparison height -/

/-- The antisymmetrised kernel of the two-radius even defect against the on-line
profile. -/
def twoRadiusKernel (r a u v : ℝ) : ℝ :=
  (Real.cosh (a * u) - Real.cosh (a * v))
    * (Real.cos (r * u) * Real.cos (2 * r * v) - Real.cos (2 * r * u) * Real.cos (r * v))

theorem heightIntegrand_zero_eq (g : ℝ → ℝ) (r a : ℝ) (z : ℝ × ℝ) :
    heightIntegrand g r a 0 z = g z.1 * g z.2 * twoRadiusKernel r a z.1 z.2 := by
  unfold heightIntegrand twoRadiusKernel
  simp

theorem continuous_twoRadiusKernel (r a : ℝ) :
    Continuous fun z : ℝ × ℝ => twoRadiusKernel r a z.1 z.2 := by
  unfold twoRadiusKernel
  fun_prop

/-- The kernel is strictly positive at unequal moduli inside the radially admissible
range, for every nonzero height. -/
theorem twoRadiusKernel_pos {r a u v : ℝ} (hr : 0 < r) (ha : a ≠ 0)
    (hu : 2 * r * |u| < π / 2) (hv : 2 * r * |v| < π / 2) (hne : |u| ≠ |v|) :
    0 < twoRadiusKernel r a u v := by
  have h := heightKernel2_pos (b := 0) hr (by simpa using abs_pos.mpr ha) hu hv hne
  simpa [twoRadiusKernel] using h

/-! ## The rectangular lower bound -/

/-- **`heightDefect_ge_rectangle`.**  A literal rectangular-region lower bound for the
two-radius even defect: on a rectangle where the taper is at least `c` and the kernel
at least `κ`, the discarded part of the integral is nonnegative, so

    D(a, 0; r) ≥ c² κ (q − p)(q' − p') / 2. -/
theorem heightDefect_ge_rectangle {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u) {r : ℝ} (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) {a : ℝ}
    {p q p' q' c κ : ℝ} (hpq : p ≤ q) (hpq' : p' ≤ q') (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (hgA : ∀ u ∈ Set.Icc p q, c ≤ g u) (hgB : ∀ v ∈ Set.Icc p' q', c ≤ g v)
    (hK : ∀ u ∈ Set.Icc p q, ∀ v ∈ Set.Icc p' q', κ ≤ twoRadiusKernel r a u v) :
    c ^ 2 * κ * ((q - p) * (q' - p')) / 2 ≤ heightDefect g r a 0 := by
  set F : ℝ × ℝ → ℝ := heightIntegrand g r a 0 with hF
  have hrep : 2 * heightDefect g r a 0 = ∫ z : ℝ × ℝ, F z :=
    heightDefect_two_mul hg hgc r a 0
  have hFnn : ∀ z : ℝ × ℝ, 0 ≤ F z :=
    heightIntegrand_nonneg hnn hr hrad (by simp)
  have hFint : Integrable F := integrable_heightIntegrand hg hgc r a 0
  set S : Set (ℝ × ℝ) := Set.Icc p q ×ˢ Set.Icc p' q' with hS
  have hSmeas : MeasurableSet S := (measurableSet_Icc).prod measurableSet_Icc
  have hSvol : volume S = ENNReal.ofReal (q - p) * ENNReal.ofReal (q' - p') := by
    rw [hS, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  have hSfin : volume S ≠ ⊤ := by
    rw [hSvol]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hSreal : (volume S).toReal = (q - p) * (q' - p') := by
    rw [hSvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
      ENNReal.toReal_ofReal (by linarith)]
  have hconst : ∀ z ∈ S, c ^ 2 * κ ≤ F z := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have h1 : c ≤ g u := hgA u hu
    have h2 : c ≤ g v := hgB v hv
    have h3 : κ ≤ twoRadiusKernel r a u v := hK u hu v hv
    have hFz : F (u, v) = g u * g v * twoRadiusKernel r a u v :=
      heightIntegrand_zero_eq g r a (u, v)
    rw [hFz]
    have hcc : c * c ≤ g u * g v := mul_le_mul h1 h2 hc (le_trans hc h1)
    nlinarith [le_trans hc h1, le_trans hc h2, le_trans hκ h3]
  have hIntOn : IntegrableOn F S := hFint.integrableOn
  have hlow : (volume S).toReal • (c ^ 2 * κ) ≤ ∫ z in S, F z := by
    simpa [measureReal_def] using
      setIntegral_ge_of_const_le (μ := (volume : Measure (ℝ × ℝ))) hSmeas hSfin hconst hIntOn
  have hup : ∫ z in S, F z ≤ ∫ z : ℝ × ℝ, F z :=
    setIntegral_le_integral hFint (Filter.Eventually.of_forall hFnn)
  rw [hSreal, smul_eq_mul] at hlow
  linarith

/-! ## Such a rectangle exists -/

/-- A continuous function that is positive at a point is bounded below by half its
value on a closed interval around that point. -/
theorem exists_interval_lower_bound {g : ℝ → ℝ} (hg : Continuous g) {u₀ : ℝ} (hu₀ : 0 < g u₀) :
    ∃ δ > 0, ∀ u, |u - u₀| ≤ δ → g u₀ / 2 ≤ g u := by
  have hopen : IsOpen {u : ℝ | g u₀ / 2 < g u} := isOpen_lt continuous_const hg
  have hmem : u₀ ∈ {u : ℝ | g u₀ / 2 < g u} := by
    show g u₀ / 2 < g u₀
    linarith
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen u₀ hmem
  refine ⟨ε / 2, by positivity, fun u hu => ?_⟩
  have hmem' : u ∈ Metric.ball u₀ ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    linarith
  exact (hball hmem').le

/-- **`exists_rectangle_margin`.**  For a nonnegative, radially admissible taper that
is strictly positive at two points of different modulus, and for any nonzero height,
there is a genuine rectangle on which the taper and the kernel both have *uniform
positive* lower bounds. -/
theorem exists_rectangle_margin {g : ℝ → ℝ} (hg : Continuous g)
    {r : ℝ} (hr : 0 < r) (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
    {u₀ v₀ : ℝ} (hu₀ : 0 < g u₀) (hv₀ : 0 < g v₀) (hne : |u₀| ≠ |v₀|) {a : ℝ} (ha : a ≠ 0) :
    ∃ p q p' q' c κ : ℝ, p < q ∧ p' < q' ∧ 0 < c ∧ 0 < κ
      ∧ (∀ u ∈ Set.Icc p q, c ≤ g u) ∧ (∀ v ∈ Set.Icc p' q', c ≤ g v)
      ∧ (∀ u ∈ Set.Icc p q, ∀ v ∈ Set.Icc p' q', κ ≤ twoRadiusKernel r a u v) := by
  obtain ⟨δ₁, hδ₁, hb₁⟩ := exists_interval_lower_bound hg hu₀
  obtain ⟨δ₂, hδ₂, hb₂⟩ := exists_interval_lower_bound hg hv₀
  set d : ℝ := |(|u₀| - |v₀|)| with hd
  have hdpos : 0 < d := by
    rw [hd, abs_pos]
    exact sub_ne_zero.mpr hne
  set δ : ℝ := min (min δ₁ δ₂) (d / 4) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min hδ₁ hδ₂) (by positivity)
  have hδ1 : δ ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ2 : δ ≤ δ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδd : δ ≤ d / 4 := min_le_right _ _
  set c : ℝ := min (g u₀ / 2) (g v₀ / 2) with hcdef
  have hc : 0 < c := lt_min (by linarith) (by linarith)
  have hgA : ∀ u ∈ Set.Icc (u₀ - δ) (u₀ + δ), c ≤ g u := by
    rintro u ⟨h1, h2⟩
    have habs : |u - u₀| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
    exact le_trans (min_le_left _ _) (hb₁ u (le_trans habs hδ1))
  have hgB : ∀ v ∈ Set.Icc (v₀ - δ) (v₀ + δ), c ≤ g v := by
    rintro v ⟨h1, h2⟩
    have habs : |v - v₀| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
    exact le_trans (min_le_right _ _) (hb₂ v (le_trans habs hδ2))
  -- the kernel is strictly positive at every point of the rectangle
  have hKpos : ∀ z ∈ Set.Icc (u₀ - δ) (u₀ + δ) ×ˢ Set.Icc (v₀ - δ) (v₀ + δ),
      0 < twoRadiusKernel r a z.1 z.2 := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have hgu : 0 < g u := lt_of_lt_of_le hc (hgA u hu)
    have hgv : 0 < g v := lt_of_lt_of_le hc (hgB v hv)
    have hdu : |u - u₀| ≤ δ := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hdv : |v - v₀| ≤ δ := abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have h1 : |(|u| - |u₀|)| ≤ δ := le_trans (abs_abs_sub_abs_le_abs_sub u u₀) hdu
    have h2 : |(|v| - |v₀|)| ≤ δ := le_trans (abs_abs_sub_abs_le_abs_sub v v₀) hdv
    have hne' : |u| ≠ |v| := by
      intro heq
      obtain ⟨h1a, h1b⟩ := abs_le.mp h1
      obtain ⟨h2a, h2b⟩ := abs_le.mp h2
      have hdle : d ≤ 2 * δ := by
        rw [hd]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    exact twoRadiusKernel_pos hr ha (hrad u hgu.ne') (hrad v hgv.ne') hne'
  -- minimise the kernel over the compact rectangle
  have hcompact : IsCompact (Set.Icc (u₀ - δ) (u₀ + δ) ×ˢ Set.Icc (v₀ - δ) (v₀ + δ)) :=
    isCompact_Icc.prod isCompact_Icc
  have hnonempty : (Set.Icc (u₀ - δ) (u₀ + δ) ×ˢ Set.Icc (v₀ - δ) (v₀ + δ)).Nonempty :=
    ⟨(u₀, v₀), ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨z₀, hz₀mem, hz₀min⟩ :=
    hcompact.exists_isMinOn hnonempty (continuous_twoRadiusKernel r a).continuousOn
  refine ⟨u₀ - δ, u₀ + δ, v₀ - δ, v₀ + δ, c, twoRadiusKernel r a z₀.1 z₀.2, by linarith,
    by linarith, hc, hKpos z₀ hz₀mem, hgA, hgB, ?_⟩
  intro u hu v hv
  exact hz₀min (Set.mk_mem_prod hu hv)

/-- **`targetHeightDefectLowerMargin`.**  The floor and its witness combined: the
two-radius even defect of an off-line height exceeds an explicit, strictly positive
rectangular quantity. -/
theorem targetHeightDefectLowerMargin {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hnn : ∀ u, 0 ≤ g u) {r : ℝ} (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
    {u₀ v₀ : ℝ} (hu₀ : 0 < g u₀) (hv₀ : 0 < g v₀) (hne : |u₀| ≠ |v₀|) {a : ℝ} (ha : a ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ m ≤ heightDefect g r a 0
      ∧ ∃ p q p' q' c κ : ℝ, p < q ∧ p' < q' ∧ 0 < c ∧ 0 < κ
        ∧ (∀ u ∈ Set.Icc p q, c ≤ g u) ∧ (∀ v ∈ Set.Icc p' q', c ≤ g v)
        ∧ (∀ u ∈ Set.Icc p q, ∀ v ∈ Set.Icc p' q', κ ≤ twoRadiusKernel r a u v)
        ∧ m = c ^ 2 * κ * ((q - p) * (q' - p')) / 2 := by
  obtain ⟨p, q, p', q', c, κ, hpq, hpq', hc, hκ, hgA, hgB, hK⟩ :=
    exists_rectangle_margin hg hr hrad hu₀ hv₀ hne ha
  refine ⟨c ^ 2 * κ * ((q - p) * (q' - p')) / 2, ?_, ?_,
    p, q, p', q', c, κ, hpq, hpq', hc, hκ, hgA, hgB, hK, rfl⟩
  · have h1 : 0 < q - p := by linarith
    have h2 : 0 < q' - p' := by linarith
    positivity
  · exact heightDefect_ge_rectangle hg hgc hnn hr hrad hpq.le hpq'.le hc.le hκ.le hgA hgB hK

/-- The same margin for the literal per-zero defect `D_{ρ} = 2 m_ρ D(a_ρ, 0)`, using
that multiplicities are at least one. -/
theorem zeroHeightDefect_ge_margin {g : ℝ → ℝ} {r : ℝ} {ρ : Zeros} {m : ℝ}
    (hm : 0 ≤ m) (hle : m ≤ heightDefect g r (heightOf ρ) 0) :
    2 * m ≤ zeroHeightDefect g r ρ := by
  have h1 : (1 : ℕ) ≤ (Zeta23.zetaZeroConfig).mult ρ :=
    (Zeta23.zetaZeroConfig).one_le_mult (ρ : ℂ) ρ.2
  have h1R : (1 : ℝ) ≤ ((Zeta23.zetaZeroConfig).mult ρ : ℝ) := by exact_mod_cast h1
  unfold zeroHeightDefect
  nlinarith

/-! ## The ceiling, and what the gate demands of the pole channel -/

theorem abs_radialFactor_le_two (r u v : ℝ) :
    |Real.cos (r * u) * Real.cos (2 * r * v) - Real.cos (2 * r * u) * Real.cos (r * v)| ≤ 2 := by
  have h1 : |Real.cos (r * u) * Real.cos (2 * r * v)| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _)
  have h2 : |Real.cos (2 * r * u) * Real.cos (r * v)| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _)
  calc |Real.cos (r * u) * Real.cos (2 * r * v) - Real.cos (2 * r * u) * Real.cos (r * v)|
      ≤ |Real.cos (r * u) * Real.cos (2 * r * v)| + |Real.cos (2 * r * u) * Real.cos (r * v)| :=
        abs_sub _ _
    _ ≤ 2 := by linarith

/-- The pointwise ceiling for the antisymmetrised integrand of a taper supported in
`|u| ≤ Λ`. -/
theorem heightIntegrand_le {g : ℝ → ℝ} (hnn : ∀ u, 0 ≤ g u) {Λ : ℝ}
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (r a : ℝ) (z : ℝ × ℝ) :
    heightIntegrand g r a 0 z ≤ 2 * (Real.cosh (a * Λ) - 1) * (g z.1 * g z.2) := by
  rw [heightIntegrand_zero_eq]
  by_cases h1 : g z.1 = 0
  · simp [h1]
  by_cases h2 : g z.2 = 0
  · simp [h2]
  have hu : |z.1| ≤ Λ := hsupp _ h1
  have hv : |z.2| ≤ Λ := hsupp _ h2
  have hcu : Real.cosh (a * z.1) ≤ Real.cosh (a * Λ) := by
    refine Real.cosh_le_cosh.mpr ?_
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (le_trans hu (le_abs_self Λ)) (abs_nonneg a)
  have hcv : Real.cosh (a * z.2) ≤ Real.cosh (a * Λ) := by
    refine Real.cosh_le_cosh.mpr ?_
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (le_trans hv (le_abs_self Λ)) (abs_nonneg a)
  have hlu : (1 : ℝ) ≤ Real.cosh (a * z.1) := Real.one_le_cosh _
  have hlv : (1 : ℝ) ≤ Real.cosh (a * z.2) := Real.one_le_cosh _
  have hdiff : |Real.cosh (a * z.1) - Real.cosh (a * z.2)| ≤ Real.cosh (a * Λ) - 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hrad2 := abs_radialFactor_le_two r z.1 z.2
  have hK : |twoRadiusKernel r a z.1 z.2| ≤ 2 * (Real.cosh (a * Λ) - 1) := by
    unfold twoRadiusKernel
    rw [abs_mul]
    have hnn1 : (0 : ℝ) ≤ Real.cosh (a * Λ) - 1 := by
      have := Real.one_le_cosh (a * Λ); linarith
    calc |Real.cosh (a * z.1) - Real.cosh (a * z.2)|
          * |Real.cos (r * z.1) * Real.cos (2 * r * z.2)
              - Real.cos (2 * r * z.1) * Real.cos (r * z.2)|
        ≤ (Real.cosh (a * Λ) - 1) * 2 :=
          mul_le_mul hdiff hrad2 (abs_nonneg _) hnn1
      _ = 2 * (Real.cosh (a * Λ) - 1) := by ring
  have hprod : 0 ≤ g z.1 * g z.2 := mul_nonneg (hnn _) (hnn _)
  have hKle : twoRadiusKernel r a z.1 z.2 ≤ 2 * (Real.cosh (a * Λ) - 1) :=
    le_trans (le_abs_self _) hK
  nlinarith

/-- **`heightDefect_le_taperMass`.**  The signal ceiling: for a nonnegative taper
supported in `|u| ≤ Λ`,

    D(a, 0; r) ≤ (∫ g)² (cosh(aΛ) − 1),

uniformly in the sampling radius.  Since the short-taper/high-ordinate lane forces
`Λ = O(1/|t|)`, the target signal is `O(a²Λ²)` relative to the squared taper mass. -/
theorem heightDefect_le_taperMass {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u) {Λ : ℝ} (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (r a : ℝ) :
    heightDefect g r a 0 ≤ (∫ u : ℝ, g u) ^ 2 * (Real.cosh (a * Λ) - 1) := by
  have hgint : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hrep : 2 * heightDefect g r a 0 = ∫ z : ℝ × ℝ, heightIntegrand g r a 0 z :=
    heightDefect_two_mul hg hgc r a 0
  have hFint : Integrable (heightIntegrand g r a 0) := integrable_heightIntegrand hg hgc r a 0
  have hprodc : Continuous fun z : ℝ × ℝ => g z.1 * g z.2 :=
    (hg.comp continuous_fst).mul (hg.comp continuous_snd)
  have hprodsupp : HasCompactSupport fun z : ℝ × ℝ => g z.1 * g z.2 := by
    apply HasCompactSupport.intro (hgc.prod hgc)
    intro z hz
    have h : g z.1 = 0 ∨ g z.2 = 0 := by
      by_contra hcon
      push Not at hcon
      exact hz ⟨subset_tsupport g hcon.1, subset_tsupport g hcon.2⟩
    rcases h with h | h <;> simp [h]
  have hprodint : Integrable fun z : ℝ × ℝ => g z.1 * g z.2 :=
    hprodc.integrable_of_hasCompactSupport hprodsupp
  have hmaj : Integrable fun z : ℝ × ℝ => 2 * (Real.cosh (a * Λ) - 1) * (g z.1 * g z.2) :=
    hprodint.const_mul _
  have hmono : ∫ z : ℝ × ℝ, heightIntegrand g r a 0 z
      ≤ ∫ z : ℝ × ℝ, 2 * (Real.cosh (a * Λ) - 1) * (g z.1 * g z.2) :=
    integral_mono hFint hmaj (fun z => heightIntegrand_le hnn hsupp r a z)
  have hsq : ∫ z : ℝ × ℝ, g z.1 * g z.2 = (∫ u : ℝ, g u) ^ 2 := by
    have := MeasureTheory.integral_prod_mul (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ)) g g
    rw [← MeasureTheory.Measure.volume_eq_prod] at this
    rw [this]
    ring
  rw [integral_const_mul, hsq] at hmono
  linarith

/-- **`gate_forces_small_pole_channel`.**  Combining the ceiling with the gate: if the
reduced envelope really is below the target-local defect, then in particular the
doubled-radius pole penalty is below the signal ceiling.  Everything appearing here is
an explicit finite expression, so this is the exact quantitative demand the pole
channel would have to meet. -/
theorem gate_forces_small_pole_channel {g : ℝ → ℝ} {t r Λ : ℝ} (hd : GateData g t r Λ)
    (ρ₀ : Zeros)
    (hsep : reducedEnvelope g Λ t r < zeroHeightDefect g r ρ₀) :
    4 * |poleEvenResp g t (2 * r)| * |evenResp g 0 r|
      < 2 * ((Zeta23.zetaZeroConfig).mult ρ₀ : ℝ)
          * ((∫ u : ℝ, g u) ^ 2 * (Real.cosh (heightOf ρ₀ * Λ) - 1)) := by
  have hceil : heightDefect g r (heightOf ρ₀) 0
      ≤ (∫ u : ℝ, g u) ^ 2 * (Real.cosh (heightOf ρ₀ * Λ) - 1) :=
    heightDefect_le_taperMass hd.smooth.continuous hd.compactSupport hd.nonneg
      hd.supportRadius r (heightOf ρ₀)
  have hmR : (0 : ℝ) ≤ ((Zeta23.zetaZeroConfig).mult ρ₀ : ℝ) := by positivity
  have hdef : zeroHeightDefect g r ρ₀
      ≤ 2 * ((Zeta23.zetaZeroConfig).mult ρ₀ : ℝ)
          * ((∫ u : ℝ, g u) ^ 2 * (Real.cosh (heightOf ρ₀ * Λ) - 1)) := by
    unfold zeroHeightDefect
    nlinarith
  have hz1 := epsZero_nonneg g Λ t (2 * r)
  have hz2 := epsZero_nonneg g Λ t r
  have hg1 := epsGamma_nonneg g t (2 * r)
  have hg2 := epsGamma_nonneg g t r
  have hA1 := abs_nonneg (evenResp g 0 r)
  have hA2 := abs_nonneg (evenResp g 0 (2 * r))
  have hlow : 4 * |poleEvenResp g t (2 * r)| * |evenResp g 0 r| ≤ reducedEnvelope g Λ t r := by
    unfold reducedEnvelope
    nlinarith
  linarith

/-! ## The off-ordinate channel: what the gate demands of the zero tail -/

theorem norm_sampleTest (g : ℝ → ℝ) (t s u : ℝ) : ‖sampleTest g t s u‖ = |g u| := by
  unfold sampleTest
  rw [norm_mul, Complex.norm_exp]
  simp

/-- The taper mass is a lower bound for the strip constant of every sample test
function: the `L¹` norm of `k = g e^{i(s−t)u}` is the taper mass itself, and both the
exponential factor and the second-derivative term only increase it. -/
theorem taperMass_le_stripConst {g : ℝ → ℝ} (hnn : ∀ u, 0 ≤ g u) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (t s : ℝ) : (∫ u : ℝ, g u) ≤ stripConst (sampleTest g t s) Λ := by
  have h1 : (∫ u : ℝ, ‖sampleTest g t s u‖) = ∫ u : ℝ, g u := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show ‖sampleTest g t s u‖ = g u
    rw [norm_sampleTest, abs_of_nonneg (hnn u)]
  have h2 : (0 : ℝ) ≤ ∫ u : ℝ, ‖deriv (deriv (sampleTest g t s)) u‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have h3 : (1 : ℝ) ≤ Real.exp (Λ / 2) := Real.one_le_exp (by linarith)
  have h0 : (0 : ℝ) ≤ ∫ u : ℝ, g u := integral_nonneg hnn
  unfold stripConst
  rw [h1]
  nlinarith

/-- Consequently the off-ordinate envelope is at least `4 (∫ g) W(t)`, where
`W(t) = offOrdWeight t` is the companion's off-ordinate zero weight. -/
theorem taperMass_le_epsZero {g : ℝ → ℝ} (hnn : ∀ u, 0 ≤ g u) {Λ : ℝ} (hΛ : 0 ≤ Λ) (t s : ℝ) :
    4 * (∫ u : ℝ, g u) * offOrdWeight t ≤ epsZero g Λ t s := by
  have h1 := taperMass_le_stripConst hnn hΛ t s
  have h2 := taperMass_le_stripConst hnn hΛ t (-s)
  have hw := offOrdWeight_nonneg t
  unfold epsZero
  nlinarith

/-- On the radially admissible range the base-radius cosine never falls below `1/2`. -/
theorem half_le_cos_of_radial {r u : ℝ} (hr : 0 < r) (hu : 2 * r * |u| < π / 2) :
    (1 : ℝ) / 2 ≤ Real.cos (r * u) := by
  have hpi := Real.pi_pos
  have habs : |r * u| ≤ π / 3 := by
    rw [abs_mul, abs_of_pos hr]
    nlinarith [abs_nonneg u]
  have hle := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (r * u)) (by linarith) habs
  rw [Real.cos_abs, Real.cos_pi_div_three] at hle
  exact hle

/-- The on-line base-radius response is at least half the taper mass. -/
theorem taperMass_half_le_evenResp {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u) {r : ℝ} (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) :
    (1 : ℝ) / 2 * (∫ u : ℝ, g u) ≤ evenResp g 0 r := by
  have hint : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hintc : Integrable fun u : ℝ => g u * (Real.cosh (0 * u) * Real.cos (r * u)) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact hgc.mul_right
  have hpt : ∀ u : ℝ, 1 / 2 * g u ≤ g u * (Real.cosh (0 * u) * Real.cos (r * u)) := by
    intro u
    by_cases hu : g u = 0
    · simp [hu]
    · have hcos := half_le_cos_of_radial hr (hrad u hu)
      have hg0 : 0 ≤ g u := hnn u
      have : Real.cosh (0 * u) = 1 := by simp
      rw [this, one_mul]
      nlinarith
  have hmono : ∫ u : ℝ, 1 / 2 * g u
      ≤ ∫ u : ℝ, g u * (Real.cosh (0 * u) * Real.cos (r * u)) :=
    integral_mono (hint.const_mul _) hintc hpt
  rwa [integral_const_mul] at hmono

/-- A nonnegative continuous taper that is positive somewhere has positive mass. -/
theorem taperMass_pos {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u) {u₀ : ℝ} (hu₀ : 0 < g u₀) : 0 < ∫ u : ℝ, g u := by
  have hint : Integrable g := hg.integrable_of_hasCompactSupport hgc
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have hopen : IsOpen {u : ℝ | 0 < g u} := isOpen_lt continuous_const hg
  have hsub : {u : ℝ | 0 < g u} ⊆ Function.support g := fun u hu => ne_of_gt hu
  exact lt_of_lt_of_le (hopen.measure_pos volume ⟨u₀, hu₀⟩) (measure_mono hsub)

/-- **`gate_forces_small_offOrdinate_weight`.**  The scaling audit on the
off-ordinate channel.  The zero-tail envelope alone contributes at least
`2 (∫ g)² W(t)` to the reduced envelope, while the signal ceiling is
`2 m_ρ (∫ g)² (cosh(a_ρ Λ) − 1)`; so the gate inequality forces

    W(t) < m_ρ (cosh(a_ρ Λ) − 1).

Both sides are explicit, and the right-hand side is `O(a² Λ²)`. -/
theorem gate_forces_small_offOrdinate_weight {g : ℝ → ℝ} {t r Λ : ℝ} (hd : GateData g t r Λ)
    (ρ₀ : Zeros) (hsep : reducedEnvelope g Λ t r < zeroHeightDefect g r ρ₀) :
    offOrdWeight t < ((Zeta23.zetaZeroConfig).mult ρ₀ : ℝ)
      * (Real.cosh (heightOf ρ₀ * Λ) - 1) := by
  obtain ⟨u₀, v₀, hu₀, hv₀, hne⟩ := hd.twoPoint
  have hmass : 0 < ∫ u : ℝ, g u :=
    taperMass_pos hd.smooth.continuous hd.compactSupport hd.nonneg hu₀
  have hA : (1 : ℝ) / 2 * (∫ u : ℝ, g u) ≤ evenResp g 0 r :=
    taperMass_half_le_evenResp hd.smooth.continuous hd.compactSupport hd.nonneg hd.radiusPos
      hd.radial
  have hAabs : (1 : ℝ) / 2 * (∫ u : ℝ, g u) ≤ |evenResp g 0 r| :=
    le_trans hA (le_abs_self _)
  have hz := taperMass_le_epsZero hd.nonneg hd.lambdaNonneg t (2 * r)
  have hz2 := epsZero_nonneg g Λ t r
  have hg1 := epsGamma_nonneg g t (2 * r)
  have hg2 := epsGamma_nonneg g t r
  have hA2 := abs_nonneg (evenResp g 0 (2 * r))
  have hP := abs_nonneg (poleEvenResp g t (2 * r))
  have hw := offOrdWeight_nonneg t
  have hlow : 2 * (∫ u : ℝ, g u) ^ 2 * offOrdWeight t ≤ reducedEnvelope g Λ t r := by
    unfold reducedEnvelope
    nlinarith [mul_le_mul hz hAabs (by positivity) (le_trans (by positivity) hz)]
  have hceil : heightDefect g r (heightOf ρ₀) 0
      ≤ (∫ u : ℝ, g u) ^ 2 * (Real.cosh (heightOf ρ₀ * Λ) - 1) :=
    heightDefect_le_taperMass hd.smooth.continuous hd.compactSupport hd.nonneg
      hd.supportRadius r (heightOf ρ₀)
  have hmR : (0 : ℝ) ≤ ((Zeta23.zetaZeroConfig).mult ρ₀ : ℝ) := by positivity
  have hdef : zeroHeightDefect g r ρ₀
      ≤ 2 * ((Zeta23.zetaZeroConfig).mult ρ₀ : ℝ)
          * ((∫ u : ℝ, g u) ^ 2 * (Real.cosh (heightOf ρ₀ * Λ) - 1)) := by
    unfold zeroHeightDefect
    nlinarith
  have hsq : 0 < (∫ u : ℝ, g u) ^ 2 := by positivity
  nlinarith

/-- **`highOrdinate_gate_forces_vanishing_zeroTail`.**  The audit, in the lane the
programme is actually in.  For the explicit high-ordinate taper the support radius is
`Λ = 9π/(4|t|)`, so the necessary condition reads

    W(t) < m_ρ (cosh(a_ρ · 9π/(4|t|)) − 1),

whose right-hand side tends to `0` as `|t| → ∞` while the left-hand side is the
ordinate-`t` complement of a fixed convergent positive zero sum.  This is the exact
obstruction the remaining zero-tail estimate faces in this regime. -/
theorem highOrdinate_gate_forces_vanishing_zeroTail {t : ℝ} (ht : t ≠ 0)
    (hheight : 9 * π ≤ 4 * |t| * Real.log 2) (ρ₀ : Zeros) :
    ∃ (g : ℝ → ℝ) (r : ℝ), GateData g t r (9 * π / (4 * |t|)) ∧
      (reducedEnvelope g (9 * π / (4 * |t|)) t r < zeroHeightDefect g r ρ₀ →
        offOrdWeight t < ((Zeta23.zetaZeroConfig).mult ρ₀ : ℝ)
          * (Real.cosh (heightOf ρ₀ * (9 * π / (4 * |t|))) - 1)) := by
  obtain ⟨g, r, hd⟩ := exists_gateData ht hheight
  exact ⟨g, r, hd, fun hsep => gate_forces_small_offOrdinate_weight hd ρ₀ hsep⟩

/-! ## A no-go: the gate is impossible once one off-ordinate zero is heavy enough -/

/-- A single off-ordinate zero already bounds the off-ordinate weight from below. -/
theorem zeroWeight_le_offOrdWeight {t : ℝ} (σ : ((SameOrd t)ᶜ : Set Zeros)) :
    zeroWeight (σ : Zeros) ≤ offOrdWeight t :=
  (summable_offOrdWeight t).le_tsum σ (fun j _ => zeroWeight_nonneg (j : Zeros))

/-- `cosh x - 1 ≤ x²` on `|x| ≤ 1`. -/
theorem cosh_sub_one_le_sq {x : ℝ} (hx : |x| ≤ 1) : Real.cosh x - 1 ≤ x ^ 2 := by
  have h1 := Real.abs_exp_sub_one_sub_id_le hx
  have h2 := Real.abs_exp_sub_one_sub_id_le (x := -x) (by rwa [abs_neg])
  rw [Real.cosh_eq]
  have a1 := abs_le.mp h1
  have a2 := abs_le.mp h2
  nlinarith [sq_nonneg x, sq_abs x]

/-- **`gate_fails_of_heavy_offOrdinate_zero`.**  If some zero off the ordinate `t`
carries at least the threshold weight `m_ρ (cosh(a_ρ Λ) − 1)`, the gate inequality is
impossible: the zero-tail envelope alone already exceeds the signal ceiling. -/
theorem gate_fails_of_heavy_offOrdinate_zero {g : ℝ → ℝ} {t r Λ : ℝ} (hd : GateData g t r Λ)
    (ρ₀ : Zeros) (σ : ((SameOrd t)ᶜ : Set Zeros))
    (hbig : ((Zeta23.zetaZeroConfig).mult ρ₀ : ℝ) * (Real.cosh (heightOf ρ₀ * Λ) - 1)
      ≤ zeroWeight (σ : Zeros)) :
    ¬ reducedEnvelope g Λ t r < zeroHeightDefect g r ρ₀ := by
  intro hsep
  have h1 := gate_forces_small_offOrdinate_weight hd ρ₀ hsep
  have h2 := zeroWeight_le_offOrdWeight σ
  linarith

/-- The same fact stated positively, and free of any appeal to the explicit-formula
balance: the reduced envelope is *provably at least* the target-local defect as soon as
the zero tail carries the threshold weight.  This is a statement about the sizes of two
explicit expressions, so it is a limitation of the envelope method itself. -/
theorem zeroHeightDefect_le_reducedEnvelope_of_heavy_offOrdinate_zero {g : ℝ → ℝ} {t r Λ : ℝ}
    (hd : GateData g t r Λ) (ρ₀ : Zeros) (σ : ((SameOrd t)ᶜ : Set Zeros))
    (hbig : ((Zeta23.zetaZeroConfig).mult ρ₀ : ℝ) * (Real.cosh (heightOf ρ₀ * Λ) - 1)
      ≤ zeroWeight (σ : Zeros)) :
    zeroHeightDefect g r ρ₀ ≤ reducedEnvelope g Λ t r :=
  not_lt.mp (gate_fails_of_heavy_offOrdinate_zero hd ρ₀ σ hbig)

/-- **`highOrdinate_gate_impossible_of_large_ordinate`.**  The no-go in explicit form.
In the high-ordinate lane the support radius is `Λ = 9π/(4|t|)`, so the threshold the
zero tail has to beat is at most `m_ρ a_ρ² (9π/4)² / t²`.  Hence for *every* fixed zero
`σ` off the ordinate `t`, once

    m_ρ a_ρ² (9π/4)² ≤ w_σ t²,

the gate inequality cannot hold at all — the two-radius envelope method in this lane
is quantitatively dead at large ordinates, and no further prime-side input can revive
it. -/
theorem highOrdinate_gate_impossible_of_large_ordinate {g : ℝ → ℝ} {t r : ℝ}
    (hd : GateData g t r (9 * π / (4 * |t|))) (ht : t ≠ 0) (ρ₀ : Zeros)
    (σ : ((SameOrd t)ᶜ : Set Zeros))
    (hsmall : |heightOf ρ₀ * (9 * π / (4 * |t|))| ≤ 1)
    (hlarge : ((Zeta23.zetaZeroConfig).mult ρ₀ : ℝ) * heightOf ρ₀ ^ 2 * (9 * π / 4) ^ 2
      ≤ zeroWeight (σ : Zeros) * t ^ 2) :
    ¬ reducedEnvelope g (9 * π / (4 * |t|)) t r < zeroHeightDefect g r ρ₀ := by
  have habs : 0 < |t| := abs_pos.mpr ht
  have ht2 : 0 < t ^ 2 := by positivity
  have habs2 : |t| ^ 2 = t ^ 2 := sq_abs t
  have hmR : (0 : ℝ) ≤ ((Zeta23.zetaZeroConfig).mult ρ₀ : ℝ) := by positivity
  have hcosh := cosh_sub_one_le_sq hsmall
  have hsq : (heightOf ρ₀ * (9 * π / (4 * |t|))) ^ 2
      = heightOf ρ₀ ^ 2 * (9 * π / 4) ^ 2 / t ^ 2 := by
    field_simp
    nlinarith [habs2]
  refine gate_fails_of_heavy_offOrdinate_zero hd ρ₀ σ ?_
  have hstep : ((Zeta23.zetaZeroConfig).mult ρ₀ : ℝ)
      * (Real.cosh (heightOf ρ₀ * (9 * π / (4 * |t|))) - 1)
      ≤ ((Zeta23.zetaZeroConfig).mult ρ₀ : ℝ)
        * (heightOf ρ₀ ^ 2 * (9 * π / 4) ^ 2 / t ^ 2) := by
    rw [← hsq]
    exact mul_le_mul_of_nonneg_left hcosh hmR
  have hfin : ((Zeta23.zetaZeroConfig).mult ρ₀ : ℝ)
      * (heightOf ρ₀ ^ 2 * (9 * π / 4) ^ 2 / t ^ 2) ≤ zeroWeight (σ : Zeros) := by
    rw [mul_div_assoc' , div_le_iff₀ ht2]
    linarith [hlarge]
  linarith

end LiteralWeilTargetHeightMargin
end Zeta23Bridge
