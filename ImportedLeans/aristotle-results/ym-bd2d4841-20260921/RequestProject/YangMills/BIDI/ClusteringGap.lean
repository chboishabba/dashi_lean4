/-
# §14 of the BIDI note: exponential clustering implies a spectral gap

This module proves the terminal step of the BIDI chain at the level of the
spectral measure of a state, and then hands the result to the vacuum-sector
machinery already in this library.

Let `μ` be the spectral measure of a state: a finite measure on `ℝ` carried by
`[0,∞)`.  The correlation function of the state is the Laplace transform

    C(t) = ∫ e^{-tE} dμ(E).

* `measure_Ioo_eq_zero_of_laplace_decay` — **equation (42)**: if
  `C(t) ≤ C₀ e^{-mt}` for all `t ≥ 0` and `m > 0`, then `μ((0,m)) = 0`.  Any
  spectral weight strictly inside `(0,m)` would decay strictly more slowly than
  `e^{-mt}`; the proof exhibits an interval `(0,b)` with `b < m` carrying
  positive weight and lets `t → ∞`.
* `energy_ge_of_gap_support` — with no weight in `(0,m)`, no weight below `0`
  and no atom at `0`, the mean energy satisfies `∫ E dμ ≥ m · μ(ℝ)`.
* `energy_ge_of_laplace_decay` — the composite: exponential clustering of a
  state with no vacuum component gives the energy lower bound `m‖ψ‖²`.

The Hilbert-space consequence is `hasVacuumFormGap_of_clustering`: a family of
spectral measures, one for each vacuum-orthogonal state of the domain, all
obeying the clustering bound, yields
`RequestProject.YangMills.VacuumSectorSpectralGap.HasVacuumFormGap H Ω m`, and
therefore — through the results already proved in that module — no eigenvalue
below `m`, a resolvent bound on the vacuum complement, and the Clay form of the
mass gap `Δ(H) ≥ m > 0`.

Honest scope: the spectral representation of the state (total mass `‖ψ‖²`,
mean energy `re⟪ψ,Hψ⟫`, Laplace transform equal to the correlation function) is
an *input* — it is the spectral theorem for the physical Hamiltonian, which is
not available for unbounded operators in the ambient library.  What is proved
here is everything from the clustering bound onwards.
-/
import Mathlib
import RequestProject.YangMills.VacuumSectorSpectralGap

namespace RequestProject.YangMills.BIDI

open MeasureTheory Set Filter Topology

/-! ## The Laplace-transform argument -/

section SpectralMeasure

variable (mu : Measure ℝ) [IsFiniteMeasure mu]

omit [IsFiniteMeasure mu] in
/-- A spectral measure is carried by the nonnegative half-line, so almost every
energy is nonnegative. -/
theorem ae_nonneg_of_measure_Iio_zero (hsupp : mu (Iio 0) = 0) :
    ∀ᵐ x ∂mu, 0 ≤ x := by
  rw [ae_iff]
  simpa only [not_le] using hsupp

/-- The Laplace integrand is integrable against a finite spectral measure. -/
theorem integrable_exp_neg_mul (hsupp : mu (Iio 0) = 0) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => Real.exp (-(t * x))) mu := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_nonneg_of_measure_Iio_zero mu hsupp] with x hx
  have : -(t * x) ≤ 0 := by
    have : 0 ≤ t * x := mul_nonneg ht hx
    linarith
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa using Real.exp_le_one_iff.mpr this

/-- **Equation (42).**  Exponential decay of the Laplace transform forbids
spectral weight in the open interval `(0, m)`. -/
theorem measure_Ioo_eq_zero_of_laplace_decay (hsupp : mu (Iio 0) = 0)
    {C m : ℝ}
    (hdecay : ∀ t : ℝ, 0 ≤ t →
      ∫ x, Real.exp (-(t * x)) ∂mu ≤ C * Real.exp (-(m * t))) :
    mu (Ioo 0 m) = 0 := by
  by_contra hpos
  -- exhaust `(0,m)` by the intervals `(0, m - 1/(n+1))`
  have hcover : Ioo (0:ℝ) m = ⋃ n : ℕ, Ioo (0:ℝ) (m - 1 / (n + 1)) := by
    ext x
    constructor
    · rintro ⟨hx0, hxm⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < m - x by linarith)
      exact mem_iUnion.2 ⟨n, ⟨hx0, by linarith⟩⟩
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      have hpos' : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hn2 := hn.2
      exact ⟨hn.1, by linarith⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, mu (Ioo (0:ℝ) (m - 1 / (n + 1))) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hpos (by rw [hcover]; exact measure_iUnion_null hall)
  set b : ℝ := m - 1 / ((n : ℝ) + 1) with hb
  have hbm : b < m := by
    have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simp only [hb]; linarith
  set c : ℝ := (mu (Ioo (0:ℝ) b)).toReal with hc
  have hcpos : 0 < c := ENNReal.toReal_pos hn (measure_ne_top mu _)
  -- the lower bound `c·e^{-tb} ≤ C(t)` for every `t ≥ 0`
  have hlower : ∀ t : ℝ, 0 ≤ t → c * Real.exp (-(t * b)) ≤ ∫ x, Real.exp (-(t * x)) ∂mu := by
    intro t ht
    have hint := integrable_exp_neg_mul mu hsupp ht
    have hmono : ∫ x in Ioo (0:ℝ) b, Real.exp (-(t * b)) ∂mu
        ≤ ∫ x in Ioo (0:ℝ) b, Real.exp (-(t * x)) ∂mu := by
      refine setIntegral_mono_on ((integrable_const _).integrableOn)
        hint.integrableOn measurableSet_Ioo ?_
      intro x hx
      have : -(t * b) ≤ -(t * x) := by
        have : t * x ≤ t * b := by
          exact mul_le_mul_of_nonneg_left (le_of_lt hx.2) ht
        linarith
      exact Real.exp_le_exp.2 this
    have hconst : ∫ _x in Ioo (0:ℝ) b, Real.exp (-(t * b)) ∂mu
        = c * Real.exp (-(t * b)) := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def]
    have hsub : ∫ x in Ioo (0:ℝ) b, Real.exp (-(t * x)) ∂mu
        ≤ ∫ x, Real.exp (-(t * x)) ∂mu := by
      refine setIntegral_le_integral hint ?_
      filter_upwards with x
      exact le_of_lt (Real.exp_pos _)
    rw [← hconst]
    exact le_trans hmono hsub
  -- hence `c ≤ C·e^{-(m-b)t}` for every `t ≥ 0`, and the right side tends to `0`
  have hkey : ∀ t : ℝ, 0 ≤ t → c ≤ C * Real.exp (-((m - b) * t)) := by
    intro t ht
    have h1 := le_trans (hlower t ht) (hdecay t ht)
    have hexp : (0:ℝ) < Real.exp (-(t * b)) := Real.exp_pos _
    have h2 : c ≤ C * Real.exp (-(m * t)) / Real.exp (-(t * b)) := by
      rw [le_div_iff₀ hexp]
      exact h1
    have h3 : C * Real.exp (-(m * t)) / Real.exp (-(t * b))
        = C * Real.exp (-((m - b) * t)) := by
      rw [div_eq_iff (ne_of_gt hexp), mul_assoc, ← Real.exp_add]
      ring_nf
    linarith [h2, h3.le, h3.ge]
  have hdpos : 0 < m - b := by linarith
  have hlim : Tendsto (fun t : ℝ => C * Real.exp (-((m - b) * t))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (m - b) * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hdpos tendsto_id
    have h2 : Tendsto (fun t : ℝ => Real.exp (-((m - b) * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    simpa using h2.const_mul C
  have hle : c ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact hkey t ht
  linarith

/-- With no spectral weight below `m` apart from a null set at `0`, the mean
energy of the state dominates `m` times its total mass. -/
theorem energy_ge_of_gap_support (hsupp : mu (Iio 0) = 0) {m : ℝ}
    (hgap : mu (Ioo 0 m) = 0) (hzero : mu {(0:ℝ)} = 0)
    (hint : Integrable (fun x : ℝ => x) mu) :
    m * (mu univ).toReal ≤ ∫ x, x ∂mu := by
  have hIio : mu (Iio m) = 0 := by
    have hsplit : Iio m ⊆ Iio 0 ∪ ({(0:ℝ)} ∪ Ioo 0 m) := by
      intro x hx
      rcases lt_trichotomy x 0 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by simp [h]))
      · exact Or.inr (Or.inr ⟨h, hx⟩)
    refine measure_mono_null hsplit ?_
    refine measure_union_null hsupp (measure_union_null hzero hgap)
  have hae : ∀ᵐ x ∂mu, m ≤ x := by
    rw [ae_iff]
    simpa only [not_le] using hIio
  have hconst : ∫ _x : ℝ, m ∂mu = (mu univ).toReal * m := by
    rw [integral_const, smul_eq_mul, measureReal_def]
  calc m * (mu univ).toReal = ∫ _x : ℝ, m ∂mu := by rw [hconst]; ring
    _ ≤ ∫ x, x ∂mu := integral_mono_ae (integrable_const m) hint hae

/-- **The composite terminal estimate.**  Exponential clustering of a state
whose spectral measure has no atom at zero forces the mean energy to be at
least `m` times the total mass. -/
theorem energy_ge_of_laplace_decay (hsupp : mu (Iio 0) = 0) {C m : ℝ}
    (hzero : mu {(0:ℝ)} = 0) (hint : Integrable (fun x : ℝ => x) mu)
    (hdecay : ∀ t : ℝ, 0 ≤ t →
      ∫ x, Real.exp (-(t * x)) ∂mu ≤ C * Real.exp (-(m * t))) :
    m * (mu univ).toReal ≤ ∫ x, x ∂mu :=
  energy_ge_of_gap_support mu hsupp
    (measure_Ioo_eq_zero_of_laplace_decay mu hsupp hdecay) hzero hint

end SpectralMeasure

/-! ## Handing the gap to the vacuum-sector machinery -/

open RequestProject.YangMills.VacuumSectorSpectralGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

open scoped InnerProductSpace

/-- The **spectral representation** of the vacuum-orthogonal states of `H`:
for each such state a finite spectral measure on `[0,∞)` whose total mass is
`‖ψ‖²`, whose mean is the energy `re⟪ψ,Hψ⟫`, and which has no atom at `0` (the
vacuum is the unique ground state).  This is the spectral theorem for the
physical Hamiltonian, supplied as data. -/
structure SpectralRepresentation (H : E →ₗ.[ℂ] E) (vac : E) where
  /-- The spectral measure of a state. -/
  spectralMeasure : H.domain → Measure ℝ
  /-- It is a finite measure. -/
  isFinite : ∀ psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 →
    IsFiniteMeasure (spectralMeasure psi)
  /-- It is carried by the nonnegative half-line: the Hamiltonian is positive. -/
  carried : ∀ psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 →
    spectralMeasure psi (Iio 0) = 0
  /-- Its total mass is the squared norm of the state. -/
  total_mass : ∀ psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 →
    ((spectralMeasure psi) univ).toReal = ‖(psi : E)‖ ^ 2
  /-- Its mean is the energy of the state. -/
  mean_energy : ∀ psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 →
    ∫ x, x ∂(spectralMeasure psi) = (⟪(psi : E), H psi⟫_ℂ).re
  /-- The energy is integrable (the state has finite energy). -/
  integrable_energy : ∀ psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 →
    Integrable (fun x : ℝ => x) (spectralMeasure psi)
  /-- A vacuum-orthogonal state has no zero-energy component. -/
  no_zero_mode : ∀ psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 →
    spectralMeasure psi {(0:ℝ)} = 0

/-- The spectral representation together with the **exponential clustering**
estimate delivered by the source side of the BIDI chain. -/
structure ClusteringSpectralData (H : E →ₗ.[ℂ] E) (vac : E) (m : ℝ)
    extends SpectralRepresentation H vac where
  /-- The clustering constant of the state. -/
  clusterConst : H.domain → ℝ
  /-- **Exponential clustering**: the correlation function of a
  vacuum-orthogonal state decays at rate `m`. -/
  clustering : ∀ psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 → ∀ t : ℝ, 0 ≤ t →
    ∫ x, Real.exp (-(t * x)) ∂(toSpectralRepresentation.spectralMeasure psi)
      ≤ clusterConst psi * Real.exp (-(m * t))

/-- **The source-to-terminal weld.**  The source side of the chain delivers a
bound on the continuum covariance at temporal separation `t`; the OS
identification says the correlation function of the state is that covariance.
Together they produce the clustering data that the terminal consumer needs. -/
def ClusteringSpectralData.ofSourceBound {H : E →ₗ.[ℂ] E} {vac : E} {m : ℝ}
    (S : SpectralRepresentation H vac) (covInf : H.domain → ℝ → ℂ)
    (c : H.domain → ℝ)
    (hos : ∀ psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 → ∀ t : ℝ, 0 ≤ t →
      ∫ x, Real.exp (-(t * x)) ∂(S.spectralMeasure psi) ≤ ‖covInf psi t‖)
    (hsrc : ∀ psi : H.domain, ∀ t : ℝ, 0 ≤ t →
      ‖covInf psi t‖ ≤ c psi * Real.exp (-(m * t))) :
    ClusteringSpectralData H vac m where
  toSpectralRepresentation := S
  clusterConst := c
  clustering psi horth t ht := le_trans (hos psi horth t ht) (hsrc psi t ht)

/-- **Clustering ⟹ form gap.**  Equation (43)/(44): if every vacuum-orthogonal
state clusters at rate `m > 0`, the Hamiltonian has the vacuum form gap `m`. -/
theorem hasVacuumFormGap_of_clustering {H : E →ₗ.[ℂ] E} {vac : E} {m : ℝ}
    (D : ClusteringSpectralData H vac m) : HasVacuumFormGap H vac m := by
  intro psi horth
  haveI := D.isFinite psi horth
  have h := energy_ge_of_laplace_decay (D.spectralMeasure psi) (D.carried psi horth)
    (D.no_zero_mode psi horth) (D.integrable_energy psi horth) (D.clustering psi horth)
  rw [D.total_mass psi horth, D.mean_energy psi horth] at h
  exact h

end RequestProject.YangMills.BIDI
