/-
# `S₄`: connected covariance and the continuum expectation limit

Route `S` takes as its physical input a *uniform finite clustering estimate*

    |Cov_k(A, τ_t B)| ≤ C · e^{-α t}

for the literal Wilson–Gibbs states, together with convergence of the selected
expectations to one continuum state.  The step from those two inputs to a
continuum clustering estimate is pure compiler mathematics, and this file
proves it.

* `connected` — the algebraic connected part `⟨A*B⟩ − conj⟨A⟩⟨B⟩`;
* `cov` — the connected covariance of two observables in a state (a measure),
  `cov_eq_connected` identifies it with `connected` of the three expectations;
* `cov_eq_integral_centered` — the covariance is the expectation of the product
  of the centred observables (for a probability state and integrable data);
* `cov_self_nonneg`, `cov_conj` — positivity of the variance and conjugate
  symmetry;
* `tendsto_connected` — **the covariance-limit algebra**: convergence of the
  three expectations gives convergence of the covariance;
* `norm_le_of_tendsto_of_eventually_le` — a uniform bound survives the limit;
* `continuum_clustering_of_finite_clustering` — the composite: a uniform finite
  clustering estimate plus expectation convergence at each separation `t` gives
  the same exponential clustering estimate for the continuum state.  No
  `P_k`/`E_k` recovery system and no Mosco convergence is used.

The literal specialisation to the Wilson–Gibbs family and its Wilson-loop
observables is in `RouteS/WilsonCovariance.lean`.
-/
import Mathlib

namespace RequestProject.YangMills.RouteS

open MeasureTheory Filter Topology
open scoped ComplexConjugate

/-! ## The connected part -/

/-- The connected part of a pair of expectations: `⟨A*B⟩ − conj⟨A⟩·⟨B⟩`. -/
def connected (ab a b : ℂ) : ℂ := ab - conj a * b

/-- The connected covariance of `A` and `B` in the state `mu`. -/
noncomputable def cov {X : Type*} [MeasurableSpace X] (mu : Measure X) (A B : X → ℂ) : ℂ :=
  ∫ x, conj (A x) * B x ∂mu - conj (∫ x, A x ∂mu) * ∫ x, B x ∂mu

variable {X : Type*} [MeasurableSpace X]

theorem cov_eq_connected (mu : Measure X) (A B : X → ℂ) :
    cov mu A B = connected (∫ x, conj (A x) * B x ∂mu) (∫ x, A x ∂mu) (∫ x, B x ∂mu) := rfl

/-- Conjugation preserves integrability. -/
theorem integrable_conj {mu : Measure X} {A : X → ℂ} (hA : Integrable A mu) :
    Integrable (fun x => conj (A x)) mu := by
  refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hA.1, ?_⟩
  simpa [hasFiniteIntegral_iff_enorm] using hA.2

/-- The covariance is the expectation of the product of the centred
observables. -/
theorem cov_eq_integral_centered (mu : Measure X) [IsProbabilityMeasure mu] {A B : X → ℂ}
    (hA : Integrable A mu) (hB : Integrable B mu)
    (hAB : Integrable (fun x => conj (A x) * B x) mu) :
    cov mu A B =
      ∫ x, conj (A x - ∫ y, A y ∂mu) * (B x - ∫ y, B y ∂mu) ∂mu := by
  set a := ∫ y, A y ∂mu with ha_def
  set b := ∫ y, B y ∂mu with hb_def
  have hcA : Integrable (fun x => conj (A x)) mu := integrable_conj hA
  have h1 : Integrable (fun x => conj (A x) * b) mu := hcA.mul_const b
  have h2 : Integrable (fun x => conj a * B x) mu := hB.const_mul _
  have h12 : Integrable (fun x => conj (A x) * B x - conj (A x) * b) mu := hAB.sub h1
  have h123 : Integrable
      (fun x => conj (A x) * B x - conj (A x) * b - conj a * B x) mu := h12.sub h2
  have hexp : ∀ x, conj (A x - a) * (B x - b)
      = (conj (A x) * B x - conj (A x) * b - conj a * B x) + conj a * b := by
    intro x
    simp only [map_sub]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
    integral_add h123 (integrable_const _), integral_sub h12 h2, integral_sub hAB h1,
    integral_mul_const, integral_const_mul, integral_const, integral_conj]
  have hone : mu.real Set.univ = 1 := by simp
  rw [hone, one_smul]
  simp only [cov, ← ha_def, ← hb_def]
  ring

/-- The variance of an observable is a nonnegative real. -/
theorem cov_self_nonneg (mu : Measure X) [IsProbabilityMeasure mu] {A : X → ℂ}
    (hA : Integrable A mu) (hAA : Integrable (fun x => conj (A x) * A x) mu) :
    0 ≤ (cov mu A A).re := by
  rw [cov_eq_integral_centered mu hA hA hAA]
  have h : ∀ x, conj (A x - ∫ y, A y ∂mu) * (A x - ∫ y, A y ∂mu)
      = ((‖A x - ∫ y, A y ∂mu‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [integral_congr_ae (Filter.Eventually.of_forall h), integral_complex_ofReal,
    Complex.ofReal_re]
  exact integral_nonneg fun x => by positivity

/-! ## The covariance-limit algebra (`S₄`) -/

variable {ι : Type*} {l : Filter ι}

/-- **The covariance limit is the limit of the covariances.**  This is the
compiler-owned half of `S₄`: given convergence of the three selected
expectations, the connected covariance converges. -/
theorem tendsto_connected {ab a b : ι → ℂ} {abInf aInf bInf : ℂ}
    (hab : Tendsto ab l (𝓝 abInf)) (ha : Tendsto a l (𝓝 aInf))
    (hb : Tendsto b l (𝓝 bInf)) :
    Tendsto (fun k => connected (ab k) (a k) (b k)) l (𝓝 (connected abInf aInf bInf)) :=
  hab.sub ((Complex.continuous_conj.tendsto _ |>.comp ha).mul hb)

/-- A bound that holds eventually along the filter survives the limit. -/
theorem norm_le_of_tendsto_of_eventually_le [l.NeBot] {c : ι → ℂ} {cInf : ℂ} {M : ℝ}
    (hc : Tendsto c l (𝓝 cInf)) (hb : ∀ᶠ k in l, ‖c k‖ ≤ M) : ‖cInf‖ ≤ M :=
  le_of_tendsto (hc.norm) hb

/-- **Uniform finite clustering plus expectation convergence gives continuum
clustering.**  `covFinite k t` is the connected covariance of the selected pair
at Euclidean separation `t` and cutoff `k`; `covInf t` is the corresponding
continuum covariance.  If every finite covariance obeys the exponential bound
and the finite covariances converge to the continuum ones, the continuum state
obeys the same bound. -/
theorem continuum_clustering_of_finite_clustering [l.NeBot] {covFinite : ι → ℕ → ℂ}
    {covInf : ℕ → ℂ} {C alpha : ℝ}
    (hlim : ∀ t : ℕ, Tendsto (fun k => covFinite k t) l (𝓝 (covInf t)))
    (hfin : ∀ k : ι, ∀ t : ℕ, ‖covFinite k t‖ ≤ C * Real.exp (-(alpha * t))) :
    ∀ t : ℕ, ‖covInf t‖ ≤ C * Real.exp (-(alpha * t)) := fun t =>
  norm_le_of_tendsto_of_eventually_le (hlim t) (Filter.Eventually.of_forall fun k => hfin k t)

/-- The same statement in the form the continuum consumer wants: the continuum
covariance, viewed as a function of a real separation taken from the lattice
values, decays exponentially. -/
theorem continuum_clustering_of_expectation_limits [l.NeBot]
    {abF : ι → ℕ → ℂ} {aF bF : ι → ℕ → ℂ} {abI aI bI : ℕ → ℂ} {C alpha : ℝ}
    (hab : ∀ t, Tendsto (fun k => abF k t) l (𝓝 (abI t)))
    (ha : ∀ t, Tendsto (fun k => aF k t) l (𝓝 (aI t)))
    (hb : ∀ t, Tendsto (fun k => bF k t) l (𝓝 (bI t)))
    (hfin : ∀ k t, ‖connected (abF k t) (aF k t) (bF k t)‖ ≤ C * Real.exp (-(alpha * t))) :
    ∀ t : ℕ, ‖connected (abI t) (aI t) (bI t)‖ ≤ C * Real.exp (-(alpha * t)) :=
  continuum_clustering_of_finite_clustering
    (covFinite := fun k t => connected (abF k t) (aF k t) (bF k t))
    (fun t => tendsto_connected (hab t) (ha t) (hb t)) hfin

end RequestProject.YangMills.RouteS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.RouteS

#print axioms cov_eq_integral_centered
#print axioms cov_self_nonneg
#print axioms tendsto_connected
#print axioms continuum_clustering_of_finite_clustering
#print axioms continuum_clustering_of_expectation_limits

end Audit
