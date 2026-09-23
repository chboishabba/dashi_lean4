/-
# The continuum limit functional of the literal Wilson expectations exists

Route `S` (see `RouteS/Assembly.lean`) consumes two physical inputs about the
literal finite-spacing Yang–Mills theory:

* `S₁` a clustering estimate for the literal Wilson covariance, **uniform in the
  cutoff**;
* `S₄` *convergence* of the selected finite expectations to one continuum
  state.

This file removes `S₄` as a hypothesis.  For **any** countable family of
uniformly bounded continuous observables attached to **any** sequence of Wilson
cutoffs (lattice size and coupling both allowed to vary arbitrarily), there is a
subsequence of cutoffs along which *every* selected expectation converges, and
the limit functional is automatically

* bounded by the same constant,
* normalised (the unit observable has limit `1`),
* positive (pointwise nonnegative observables have nonnegative limits),
* linear (every pointwise affine relation between the selected observables that
  holds at every cutoff holds for the limits).

Nothing here is postulated: the extraction is compactness of a countable product
of closed discs (`exists_subseq_tendsto_family`), and the three functional
properties are the corresponding properties of the literal Wilson–Gibbs integral
pushed through the limit.

What is *not* claimed, and what remains the genuine mathematical frontier: the
limit functional produced here is a positive normalised functional on the chosen
countable family only; it is obtained along a subsequence, so it is not shown to
be unique or independent of the subsequence, it is not shown to be represented
by a measure on a continuum configuration space, and no nontriviality of the
limit is asserted.  The surviving physical input of Route `S` is the
cutoff-uniform clustering estimate `S₁`, for which see
`RouteS/UniformityObstruction.lean` and `RouteS/PhysicalSeparation.lean`.

The capstone `exists_subseq_continuum_clustering` makes the gain precise: given
only the uniform clustering estimate — with no convergence hypothesis at all —
there is a subsequence of cutoffs along which the continuum covariance of the
selected pair exists and obeys the same exponential bound.
-/
import Mathlib
import RequestProject.YangMills.RouteS.WilsonCovariance
import RequestProject.YangMills.RouteS.Covariance

namespace RequestProject.YangMills.Continuum

open Filter Topology MeasureTheory
open RequestProject.YangMills.Lattice
open RequestProject.YangMills.RouteS
open scoped ComplexConjugate

/-! ## Compactness: a uniformly bounded countable array has a convergent
subsequence -/

/-- **Diagonal extraction.**  A countable family of complex sequences, all
bounded by one constant `M`, converges simultaneously along one subsequence.
This is compactness of `∏_j closedBall 0 M` in the product topology; the index
type only has to be countable. -/
theorem exists_subseq_tendsto_family {ι : Type*} [Countable ι] (E : ℕ → ι → ℂ) {M : ℝ}
    (hM : ∀ k j, ‖E k j‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : ι → ℂ, (∀ j, ‖L j‖ ≤ M) ∧
      ∀ j, Tendsto (fun k => E (φ k) j) atTop (𝓝 (L j)) := by
  have hcomp : IsCompact (Set.univ.pi fun _ : ι => Metric.closedBall (0 : ℂ) M) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hmem : ∀ k : ℕ, E k ∈ Set.univ.pi fun _ : ι => Metric.closedBall (0 : ℂ) M := by
    intro k j _
    simpa [Metric.mem_closedBall] using hM k j
  obtain ⟨L, hL, φ, hφ, hconv⟩ := hcomp.tendsto_subseq hmem
  exact ⟨φ, hφ, L, fun j => by simpa [Metric.mem_closedBall] using hL j (Set.mem_univ j),
    fun j => (continuous_apply j).continuousAt.tendsto.comp hconv⟩

/-! ## Transfer of the state properties to a limit -/

/-- A value that is constant along the sequence is the limit. -/
theorem limit_eq_of_forall_eq {f : ℕ → ℂ} {L c : ℂ} (hconv : Tendsto f atTop (𝓝 L))
    (hc : ∀ k, f k = c) : L = c := by
  refine tendsto_nhds_unique hconv ?_
  rw [show f = fun _ : ℕ => c from funext hc]
  exact tendsto_const_nhds

/-- Nonnegativity of the real parts passes to the limit. -/
theorem limit_re_nonneg {f : ℕ → ℂ} {L : ℂ} (hconv : Tendsto f atTop (𝓝 L))
    (h : ∀ k, 0 ≤ (f k).re) : 0 ≤ L.re :=
  ge_of_tendsto' (Complex.continuous_re.continuousAt.tendsto.comp hconv) h

/-- An affine relation holding at every cutoff holds for the limits. -/
theorem limit_affine {f g h : ℕ → ℂ} {Lf Lg Lh a b : ℂ} (hf : Tendsto f atTop (𝓝 Lf))
    (hg : Tendsto g atTop (𝓝 Lg)) (hh : Tendsto h atTop (𝓝 Lh))
    (hrel : ∀ k, h k = a * f k + b * g k) : Lh = a * Lf + b * Lg := by
  refine tendsto_nhds_unique hh ?_
  rw [show h = fun k => a * f k + b * g k from funext hrel]
  exact (tendsto_const_nhds.mul hf).add (tendsto_const_nhds.mul hg)

/-! ## Wilson cutoff schedules -/

variable {ι : Type*}
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

/-- A **cutoff schedule**: a sequence of literal Wilson theories (lattice size
and inverse coupling both varying) together with a countable family of
uniformly bounded measurable observables attached to each of them.  No relation
between the lattices at different cutoffs is assumed. -/
structure CutoffSchedule (ι : Type*) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] where
  /-- the lattice size at cutoff `k` -/
  size : ℕ → ℕ
  /-- the inverse coupling at cutoff `k` -/
  beta : ℕ → ℝ
  /-- the class function defining the Wilson action -/
  chi : G → ℝ
  /-- the selected observables -/
  obs : (k : ℕ) → ι → Conf (size k) G → ℂ
  /-- the common bound -/
  bound : ℝ
  /-- the class function is continuous -/
  continuous_chi : Continuous chi
  /-- the observables are measurable -/
  measurable_obs : ∀ k j, Measurable (obs k j)
  /-- the observables are uniformly bounded -/
  norm_obs_le : ∀ k j U, ‖obs k j U‖ ≤ bound

namespace CutoffSchedule

variable (S : CutoffSchedule ι G)

/-- The literal Wilson–Gibbs expectation of the selected observable `j` at the
cutoff `k`. -/
noncomputable def expect (k : ℕ) (j : ι) : ℂ :=
  ∫ U, S.obs k j U ∂(gibbs (S.size k) G (S.beta k) S.chi)

theorem integrable_obs (k : ℕ) (j : ι) :
    Integrable (S.obs k j) (gibbs (S.size k) G (S.beta k) S.chi) := by
  haveI := isProbabilityMeasure_gibbs (n := S.size k) (G := G) S.continuous_chi (S.beta k)
  exact Integrable.mono' (integrable_const S.bound) (S.measurable_obs k j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun U => S.norm_obs_le k j U)

/-- The expectations are bounded by the same constant as the observables, at
every cutoff. -/
theorem norm_expect_le (k : ℕ) (j : ι) : ‖S.expect k j‖ ≤ S.bound := by
  haveI := isProbabilityMeasure_gibbs (n := S.size k) (G := G) S.continuous_chi (S.beta k)
  simpa [expect] using norm_integral_le_of_norm_le_const
    (μ := gibbs (S.size k) G (S.beta k) S.chi) (f := S.obs k j) (C := S.bound)
    (Filter.Eventually.of_forall fun U => S.norm_obs_le k j U)

/-- Normalisation at a fixed cutoff: the unit observable has expectation `1`. -/
theorem expect_eq_one {k : ℕ} {j : ι} (h : ∀ U, S.obs k j U = 1) : S.expect k j = 1 := by
  haveI := isProbabilityMeasure_gibbs (n := S.size k) (G := G) S.continuous_chi (S.beta k)
  simp [expect, h]

/-- Positivity at a fixed cutoff: a pointwise nonnegative observable has
nonnegative expectation.  This is the literal Wilson–Gibbs integral, not a
formal functional. -/
theorem expect_re_nonneg {k : ℕ} {j : ι} (h : ∀ U, 0 ≤ (S.obs k j U).re) :
    0 ≤ (S.expect k j).re := by
  haveI := isProbabilityMeasure_gibbs (n := S.size k) (G := G) S.continuous_chi (S.beta k)
  rw [expect, ← Complex.reCLM_apply,
    ← ContinuousLinearMap.integral_comp_comm _ (S.integrable_obs k j)]
  exact integral_nonneg h

/-- Linearity at a fixed cutoff. -/
theorem expect_affine {k : ℕ} {i j l : ι} {a b : ℂ}
    (h : ∀ U, S.obs k l U = a * S.obs k i U + b * S.obs k j U) :
    S.expect k l = a * S.expect k i + b * S.expect k j := by
  haveI := isProbabilityMeasure_gibbs (n := S.size k) (G := G) S.continuous_chi (S.beta k)
  have hadd := integral_add (μ := gibbs (S.size k) G (S.beta k) S.chi)
    ((S.integrable_obs k i).const_mul a) ((S.integrable_obs k j).const_mul b)
  simp only [expect]
  rw [show S.obs k l = fun U => a * S.obs k i U + b * S.obs k j U from funext h, hadd,
    integral_const_mul, integral_const_mul]

end CutoffSchedule

/-! ## The limit functional -/

/-- **Existence of the continuum limit functional, unconditionally.**

For an arbitrary sequence of literal Wilson cutoffs and an arbitrary countable
family of uniformly bounded continuous observables there is a subsequence of
cutoffs along which every selected expectation converges; the limit functional
`L` is bounded by the same constant, normalised, positive and linear.

The convergence input `S₄` of Route `S` is therefore not an extra physical
assumption: it holds along a subsequence for purely compactness reasons. -/
theorem exists_limit_functional [Countable ι] (S : CutoffSchedule ι G) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : ι → ℂ,
      (∀ j, Tendsto (fun k => S.expect (φ k) j) atTop (𝓝 (L j))) ∧
      (∀ j, ‖L j‖ ≤ S.bound) ∧
      (∀ j, (∀ k U, S.obs k j U = 1) → L j = 1) ∧
      (∀ j, (∀ k U, 0 ≤ (S.obs k j U).re) → 0 ≤ (L j).re) ∧
      (∀ (a b : ℂ) (i j l : ι),
        (∀ k U, S.obs k l U = a * S.obs k i U + b * S.obs k j U) →
        L l = a * L i + b * L j) := by
  obtain ⟨φ, hφ, L, hLbd, hconv⟩ :=
    exists_subseq_tendsto_family (fun k j => S.expect k j) (fun k j => S.norm_expect_le k j)
  refine ⟨φ, hφ, L, hconv, hLbd, ?_, ?_, ?_⟩
  · intro j h
    exact limit_eq_of_forall_eq (hconv j) fun k => S.expect_eq_one (h (φ k))
  · intro j h
    exact limit_re_nonneg (hconv j) fun k => S.expect_re_nonneg (h (φ k))
  · intro a b i j l h
    exact limit_affine (hconv i) (hconv j) (hconv l) fun k => S.expect_affine (h (φ k))

/-! ## Capstone: clustering of the continuum covariance with no convergence
hypothesis -/

/-- **Uniform clustering alone gives a clustering continuum covariance.**

Let a cutoff schedule carry, for every Euclidean separation `t`, the three
observables entering the connected covariance of a selected pair: the product
`ab t` and the two single loops `aObs t`, `bObs t`.  Assume only the
cutoff-uniform exponential bound on the finite connected covariances (the
Route-`S` input `S₁`).  Then there is a subsequence of cutoffs along which all
three expectation families converge and the resulting continuum connected
covariance obeys the same exponential bound, with the same constant and rate.

No convergence assumption is made: the limit is produced by
`exists_limit_functional`. -/
theorem exists_subseq_continuum_clustering [Countable ι] (S : CutoffSchedule ι G)
    (ab aObs bObs : ℕ → ι) {C alpha : ℝ}
    (hcluster : ∀ k t, ‖connected (S.expect k (ab t)) (S.expect k (aObs t))
        (S.expect k (bObs t))‖ ≤ C * Real.exp (-(alpha * t))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ abInf aInf bInf : ℕ → ℂ,
      (∀ t, Tendsto (fun k => S.expect (φ k) (ab t)) atTop (𝓝 (abInf t))) ∧
      (∀ t, Tendsto (fun k => S.expect (φ k) (aObs t)) atTop (𝓝 (aInf t))) ∧
      (∀ t, Tendsto (fun k => S.expect (φ k) (bObs t)) atTop (𝓝 (bInf t))) ∧
      ∀ t, ‖connected (abInf t) (aInf t) (bInf t)‖ ≤ C * Real.exp (-(alpha * t)) := by
  obtain ⟨φ, hφ, L, hconv, -, -, -, -⟩ := exists_limit_functional S
  refine ⟨φ, hφ, fun t => L (ab t), fun t => L (aObs t), fun t => L (bObs t),
    fun t => hconv (ab t), fun t => hconv (aObs t), fun t => hconv (bObs t), ?_⟩
  exact continuum_clustering_of_expectation_limits
    (abF := fun k t => S.expect (φ k) (ab t)) (aF := fun k t => S.expect (φ k) (aObs t))
    (bF := fun k t => S.expect (φ k) (bObs t))
    (fun t => hconv (ab t)) (fun t => hconv (aObs t)) (fun t => hconv (bObs t))
    (fun k t => hcluster (φ k) t)

end RequestProject.YangMills.Continuum

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Continuum

#print axioms exists_subseq_tendsto_family
#print axioms CutoffSchedule.expect_re_nonneg
#print axioms CutoffSchedule.expect_affine
#print axioms exists_limit_functional
#print axioms exists_subseq_continuum_clustering

end Audit
