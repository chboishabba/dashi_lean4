/-
# Route `S`: the least-privilege mass-gap cut, assembled

Route `S` derives a positive mass gap of the Osterwalder–Schrader Hamiltonian
from five coordinates, *without* the uniform finite transfer gap `F₁`, without
the varying-carrier transport `F₂`, and without the `P_k`/`E_k` Mosco recovery
system `F₃`:

* `S₁` a source/clustering estimate for the selected literal pair at every
  cutoff (the physical input, displayed as a hypothesis);
* `S₂` the separation coordinate is Euclidean lattice time — proved for the
  literal objects in `RouteS/EuclideanTime.lean`;
* `S₃` the selected observables are literal Wilson loops — constructed in
  `Lattice/WilsonLoop.lean` and used as such in `RouteS/WilsonCovariance.lean`;
* `S₄` convergence of the selected expectations to one continuum state (the
  physical input), whose covariance consequence is proved in
  `RouteS/Covariance.lean`;
* `S₅` the decay coordinate is the spectral coordinate of the *same* `H_OS`
  reconstructed from the same Schwinger family (the same-object input).

What this file adds:

* `laplace_antitone` — the Laplace transform of a spectral measure carried by
  `[0,∞)` is nonincreasing in the Euclidean time;
* `laplace_decay_real_of_nat` — hence exponential decay **at integer
  separations only** already gives exponential decay at every real separation,
  with the same rate and the constant inflated by `e^α`.  This is what lets the
  lattice-native Route `S` input (separations are numbers of lattice time
  steps) feed the continuum spectral argument;
* `RouteSData` — the five coordinates as a single record over a Hilbert space;
* `routeS_vacuum_form_gap` — Route `S` ⟹ `HasVacuumFormGap H_OS Ω α`;
* `routeS_massGapConclusion` — Route `S` together with the standard vacuum data
  (self-adjointness, `H Ω = 0`, `‖Ω‖ = 1`) ⟹ the repository's full
  `MassGapConclusion`: `Spec(H_OS) ⊆ {0} ∪ [α,∞)` in its operator form (no
  eigenvalue in `(0,α)`, unique solvability and the resolvent bound on the
  vacuum complement);
* `routeS_continuum_clustering_of_wilson` — the literal `S₄` half: uniform
  clustering of the literal Wilson-loop covariances plus convergence of the
  three literal Wilson expectations gives the continuum clustering estimate
  that `RouteSData.clustering` asks for.

Nothing here is an axiom, a receipt or a Boolean flag: the physical inputs
`S₁`, `S₄`, `S₅` appear as explicit hypotheses of explicit theorems, and every
step between them is proved.
-/
import Mathlib
import RequestProject.YangMills.BIDI.ClusteringGap
import RequestProject.YangMills.Clay.MassGapAssembly
import RequestProject.YangMills.RouteS.WilsonCovariance

namespace RequestProject.YangMills.RouteS

open MeasureTheory Set Filter Topology
open RequestProject.YangMills.BIDI
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.Clay
open scoped InnerProductSpace ComplexConjugate

/-! ## From integer separations to all real separations -/

variable (mu : Measure ℝ) [IsFiniteMeasure mu]

/-- The Laplace transform of a measure carried by `[0,∞)` is nonincreasing. -/
theorem laplace_antitone (hsupp : mu (Iio 0) = 0) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ x, Real.exp (-(t * x)) ∂mu ≤ ∫ x, Real.exp (-(s * x)) ∂mu := by
  refine integral_mono_ae (integrable_exp_neg_mul mu hsupp (hs.trans hst))
    (integrable_exp_neg_mul mu hsupp hs) ?_
  filter_upwards [ae_nonneg_of_measure_Iio_zero mu hsupp] with x hx
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- **Lattice-native clustering suffices.**  Exponential decay of the Laplace
transform at integer Euclidean separations gives exponential decay at every
real separation, with the same rate `alpha` and constant inflated by `e^alpha`.
-/
theorem laplace_decay_real_of_nat (hsupp : mu (Iio 0) = 0) {C alpha : ℝ}
    (hC : 0 ≤ C) (halpha : 0 ≤ alpha)
    (hnat : ∀ k : ℕ, ∫ x, Real.exp (-((k : ℝ) * x)) ∂mu ≤ C * Real.exp (-(alpha * k))) :
    ∀ t : ℝ, 0 ≤ t →
      ∫ x, Real.exp (-(t * x)) ∂mu ≤ (C * Real.exp alpha) * Real.exp (-(alpha * t)) := by
  intro t ht
  set k : ℕ := ⌊t⌋₊ with hk
  have hkt : (k : ℝ) ≤ t := Nat.floor_le ht
  have htk : t - 1 ≤ (k : ℝ) := by
    have := Nat.lt_floor_add_one t
    linarith
  calc ∫ x, Real.exp (-(t * x)) ∂mu
      ≤ ∫ x, Real.exp (-((k : ℝ) * x)) ∂mu :=
        laplace_antitone mu hsupp (by positivity) hkt
    _ ≤ C * Real.exp (-(alpha * k)) := hnat k
    _ ≤ C * Real.exp (-(alpha * (t - 1))) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
        nlinarith
    _ = (C * Real.exp alpha) * Real.exp (-(alpha * t)) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf

/-! ## The five coordinates of Route `S` -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Route `S` data.**  `H` is the Osterwalder–Schrader Hamiltonian
reconstructed from the continuum Schwinger family, `vac` its vacuum, `spec` the
spectral representation of its vacuum-orthogonal states (`S₅`, the same-object
input), `covInf psi k` the continuum connected covariance of the selected pair
at Euclidean separation `k` lattice steps, `os_same_object` the statement that
the OS correlation function of a state is that covariance (`S₅` again, the
*same* Euclidean family), and `clustering` the continuum clustering estimate
produced by `S₁`–`S₄`. -/
structure RouteSData (H : E →ₗ.[ℂ] E) (vac : E) (alpha : ℝ) where
  /-- The spectral representation of the vacuum-orthogonal states of `H`. -/
  spec : SpectralRepresentation H vac
  /-- The continuum connected covariance at integer Euclidean separation. -/
  covInf : H.domain → ℕ → ℂ
  /-- The clustering constant of the selected pair for the state. -/
  clusterConst : H.domain → ℝ
  /-- The clustering constants are nonnegative. -/
  clusterConst_nonneg : ∀ psi : H.domain, 0 ≤ clusterConst psi
  /-- The rate is positive. -/
  alpha_pos : 0 < alpha
  /-- `S₅`: the OS correlation function of a vacuum-orthogonal state at
  Euclidean separation `k` is the continuum covariance of the selected pair —
  the decay coordinate is the spectral coordinate of this very `H`. -/
  os_same_object : ∀ psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 → ∀ k : ℕ,
    ∫ x, Real.exp (-((k : ℝ) * x)) ∂(spec.spectralMeasure psi) ≤ ‖covInf psi k‖
  /-- `S₁`–`S₄`: the continuum covariance clusters exponentially at rate
  `alpha` at integer Euclidean separations. -/
  clustering : ∀ psi : H.domain, ∀ k : ℕ,
    ‖covInf psi k‖ ≤ clusterConst psi * Real.exp (-(alpha * k))

variable {H : E →ₗ.[ℂ] E} {vac : E} {alpha : ℝ}

/-- The clustering data in the real-time form the terminal spectral consumer
needs, obtained from the lattice-native (integer separation) form. -/
noncomputable def RouteSData.toClusteringSpectralData (D : RouteSData H vac alpha) :
    ClusteringSpectralData H vac alpha where
  toSpectralRepresentation := D.spec
  clusterConst psi := D.clusterConst psi * Real.exp alpha
  clustering psi horth t ht := by
    haveI := D.spec.isFinite psi horth
    exact laplace_decay_real_of_nat _ (D.spec.carried psi horth)
      (D.clusterConst_nonneg psi) D.alpha_pos.le
      (fun k => le_trans (D.os_same_object psi horth k) (D.clustering psi k)) t ht

/-- **Route `S` ⟹ the vacuum form gap of the same `H_OS`.** -/
theorem RouteSData.vacuum_form_gap (D : RouteSData H vac alpha) :
    HasVacuumFormGap H vac alpha :=
  hasVacuumFormGap_of_clustering D.toClusteringSpectralData

/-- **Route `S` ⟹ the Clay mass-gap conclusion for `H_OS`.**  Given the five
Route-`S` coordinates and the standard vacuum data of the reconstructed theory,
the Osterwalder–Schrader Hamiltonian has no spectrum in `(0, alpha)` on the
vacuum complement, in the repository's full operator form. -/
theorem routeS_massGapConclusion [CompleteSpace E] {H : E →ₗ.[ℂ] E} {vac : E} {alpha : ℝ}
    (D : RouteSData H vac alpha) (hmem : vac ∈ H.domain) (hunit : ‖vac‖ = 1)
    (hground : H ⟨vac, hmem⟩ = 0) (hsa : IsSelfAdjoint H) :
    MassGapConclusion H vac alpha :=
  massGapConclusion_of_datum
    { op := H
      vac := vac
      gap := alpha
      vac_mem := hmem
      vac_unit := hunit
      vac_ground := hground
      selfAdjoint := hsa
      gap_pos := D.alpha_pos
      form_gap := D.vacuum_form_gap }

/-! ## The literal `S₄` half on the Wilson family -/

open RequestProject.YangMills.Lattice

/-- **Literal `S₄`.**  Let `size k`, `beta k` be a trajectory of literal Wilson
theories and let the selected pair be literal Wilson loops.  If every finite
covariance of the translated pair obeys the clustering bound (`S₁`–`S₃`), and
the three literal Wilson expectations converge to continuum values (`S₄`), then
the continuum connected covariance obeys the same bound.  No `P_k`, no `E_k`,
no Mosco recovery. -/
theorem routeS_continuum_clustering_of_wilson {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] {size : ℕ → ℕ} {beta : ℕ → ℝ} {chi : G → ℝ}
    {xs ys : ∀ k, Site (size k)} {ps qs : ∀ _ : ℕ, List Step}
    {abI aI bI : ℕ → ℂ} {C alpha : ℝ}
    (hab : ∀ t : ℕ, Tendsto (fun k => ∫ U, conj (loopObs chi (xs k) (ps k) U) *
        loopObs chi (ys k + timeVec (size k) t) (qs k) U ∂(gibbs (size k) G (beta k) chi))
      atTop (𝓝 (abI t)))
    (ha : ∀ t : ℕ, Tendsto (fun k => ∫ U, loopObs chi (xs k) (ps k) U
        ∂(gibbs (size k) G (beta k) chi)) atTop (𝓝 (aI t)))
    (hb : ∀ t : ℕ, Tendsto (fun k => ∫ U, loopObs chi (ys k + timeVec (size k) t) (qs k) U
        ∂(gibbs (size k) G (beta k) chi)) atTop (𝓝 (bI t)))
    (hfin : ∀ k t : ℕ,
      ‖loopCov (size k) G (beta k) chi (xs k) (ys k) (ps k) (qs k) t‖
        ≤ C * Real.exp (-(alpha * t))) :
    ∀ t : ℕ, ‖connected (abI t) (aI t) (bI t)‖ ≤ C * Real.exp (-(alpha * t)) := by
  refine continuum_clustering_of_expectation_limits hab ha hb ?_
  intro k t
  have := hfin k t
  rwa [loopCov_eq_connected] at this

/-- **Route `S` end to end on the literal Wilson family.**  Inputs: the finite
clustering estimate for the selected literal Wilson-loop pair at every cutoff
(`S₁`–`S₃`), convergence of the three literal Wilson expectations at every
Euclidean separation (`S₄`), and a spectral representation of the reconstructed
Osterwalder–Schrader Hamiltonian whose correlation function is that same
continuum covariance (`S₅`).  Output: the full Clay-form mass-gap conclusion for
`H_OS` at the clustering rate. -/
theorem wilson_routeS_massGapConclusion {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] {size : ℕ → ℕ} {beta : ℕ → ℝ} {chi : G → ℝ}
    {xs ys : ∀ k, Site (size k)} {ps qs : ∀ _ : ℕ, List Step}
    {abI aI bI : ℕ → ℂ} {C alpha : ℝ} (halpha : 0 < alpha)
    (hab : ∀ t : ℕ, Tendsto (fun k => ∫ U, conj (loopObs chi (xs k) (ps k) U) *
        loopObs chi (ys k + timeVec (size k) t) (qs k) U ∂(gibbs (size k) G (beta k) chi))
      atTop (𝓝 (abI t)))
    (ha : ∀ t : ℕ, Tendsto (fun k => ∫ U, loopObs chi (xs k) (ps k) U
        ∂(gibbs (size k) G (beta k) chi)) atTop (𝓝 (aI t)))
    (hb : ∀ t : ℕ, Tendsto (fun k => ∫ U, loopObs chi (ys k + timeVec (size k) t) (qs k) U
        ∂(gibbs (size k) G (beta k) chi)) atTop (𝓝 (bI t)))
    (hfin : ∀ k t : ℕ,
      ‖loopCov (size k) G (beta k) chi (xs k) (ys k) (ps k) (qs k) t‖
        ≤ C * Real.exp (-(alpha * t)))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {H : E →ₗ.[ℂ] E} {vac : E} (spec : SpectralRepresentation H vac)
    (hos : ∀ psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 → ∀ k : ℕ,
      ∫ x, Real.exp (-((k : ℝ) * x)) ∂(spec.spectralMeasure psi)
        ≤ ‖(psi : E)‖ ^ 2 * ‖connected (abI k) (aI k) (bI k)‖)
    (hmem : vac ∈ H.domain) (hunit : ‖vac‖ = 1) (hground : H ⟨vac, hmem⟩ = 0)
    (hsa : IsSelfAdjoint H) :
    MassGapConclusion H vac alpha := by
  have hclust : ∀ t : ℕ, ‖connected (abI t) (aI t) (bI t)‖ ≤ C * Real.exp (-(alpha * t)) :=
    routeS_continuum_clustering_of_wilson hab ha hb hfin
  have hC0 : (0 : ℝ) ≤ C := by
    have h0 : ‖connected (abI 0) (aI 0) (bI 0)‖ ≤ C := by simpa using hclust 0
    exact le_trans (norm_nonneg _) h0
  have hnorm : ∀ (psi : H.domain) (k : ℕ),
      ‖((‖(psi : E)‖ ^ 2 : ℝ) : ℂ) * connected (abI k) (aI k) (bI k)‖
        = ‖(psi : E)‖ ^ 2 * ‖connected (abI k) (aI k) (bI k)‖ := by
    intro psi k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine routeS_massGapConclusion
    (D := { spec := spec
            covInf := fun psi k =>
              ((‖(psi : E)‖ ^ 2 : ℝ) : ℂ) * connected (abI k) (aI k) (bI k)
            clusterConst := fun psi => ‖(psi : E)‖ ^ 2 * C
            clusterConst_nonneg := fun psi => by positivity
            alpha_pos := halpha
            os_same_object := by
              intro psi horth k
              rw [hnorm psi k]
              exact hos psi horth k
            clustering := by
              intro psi k
              rw [hnorm psi k, mul_assoc]
              exact mul_le_mul_of_nonneg_left (hclust k) (by positivity) })
    hmem hunit hground hsa


end RequestProject.YangMills.RouteS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.RouteS

#print axioms laplace_antitone
#print axioms laplace_decay_real_of_nat
#print axioms RouteSData.vacuum_form_gap
#print axioms routeS_massGapConclusion
#print axioms routeS_continuum_clustering_of_wilson
#print axioms wilson_routeS_massGapConclusion

end Audit
