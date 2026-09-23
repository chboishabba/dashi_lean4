/-
# Route `S` in physical units, and why the lattice-unit form is the wrong cut

`RouteS/Assembly.lean` states the clustering input of Route `S` in **lattice
steps**: one pair `(C, alpha)` valid at every cutoff `k`, bounding the
covariance at separation `t` lattice steps by `C e^{-alpha t}`.  As soon as one
actually takes a continuum limit — lattice spacings `a k → 0` — that hypothesis
is the wrong one, and this file proves it:

* `physical_rate_unbounded_of_lattice_uniform_clustering` — if a covariance
  family obeys a **cutoff-independent** exponential bound in lattice steps and
  the spacings tend to `0`, then at every *fixed physical* separation `s > 0`
  the covariance is eventually smaller than `C e^{alpha} e^{-m s}` for **every**
  rate `m`.  The limiting theory therefore has zero correlation length: the
  hypothesis is satisfiable only by an ultralocal limit, and the `alpha` it
  delivers is an inverse lattice spacing (`RouteS/Calibration.lean`:
  `m = ħ alpha / (c a)`), not a physical mass.

So the correct Route-`S` input indexes separations physically, `t_k(s) =
⌊s / a_k⌋`, with a bound `C e^{-m s}` whose rate `m` is a physical inverse
length.  The rest of this file rebuilds Route `S` in exactly that form:

* `latticeSteps` — the number of lattice time steps representing a physical
  separation at a given spacing;
* `continuum_clustering_physical` — uniform-in-cutoff clustering at physical
  separations plus convergence of the covariances gives continuum clustering at
  the same physical rate;
* `wilson_continuum_clustering_physical` — the same on the literal Wilson
  family, from the three literal expectations;
* `RouteSPhysicalData`, `RouteSPhysicalData.massGapConclusion` — the five
  Route-`S` coordinates in physical units and the resulting Clay-form mass-gap
  conclusion, now with a gap that is a physical inverse correlation length;
* `wilson_routeS_physical_massGapConclusion` — end to end on the literal Wilson
  family.

The physical input is unchanged in nature (a uniform-in-cutoff clustering
estimate and the same-object OS identification are still hypotheses); what
changes is that the estimate is now stated at fixed physical separation, where
it is not self-defeating.
-/
import Mathlib
import RequestProject.YangMills.RouteS.Assembly
import RequestProject.YangMills.RouteS.UniformityObstruction

namespace RequestProject.YangMills.RouteS

open MeasureTheory Set Filter Topology
open RequestProject.YangMills.BIDI
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.Clay
open scoped InnerProductSpace ComplexConjugate

/-- The number of lattice time steps representing the physical separation `s`
at lattice spacing `a`. -/
noncomputable def latticeSteps (a s : ℝ) : ℕ := ⌊s / a⌋₊

theorem latticeSteps_ge (a s : ℝ) : s / a - 1 ≤ (latticeSteps a s : ℝ) := by
  have := Nat.lt_floor_add_one (s / a)
  simp only [latticeSteps]
  linarith

/-! ## The lattice-unit hypothesis trivialises the continuum limit -/

/-- **A cutoff-independent clustering rate in lattice units forces an infinite
physical rate.**  If `‖cov k t‖ ≤ C e^{-alpha t}` at every cutoff `k` and every
number `t` of lattice steps, and the spacings `a k` tend to `0`, then for every
physical separation `s > 0` and every rate `m` — however large — the covariance
at the lattice separation representing `s` is eventually bounded by
`C e^{alpha} e^{-m s}`.

In other words such a family has no finite continuum correlation length; the
hypothesis cannot be met by a theory with a finite, nonzero mass gap in physical
units.  This is why Route `S` must be stated at fixed physical separation. -/
theorem physical_rate_unbounded_of_lattice_uniform_clustering
    {cov : ℕ → ℕ → ℂ} {a : ℕ → ℝ} {C alpha : ℝ}
    (hC : 0 ≤ C) (halpha : 0 < alpha) (hapos : ∀ k, 0 < a k)
    (ha0 : Tendsto a atTop (𝓝 0))
    (hfin : ∀ k t : ℕ, ‖cov k t‖ ≤ C * Real.exp (-(alpha * t))) :
    ∀ m s : ℝ, 0 < s → ∀ᶠ k in atTop,
      ‖cov k (latticeSteps (a k) s)‖ ≤ (C * Real.exp alpha) * Real.exp (-(m * s)) := by
  intro m s hs
  set M : ℝ := max m 1 with hM
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsmall : ∀ᶠ k in atTop, a k < alpha / M := by
    have hpos : 0 < alpha / M := div_pos halpha hMpos
    have := ha0.eventually (gt_mem_nhds hpos)
    exact this
  filter_upwards [hsmall] with k hk
  have hak : 0 < a k := hapos k
  have hratio : M ≤ alpha / a k := by
    rw [le_div_iff₀ hak]
    have : a k * M < (alpha / M) * M := by
      exact (mul_lt_mul_of_pos_right hk hMpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hMpos)] at this
    linarith
  have hmle : m * s ≤ alpha * (s / a k) := by
    have h1 : m ≤ alpha / a k := le_trans (le_max_left _ _) hratio
    have : m * s ≤ (alpha / a k) * s := mul_le_mul_of_nonneg_right h1 hs.le
    calc m * s ≤ (alpha / a k) * s := this
      _ = alpha * (s / a k) := by field_simp
  have hstep : alpha * (s / a k) - alpha ≤ alpha * (latticeSteps (a k) s : ℝ) := by
    have h := latticeSteps_ge (a k) s
    nlinarith [halpha.le]
  calc ‖cov k (latticeSteps (a k) s)‖
      ≤ C * Real.exp (-(alpha * (latticeSteps (a k) s : ℝ))) := hfin k _
    _ ≤ C * Real.exp (-(m * s) + alpha) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
        linarith
    _ = (C * Real.exp alpha) * Real.exp (-(m * s)) := by
        rw [Real.exp_add]; ring

/-! ## Route `S` at physical separations -/

variable {ι : Type*} {l : Filter ι}

/-- **The `S₄` compiler in physical units.**  If the covariance at the lattice
separation representing the physical separation `s` obeys the bound
`C e^{-m s}` uniformly in the cutoff, and converges as the cutoff is removed,
the continuum covariance obeys the same bound at every physical separation. -/
theorem continuum_clustering_physical [l.NeBot] {a : ι → ℝ} {covF : ι → ℕ → ℂ} {covI : ℝ → ℂ}
    {C m : ℝ}
    (hlim : ∀ s : ℝ, Tendsto (fun k => covF k (latticeSteps (a k) s)) l (𝓝 (covI s)))
    (hfin : ∀ (k : ι) (s : ℝ), 0 ≤ s →
      ‖covF k (latticeSteps (a k) s)‖ ≤ C * Real.exp (-(m * s))) :
    ∀ s : ℝ, 0 ≤ s → ‖covI s‖ ≤ C * Real.exp (-(m * s)) := by
  intro s hs
  exact norm_le_of_tendsto_of_eventually_le (hlim s)
    (Filter.Eventually.of_forall fun k => hfin k s hs)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Route `S` data in physical units.**  Identical to `RouteSData` except
that the Euclidean separation is a physical length and the rate `m` is a
physical inverse length — the quantity that `RouteS/Calibration.lean` converts
into a mass. -/
structure RouteSPhysicalData (H : E →ₗ.[ℂ] E) (vac : E) (m : ℝ) where
  /-- The spectral representation of the vacuum-orthogonal states of `H`. -/
  spec : SpectralRepresentation H vac
  /-- The continuum connected covariance at physical Euclidean separation. -/
  covInf : H.domain → ℝ → ℂ
  /-- The clustering constant of the selected pair for the state. -/
  clusterConst : H.domain → ℝ
  /-- The physical rate is positive. -/
  m_pos : 0 < m
  /-- `S₅`: the OS correlation function of a vacuum-orthogonal state at
  physical separation `s` is the continuum covariance of the selected pair. -/
  os_same_object : ∀ psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 → ∀ s : ℝ, 0 ≤ s →
    ∫ x, Real.exp (-(s * x)) ∂(spec.spectralMeasure psi) ≤ ‖covInf psi s‖
  /-- `S₁`–`S₄`: the continuum covariance clusters exponentially at the physical
  rate `m`. -/
  clustering : ∀ psi : H.domain, ∀ s : ℝ, 0 ≤ s →
    ‖covInf psi s‖ ≤ clusterConst psi * Real.exp (-(m * s))

variable {H : E →ₗ.[ℂ] E} {vac : E} {m : ℝ}

/-- The physical Route-`S` data in the form the terminal spectral consumer
needs. -/
noncomputable def RouteSPhysicalData.toClusteringSpectralData (D : RouteSPhysicalData H vac m) :
    ClusteringSpectralData H vac m :=
  ClusteringSpectralData.ofSourceBound D.spec D.covInf D.clusterConst
    D.os_same_object (fun psi s hs => D.clustering psi s hs)

/-- **Physical Route `S` ⟹ the vacuum form gap of the same `H_OS`.** -/
theorem RouteSPhysicalData.vacuum_form_gap (D : RouteSPhysicalData H vac m) :
    HasVacuumFormGap H vac m :=
  hasVacuumFormGap_of_clustering D.toClusteringSpectralData

/-- **Physical Route `S` ⟹ the Clay mass-gap conclusion**, with a gap that is a
physical inverse correlation length. -/
theorem RouteSPhysicalData.massGapConclusion [CompleteSpace E] (D : RouteSPhysicalData H vac m)
    (hmem : vac ∈ H.domain) (hunit : ‖vac‖ = 1) (hground : H ⟨vac, hmem⟩ = 0)
    (hsa : IsSelfAdjoint H) :
    MassGapConclusion H vac m :=
  massGapConclusion_of_datum
    { op := H
      vac := vac
      gap := m
      vac_mem := hmem
      vac_unit := hunit
      vac_ground := hground
      selfAdjoint := hsa
      gap_pos := D.m_pos
      form_gap := D.vacuum_form_gap }

/-! ## The literal Wilson family at physical separations -/

open RequestProject.YangMills.Lattice

/-- **Literal `S₄` in physical units.**  The selected pair is a pair of literal
Wilson loops, the second displaced by the number of lattice time steps
representing the physical separation `s`.  Uniform clustering at physical
separations plus convergence of the three literal Wilson expectations gives the
continuum clustering estimate at the same physical rate. -/
theorem wilson_continuum_clustering_physical {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] {size : ℕ → ℕ} {beta : ℕ → ℝ} {a : ℕ → ℝ} {chi : G → ℝ}
    {xs ys : ∀ k, Site (size k)} {ps qs : ∀ _ : ℕ, List Step}
    {abI aI bI : ℝ → ℂ} {C m : ℝ}
    (hab : ∀ s : ℝ, Tendsto (fun k => ∫ U, conj (loopObs chi (xs k) (ps k) U) *
        loopObs chi (ys k + timeVec (size k) (latticeSteps (a k) s)) (qs k) U
          ∂(gibbs (size k) G (beta k) chi)) atTop (𝓝 (abI s)))
    (ha : ∀ s : ℝ, Tendsto (fun k => ∫ U, loopObs chi (xs k) (ps k) U
        ∂(gibbs (size k) G (beta k) chi)) atTop (𝓝 (aI s)))
    (hb : ∀ s : ℝ, Tendsto (fun k => ∫ U,
        loopObs chi (ys k + timeVec (size k) (latticeSteps (a k) s)) (qs k) U
        ∂(gibbs (size k) G (beta k) chi)) atTop (𝓝 (bI s)))
    (hfin : ∀ (k : ℕ) (s : ℝ), 0 ≤ s →
      ‖loopCov (size k) G (beta k) chi (xs k) (ys k) (ps k) (qs k) (latticeSteps (a k) s)‖
        ≤ C * Real.exp (-(m * s))) :
    ∀ s : ℝ, 0 ≤ s → ‖connected (abI s) (aI s) (bI s)‖ ≤ C * Real.exp (-(m * s)) := by
  intro s hs
  refine norm_le_of_tendsto_of_eventually_le
    (tendsto_connected (hab s) (ha s) (hb s)) (Filter.Eventually.of_forall fun k => ?_)
  have h := hfin k s hs
  rwa [loopCov_eq_connected] at h

/-- **Route `S` end to end on the literal Wilson family, in physical units.**
The clustering input is a uniform-in-cutoff estimate at fixed *physical*
separation, so — unlike the lattice-step form — it is compatible with a
continuum limit; the conclusion is the repository's full Clay-form mass-gap
statement for the reconstructed Osterwalder–Schrader Hamiltonian, at a gap
which is a physical inverse correlation length. -/
theorem wilson_routeS_physical_massGapConclusion {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] {size : ℕ → ℕ} {beta : ℕ → ℝ} {a : ℕ → ℝ} {chi : G → ℝ}
    {xs ys : ∀ k, Site (size k)} {ps qs : ∀ _ : ℕ, List Step}
    {abI aI bI : ℝ → ℂ} {C m : ℝ} (hm : 0 < m)
    (hab : ∀ s : ℝ, Tendsto (fun k => ∫ U, conj (loopObs chi (xs k) (ps k) U) *
        loopObs chi (ys k + timeVec (size k) (latticeSteps (a k) s)) (qs k) U
          ∂(gibbs (size k) G (beta k) chi)) atTop (𝓝 (abI s)))
    (ha : ∀ s : ℝ, Tendsto (fun k => ∫ U, loopObs chi (xs k) (ps k) U
        ∂(gibbs (size k) G (beta k) chi)) atTop (𝓝 (aI s)))
    (hb : ∀ s : ℝ, Tendsto (fun k => ∫ U,
        loopObs chi (ys k + timeVec (size k) (latticeSteps (a k) s)) (qs k) U
        ∂(gibbs (size k) G (beta k) chi)) atTop (𝓝 (bI s)))
    (hfin : ∀ (k : ℕ) (s : ℝ), 0 ≤ s →
      ‖loopCov (size k) G (beta k) chi (xs k) (ys k) (ps k) (qs k) (latticeSteps (a k) s)‖
        ≤ C * Real.exp (-(m * s)))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {H : E →ₗ.[ℂ] E} {vac : E} (spec : SpectralRepresentation H vac)
    (hos : ∀ psi : H.domain, ⟪vac, (psi : E)⟫_ℂ = 0 → ∀ s : ℝ, 0 ≤ s →
      ∫ x, Real.exp (-(s * x)) ∂(spec.spectralMeasure psi)
        ≤ ‖(psi : E)‖ ^ 2 * ‖connected (abI s) (aI s) (bI s)‖)
    (hmem : vac ∈ H.domain) (hunit : ‖vac‖ = 1) (hground : H ⟨vac, hmem⟩ = 0)
    (hsa : IsSelfAdjoint H) :
    MassGapConclusion H vac m := by
  have hclust : ∀ s : ℝ, 0 ≤ s → ‖connected (abI s) (aI s) (bI s)‖ ≤ C * Real.exp (-(m * s)) :=
    wilson_continuum_clustering_physical hab ha hb hfin
  have hnorm : ∀ (psi : H.domain) (s : ℝ),
      ‖((‖(psi : E)‖ ^ 2 : ℝ) : ℂ) * connected (abI s) (aI s) (bI s)‖
        = ‖(psi : E)‖ ^ 2 * ‖connected (abI s) (aI s) (bI s)‖ := by
    intro psi s
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine RouteSPhysicalData.massGapConclusion
    (D := { spec := spec
            covInf := fun psi s => ((‖(psi : E)‖ ^ 2 : ℝ) : ℂ) * connected (abI s) (aI s) (bI s)
            clusterConst := fun psi => ‖(psi : E)‖ ^ 2 * C
            m_pos := hm
            os_same_object := by
              intro psi horth s hs
              rw [hnorm psi s]
              exact hos psi horth s hs
            clustering := by
              intro psi s hs
              rw [hnorm psi s, mul_assoc]
              exact mul_le_mul_of_nonneg_left (hclust s hs) (by positivity) })
    hmem hunit hground hsa

end RequestProject.YangMills.RouteS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.RouteS

#print axioms physical_rate_unbounded_of_lattice_uniform_clustering
#print axioms continuum_clustering_physical
#print axioms RouteSPhysicalData.massGapConclusion
#print axioms wilson_continuum_clustering_physical
#print axioms wilson_routeS_physical_massGapConclusion

end Audit
