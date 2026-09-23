/-
# The limit functional, pinned to the literal Wilson loops

`Continuum/LimitState.lean` proves that a countable family of uniformly bounded
continuous observables on a sequence of Wilson cutoffs always has a convergent
subsequence of expectations.  This file **instantiates** that statement on the
literal objects, so that nothing abstract is left in the statement:

* `wilsonLoopSchedule` — the cutoff schedule whose observables are the literal
  Wilson loops `loopObs chi x p` of `Lattice/WilsonLoop.lean`, at an arbitrary
  sequence of lattice sizes and inverse couplings;
* `exists_wilson_limit_functional` — along a subsequence of cutoffs **every**
  selected literal Wilson expectation `∫ W ∂μ_Gibbs` converges, with the limit
  bounded by the bound of the class function;
* `wilsonPairSchedule` — the schedule carrying, for every Euclidean separation
  `t`, the three literal integrals that make up the connected Wilson covariance
  `loopCov`;
* `expect_pair_*` — the identification of those expectations with the literal
  integrals, and `connected_expect_pair_eq_loopCov`, the identification of the
  resulting connected combination with `loopCov` itself;
* `exists_subseq_wilson_continuum_clustering` — the pinned capstone: from the
  cutoff-uniform clustering estimate for the **literal** `loopCov` alone, with
  no convergence hypothesis, there is a subsequence of cutoffs along which the
  three literal Wilson expectations converge and the continuum connected
  covariance obeys the same exponential bound.

This turns the Route-`S` coordinate `S₄` from a physical input into a theorem
about the literal objects (along a subsequence).  The genuinely physical input
that survives is `S₁`, the cutoff-uniform clustering hypothesis of
`exists_subseq_wilson_continuum_clustering`; it is not proved here, and
`RouteS/UniformityObstruction.lean` shows it cannot be assembled from
per-cutoff estimates.  Nothing here asserts that the limit is unique,
subsequence-independent, represented by a continuum measure, or nontrivial.
-/
import Mathlib
import RequestProject.YangMills.Continuum.LimitState
import RequestProject.YangMills.RouteS.UniformBounds

namespace RequestProject.YangMills.Continuum

open Filter Topology MeasureTheory
open RequestProject.YangMills.Lattice
open RequestProject.YangMills.RouteS
open scoped ComplexConjugate

variable {ι : Type*}
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

/-! ## The schedule of literal Wilson loops -/

/-- The cutoff schedule whose observables are the literal Wilson loops: at the
cutoff `k` the lattice has size `size k`, the inverse coupling is `beta k`, and
the observable `j` is the Wilson loop of shape `path k j` based at
`site k j`. -/
noncomputable def wilsonLoopSchedule (size : ℕ → ℕ) (beta : ℕ → ℝ) (chi : G → ℝ)
    (hchi : Continuous chi) {M : ℝ} (hM : ∀ g : G, |chi g| ≤ M)
    (site : (k : ℕ) → ι → Site (size k)) (path : ℕ → ι → List Step) :
    CutoffSchedule ι G where
  size := size
  beta := beta
  chi := chi
  obs := fun k j => loopObs chi (site k j) (path k j)
  bound := M
  continuous_chi := hchi
  measurable_obs := fun _ _ => (continuous_loopObs hchi _ _).measurable
  norm_obs_le := fun _ _ U => norm_loopObs_le hM _ _ U

@[simp]
theorem wilsonLoopSchedule_expect (size : ℕ → ℕ) (beta : ℕ → ℝ) (chi : G → ℝ)
    (hchi : Continuous chi) {M : ℝ} (hM : ∀ g : G, |chi g| ≤ M)
    (site : (k : ℕ) → ι → Site (size k)) (path : ℕ → ι → List Step) (k : ℕ) (j : ι) :
    (wilsonLoopSchedule size beta chi hchi hM site path).expect k j =
      ∫ U, loopObs chi (site k j) (path k j) U ∂(gibbs (size k) G (beta k) chi) := rfl

/-- **The literal Wilson expectations converge along a subsequence of cutoffs.**
No assumption is made on how the lattice sizes or the couplings vary, and none
on the loops: only that the class function is continuous and bounded (automatic
for a character of a compact group). -/
theorem exists_wilson_limit_functional [Countable ι] (size : ℕ → ℕ) (beta : ℕ → ℝ)
    (chi : G → ℝ) (hchi : Continuous chi) {M : ℝ} (hM : ∀ g : G, |chi g| ≤ M)
    (site : (k : ℕ) → ι → Site (size k)) (path : ℕ → ι → List Step) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : ι → ℂ, (∀ j, ‖L j‖ ≤ M) ∧
      ∀ j, Tendsto
        (fun k => ∫ U, loopObs chi (site (φ k) j) (path (φ k) j) U
          ∂(gibbs (size (φ k)) G (beta (φ k)) chi)) atTop (𝓝 (L j)) := by
  obtain ⟨φ, hφ, L, hconv, hbd, -, -, -⟩ :=
    exists_limit_functional (wilsonLoopSchedule size beta chi hchi hM site path)
  exact ⟨φ, hφ, L, hbd, hconv⟩

/-! ## The schedule of a selected pair and all its separations -/

/-- The index set of the three literal integrals entering the connected Wilson
covariance, one copy for each Euclidean separation. -/
abbrev PairIndex := ℕ ⊕ ℕ ⊕ ℕ

/-- The observables of the selected pair: the product at separation `t`, the
left loop, and the right loop translated by `t`. -/
noncomputable def pairObs (size : ℕ → ℕ) (chi : G → ℝ)
    (x y : (k : ℕ) → Site (size k)) (p q : List Step) (k : ℕ) :
    PairIndex → Conf (size k) G → ℂ
  | Sum.inl t => fun U =>
      conj (loopObs chi (x k) p U) * loopObs chi (y k + timeVec (size k) t) q U
  | Sum.inr (Sum.inl _) => loopObs chi (x k) p
  | Sum.inr (Sum.inr t) => loopObs chi (y k + timeVec (size k) t) q

/-- The cutoff schedule carrying, at every separation, the three literal
integrals of the connected Wilson covariance of one selected pair of loops. -/
noncomputable def wilsonPairSchedule (size : ℕ → ℕ) (beta : ℕ → ℝ) (chi : G → ℝ)
    (hchi : Continuous chi) {M : ℝ} (hM : ∀ g : G, |chi g| ≤ M)
    (x y : (k : ℕ) → Site (size k)) (p q : List Step) :
    CutoffSchedule PairIndex G where
  size := size
  beta := beta
  chi := chi
  obs := pairObs size chi x y p q
  bound := M + M ^ 2
  continuous_chi := hchi
  measurable_obs := by
    rintro k (t | t | t)
    · exact ((Complex.continuous_conj.comp (continuous_loopObs hchi _ _)).mul
        (continuous_loopObs hchi _ _)).measurable
    · exact (continuous_loopObs hchi _ _).measurable
    · exact (continuous_loopObs hchi _ _).measurable
  norm_obs_le := by
    have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM 1)
    have hsingle : ∀ (k : ℕ) (z : Site (size k)) (r : List Step) (U : Conf (size k) G),
        ‖loopObs chi z r U‖ ≤ M + M ^ 2 := by
      intro k z r U
      exact le_trans (norm_loopObs_le hM _ _ U) (by nlinarith [sq_nonneg M])
    rintro k (t | t | t) U
    · show ‖conj (loopObs chi (x k) p U) * loopObs chi (y k + timeVec (size k) t) q U‖ ≤ _
      rw [norm_mul, RCLike.norm_conj]
      have h1 := norm_loopObs_le hM (x k) p U
      have h2 := norm_loopObs_le hM (y k + timeVec (size k) t) q U
      calc ‖loopObs chi (x k) p U‖ * ‖loopObs chi (y k + timeVec (size k) t) q U‖
          ≤ M * M := mul_le_mul h1 h2 (norm_nonneg _) hM0
        _ ≤ M + M ^ 2 := by nlinarith
    · exact hsingle _ _ _ _
    · exact hsingle _ _ _ _

section Pair

variable (size : ℕ → ℕ) (beta : ℕ → ℝ) (chi : G → ℝ) (hchi : Continuous chi) {M : ℝ}
  (hM : ∀ g : G, |chi g| ≤ M) (x y : (k : ℕ) → Site (size k)) (p q : List Step)

@[simp]
theorem expect_pair_prod (k t : ℕ) :
    (wilsonPairSchedule size beta chi hchi hM x y p q).expect k (Sum.inl t) =
      ∫ U, conj (loopObs chi (x k) p U) * loopObs chi (y k + timeVec (size k) t) q U
        ∂(gibbs (size k) G (beta k) chi) := rfl

@[simp]
theorem expect_pair_left (k t : ℕ) :
    (wilsonPairSchedule size beta chi hchi hM x y p q).expect k (Sum.inr (Sum.inl t)) =
      ∫ U, loopObs chi (x k) p U ∂(gibbs (size k) G (beta k) chi) := rfl

@[simp]
theorem expect_pair_right (k t : ℕ) :
    (wilsonPairSchedule size beta chi hchi hM x y p q).expect k (Sum.inr (Sum.inr t)) =
      ∫ U, loopObs chi (y k + timeVec (size k) t) q U ∂(gibbs (size k) G (beta k) chi) := rfl

/-- The connected combination of the three schedule expectations **is** the
literal Wilson covariance of the selected pair at separation `t`. -/
theorem connected_expect_pair_eq_loopCov (k t : ℕ) :
    connected ((wilsonPairSchedule size beta chi hchi hM x y p q).expect k (Sum.inl t))
        ((wilsonPairSchedule size beta chi hchi hM x y p q).expect k (Sum.inr (Sum.inl t)))
        ((wilsonPairSchedule size beta chi hchi hM x y p q).expect k (Sum.inr (Sum.inr t)))
      = loopCov (size k) G (beta k) chi (x k) (y k) p q t :=
  (loopCov_eq_connected (beta k) chi (x k) (y k) p q t).symm

end Pair

/-- **Pinned capstone.**  Assume only the cutoff-uniform exponential clustering
estimate for the *literal* Wilson covariance `loopCov` of a selected pair of
loops (the Route-`S` input `S₁`).  Then there is a subsequence of cutoffs along
which the three literal Wilson expectations converge and the continuum connected
covariance built from those limits obeys the same exponential bound, with the
same constant and the same rate.

No convergence of the finite expectations is assumed: it is produced by
compactness in `exists_limit_functional`. -/
theorem exists_subseq_wilson_continuum_clustering (size : ℕ → ℕ) (beta : ℕ → ℝ) (chi : G → ℝ)
    (hchi : Continuous chi) {M : ℝ} (hM : ∀ g : G, |chi g| ≤ M)
    (x y : (k : ℕ) → Site (size k)) (p q : List Step) {C alpha : ℝ}
    (hcluster : ∀ k t : ℕ,
      ‖loopCov (size k) G (beta k) chi (x k) (y k) p q t‖ ≤ C * Real.exp (-(alpha * t))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ abInf aInf bInf : ℕ → ℂ,
      (∀ t, Tendsto (fun k => ∫ U, conj (loopObs chi (x (φ k)) p U) *
          loopObs chi (y (φ k) + timeVec (size (φ k)) t) q U
          ∂(gibbs (size (φ k)) G (beta (φ k)) chi)) atTop (𝓝 (abInf t))) ∧
      (∀ t, Tendsto (fun k => ∫ U, loopObs chi (x (φ k)) p U
          ∂(gibbs (size (φ k)) G (beta (φ k)) chi)) atTop (𝓝 (aInf t))) ∧
      (∀ t, Tendsto (fun k => ∫ U, loopObs chi (y (φ k) + timeVec (size (φ k)) t) q U
          ∂(gibbs (size (φ k)) G (beta (φ k)) chi)) atTop (𝓝 (bInf t))) ∧
      ∀ t, ‖connected (abInf t) (aInf t) (bInf t)‖ ≤ C * Real.exp (-(alpha * t)) := by
  have hcluster' : ∀ k t : ℕ,
      ‖connected ((wilsonPairSchedule size beta chi hchi hM x y p q).expect k (Sum.inl t))
        ((wilsonPairSchedule size beta chi hchi hM x y p q).expect k (Sum.inr (Sum.inl t)))
        ((wilsonPairSchedule size beta chi hchi hM x y p q).expect k (Sum.inr (Sum.inr t)))‖
      ≤ C * Real.exp (-(alpha * t)) := by
    intro k t
    rw [connected_expect_pair_eq_loopCov]
    exact hcluster k t
  obtain ⟨φ, hφ, abInf, aInf, bInf, hab, ha, hb, hbound⟩ :=
    exists_subseq_continuum_clustering (wilsonPairSchedule size beta chi hchi hM x y p q)
      (ab := Sum.inl) (aObs := fun t => Sum.inr (Sum.inl t))
      (bObs := fun t => Sum.inr (Sum.inr t)) hcluster'
  exact ⟨φ, hφ, abInf, aInf, bInf, hab, ha, hb, hbound⟩

end RequestProject.YangMills.Continuum

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Continuum

#print axioms exists_wilson_limit_functional
#print axioms connected_expect_pair_eq_loopCov
#print axioms exists_subseq_wilson_continuum_clustering

end Audit
