/-
# Reflection positivity of the continuum limit functional (OS2), unconditionally

`OS/WilsonReflectionPositivity.lean` proves Osterwalder–Schrader reflection
positivity of the **literal** Wilson–Gibbs measure at every even-time-extent
lattice, for every compact gauge group.  `Continuum/LimitState.lean` produces a
limit functional along a subsequence of cutoffs with no hypothesis at all.  This
file combines the two: the limit functional is reflection positive.

* `ReflectionSchedule` — a sequence of literal Wilson theories with even time
  extent, together with a finite family of uniformly bounded measurable
  observables living on the closed positive time half of each lattice;
* `gram_re_nonneg` — at every cutoff the Gram matrix of the reflected pairings
  is positive semidefinite.  This is `wilson_reflection_positive` applied to the
  linear combination `Σ c_s F_s`, expanded by linearity of the literal integral;
* `exists_reflection_positive_limit` — **the theorem**: there is a subsequence
  of cutoffs along which every reflected pairing
  `∫ conj(F_r ∘ Θ) · F_s dμ_Gibbs` converges, and the limiting Gram matrix is
  positive semidefinite:

  ```
    0 ≤ Re Σ_{r,s} conj(c_r) c_s L(r,s)   for every c : Fin m → ℂ.
  ```

So OS2 for the (subsequential) continuum limit of the literal Wilson theory is a
theorem, not an assumption, on any finite family of half-space observables.
What is *not* claimed: that the limit is unique or subsequence independent, that
it is represented by a measure on a continuum configuration space, that the
remaining OS axioms hold, or that the limit is nontrivial.
-/
import Mathlib
import RequestProject.YangMills.Continuum.LimitState
import RequestProject.YangMills.OS.WilsonReflectionPositivity

namespace RequestProject.YangMills.Continuum

open Filter Topology MeasureTheory
open RequestProject.YangMills.Lattice
open RequestProject.YangMills.OS
open scoped ComplexConjugate

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

/-- A sequence of literal Wilson theories with even time extent, carrying a
finite family of uniformly bounded measurable observables supported on the
closed positive time half. -/
structure ReflectionSchedule (m : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] where
  /-- the lattice size at cutoff `k`; the time extent is `size k + 1 = 2 * half k` -/
  size : ℕ → ℕ
  /-- half the time extent -/
  half : ℕ → ℕ
  /-- the time extent is even -/
  even_extent : ∀ k, size k + 1 = 2 * half k
  /-- the inverse coupling at cutoff `k` -/
  beta : ℕ → ℝ
  /-- the class function -/
  chi : G → ℝ
  continuous_chi : Continuous chi
  /-- conjugation invariance of the class function -/
  conj_chi : ∀ a g : G, chi (a * g * a⁻¹) = chi g
  /-- inversion symmetry of the class function -/
  inv_chi : ∀ g : G, chi g⁻¹ = chi g
  /-- the selected half-space observables -/
  F : (k : ℕ) → Fin m → Conf (size k) G → ℂ
  /-- the common bound -/
  bound : ℝ
  measurable_F : ∀ k r, Measurable (F k r)
  norm_F_le : ∀ k r U, ‖F k r U‖ ≤ bound
  /-- each observable depends only on the links of the closed positive half -/
  local_F : ∀ (k : ℕ) (r : Fin m) (U V : Conf (size k) G),
    (∀ l : Link (size k),
      l ∈ planeLinks (size k) (half k) ∨ l ∈ posLinks (size k) (half k) → U l = V l) →
    F k r U = F k r V

namespace ReflectionSchedule

variable {m : ℕ} (R : ReflectionSchedule m G)

/-- The reflected pairing of two selected observables at one cutoff: the literal
Wilson–Gibbs integral `∫ conj (F_r (Θ U)) · F_s (U) dμ(U)`. -/
noncomputable def pairing (k : ℕ) (r s : Fin m) : ℂ :=
  ∫ U, conj (R.F k r (reflConf (R.even_extent k) U)) * R.F k s U
    ∂(gibbs (R.size k) G (R.beta k) R.chi)

theorem measurable_reflConf (k : ℕ) :
    Measurable (reflConf (G := G) (R.even_extent k)) :=
  (wilsonReflData (R.even_extent k)).measurable_confRefl

theorem measurable_pairObs (k : ℕ) (r s : Fin m) :
    Measurable fun U => conj (R.F k r (reflConf (R.even_extent k) U)) * R.F k s U :=
  ((Complex.continuous_conj.measurable.comp
    ((R.measurable_F k r).comp (R.measurable_reflConf k)))).mul (R.measurable_F k s)

theorem norm_pairObs_le (k : ℕ) (r s : Fin m) (U : Conf (R.size k) G) :
    ‖conj (R.F k r (reflConf (R.even_extent k) U)) * R.F k s U‖ ≤ R.bound ^ 2 := by
  have h0 : (0 : ℝ) ≤ R.bound := le_trans (norm_nonneg _) (R.norm_F_le k s U)
  rw [norm_mul, RCLike.norm_conj]
  calc ‖R.F k r (reflConf (R.even_extent k) U)‖ * ‖R.F k s U‖
      ≤ R.bound * R.bound :=
        mul_le_mul (R.norm_F_le k r _) (R.norm_F_le k s U) (norm_nonneg _) h0
    _ = R.bound ^ 2 := by ring

theorem integrable_pairObs (k : ℕ) (r s : Fin m) :
    Integrable (fun U => conj (R.F k r (reflConf (R.even_extent k) U)) * R.F k s U)
      (gibbs (R.size k) G (R.beta k) R.chi) := by
  haveI := isProbabilityMeasure_gibbs (n := R.size k) (G := G) R.continuous_chi (R.beta k)
  exact Integrable.mono' (integrable_const (R.bound ^ 2))
    (R.measurable_pairObs k r s).aestronglyMeasurable
    (Filter.Eventually.of_forall fun U => R.norm_pairObs_le k r s U)

/-- **Finite-cutoff Gram positivity.**  At every cutoff the matrix of reflected
pairings of the selected half-space observables is positive semidefinite.  This
is Osterwalder–Seiler reflection positivity of the literal Wilson–Gibbs measure,
applied to the linear combination `Σ_s c_s F_s`. -/
theorem gram_re_nonneg (k : ℕ) (c : Fin m → ℂ) :
    0 ≤ (∑ r, ∑ s, conj (c r) * c s * R.pairing k r s).re := by
  haveI := isProbabilityMeasure_gibbs (n := R.size k) (G := G) R.continuous_chi (R.beta k)
  set n := R.size k
  set L := R.half k
  set hN := R.even_extent k
  set mu := gibbs n G (R.beta k) R.chi
  -- the combined half-space observable
  set Fc : Conf n G → ℂ := fun U => ∑ s, c s * R.F k s U with hFc
  have hFcm : Measurable Fc := by
    refine Finset.measurable_sum _ fun s _ => ?_
    exact (measurable_const.mul (R.measurable_F k s))
  have hFcb : ∀ U, ‖Fc U‖ ≤ ∑ s, ‖c s‖ * R.bound := by
    intro U
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun s _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (R.norm_F_le k s U) (norm_nonneg _)
  have hFcloc : ∀ U V : Conf n G,
      (∀ l : Link n, l ∈ planeLinks n L ∨ l ∈ posLinks n L → U l = V l) → Fc U = Fc V := by
    intro U V h
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [R.local_F k s U V h]
  have hRP := wilson_reflection_positive (n := n) (L := L) (G := G) hN R.continuous_chi
    R.conj_chi R.inv_chi (R.beta k) (F := Fc) hFcm hFcb hFcloc
  -- expand the Gram form
  have hexp : ∀ U : Conf n G, conj (Fc (reflConf hN U)) * Fc U
      = ∑ r, ∑ s, conj (c r) * c s * (conj (R.F k r (reflConf hN U)) * R.F k s U) := by
    intro U
    rw [hFc, map_sum]
    simp only [map_mul]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
  have hint : ∫ U, conj (Fc (reflConf hN U)) * Fc U ∂mu
      = ∑ r, ∑ s, conj (c r) * c s * R.pairing k r s := by
    rw [show (fun U => conj (Fc (reflConf hN U)) * Fc U)
        = fun U => ∑ r, ∑ s, conj (c r) * c s *
            (conj (R.F k r (reflConf hN U)) * R.F k s U) from funext hexp]
    rw [integral_finset_sum _ fun r _ => ?_]
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [integral_finset_sum _ fun s _ => ((R.integrable_pairObs k r s).const_mul _)]
      exact Finset.sum_congr rfl fun s _ => integral_const_mul _ _
    · exact integrable_finset_sum _ fun s _ => ((R.integrable_pairObs k r s).const_mul _)
  rw [← hint]
  exact hRP

end ReflectionSchedule

/-- The cutoff schedule of all reflected pairings of a reflection schedule. -/
noncomputable def reflectionCutoffSchedule {m : ℕ} (R : ReflectionSchedule m G) :
    CutoffSchedule (Fin m × Fin m) G where
  size := R.size
  beta := R.beta
  chi := R.chi
  obs := fun k rs U => conj (R.F k rs.1 (reflConf (R.even_extent k) U)) * R.F k rs.2 U
  bound := R.bound ^ 2
  continuous_chi := R.continuous_chi
  measurable_obs := fun k rs => R.measurable_pairObs k rs.1 rs.2
  norm_obs_le := fun k rs U => R.norm_pairObs_le k rs.1 rs.2 U

@[simp]
theorem reflectionCutoffSchedule_expect {m : ℕ} (R : ReflectionSchedule m G) (k : ℕ)
    (rs : Fin m × Fin m) :
    (reflectionCutoffSchedule R).expect k rs = R.pairing k rs.1 rs.2 := rfl

/-- **Reflection positivity of the continuum limit functional (OS2).**

For any sequence of literal Wilson theories with even time extent (lattice sizes
and couplings arbitrary) and any finite family of uniformly bounded measurable
observables supported on the closed positive time half, there is a subsequence
of cutoffs along which every reflected pairing converges, and the limiting Gram
matrix is positive semidefinite.

Neither convergence nor positivity is assumed: convergence comes from
compactness (`exists_limit_functional`) and positivity from the literal
Osterwalder–Seiler theorem (`wilson_reflection_positive`). -/
theorem exists_reflection_positive_limit {m : ℕ} (R : ReflectionSchedule m G) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : Fin m → Fin m → ℂ,
      (∀ r s, Tendsto (fun k => R.pairing (φ k) r s) atTop (𝓝 (L r s))) ∧
      (∀ r s, ‖L r s‖ ≤ R.bound ^ 2) ∧
      ∀ c : Fin m → ℂ, 0 ≤ (∑ r, ∑ s, conj (c r) * c s * L r s).re := by
  obtain ⟨φ, hφ, L, hconv, hbd, -, -, -⟩ := exists_limit_functional (reflectionCutoffSchedule R)
  refine ⟨φ, hφ, fun r s => L (r, s), fun r s => hconv (r, s), fun r s => hbd (r, s), ?_⟩
  intro c
  have hsum : Tendsto (fun k => ∑ r, ∑ s, conj (c r) * c s * R.pairing (φ k) r s) atTop
      (𝓝 (∑ r, ∑ s, conj (c r) * c s * L (r, s))) := by
    refine tendsto_finset_sum _ fun r _ => tendsto_finset_sum _ fun s _ => ?_
    exact (tendsto_const_nhds.mul (hconv (r, s)))
  exact limit_re_nonneg hsum fun k => R.gram_re_nonneg (φ k) c

end RequestProject.YangMills.Continuum

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Continuum

#print axioms ReflectionSchedule.gram_re_nonneg
#print axioms exists_reflection_positive_limit

end Audit
