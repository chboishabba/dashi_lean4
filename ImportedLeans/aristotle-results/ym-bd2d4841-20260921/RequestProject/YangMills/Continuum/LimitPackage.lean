/-
# One subsequence, one limit functional: the same-object package

The three previous files each extract their own subsequence of cutoffs.  For the
continuum construction that is not enough: the state whose clustering one
estimates has to be the *same* state that is reflection positive and translation
invariant.  This file does the extraction once.

`WilsonLimitSchedule` packages, over one sequence of literal Wilson theories
(lattice size and coupling arbitrary, time extent even):

* a countable family of literal Wilson loops (`site`, `path`);
* their pairwise products, whose expectations are the two-point functions;
* a finite family of half-space observables for reflection positivity (`F`).

`exists_wilson_limit_package` then produces **one** subsequence `φ` and **one**
limit functional along it, for which all of the following hold simultaneously:

* every selected Wilson expectation and every selected two-point function
  converges, with the a-priori bounds;
* loops of the same shape have the same limit (translation invariance — the
  translation half of OS1);
* the limiting reflection Gram matrix is positive semidefinite (OS2);
* any cutoff-uniform exponential clustering estimate for the finite connected
  two-point functions passes to the limit, for the *same* limit functional.

Everything is proved; the only hypothesis anywhere is the clustering estimate in
the last item, which is displayed as an implication and is exactly the
Route-`S` physical input `S₁`.  No claim is made that the limit is unique,
subsequence independent, represented by a continuum measure, or nontrivial.
-/
import Mathlib
import RequestProject.YangMills.Continuum.LimitSymmetries
import RequestProject.YangMills.Continuum.ReflectionPositiveLimit

namespace RequestProject.YangMills.Continuum

open Filter Topology MeasureTheory
open RequestProject.YangMills.Lattice
open RequestProject.YangMills.OS
open RequestProject.YangMills.RouteS
open scoped ComplexConjugate

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

/-- A sequence of literal Wilson theories with even time extent, carrying both a
countable family of Wilson loops and a finite family of half-space observables
for the reflection. -/
structure WilsonLimitSchedule (ι : Type*) (m : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] where
  /-- the lattice size at cutoff `k` -/
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
  /-- the bound of the class function -/
  chiBound : ℝ
  norm_chi_le : ∀ g : G, |chi g| ≤ chiBound
  /-- base points of the selected loops -/
  site : (k : ℕ) → ι → Site (size k)
  /-- shapes of the selected loops -/
  path : ℕ → ι → List Step
  /-- the selected half-space observables -/
  F : (k : ℕ) → Fin m → Conf (size k) G → ℂ
  /-- their common bound -/
  fBound : ℝ
  measurable_F : ∀ k r, Measurable (F k r)
  norm_F_le : ∀ k r U, ‖F k r U‖ ≤ fBound
  local_F : ∀ (k : ℕ) (r : Fin m) (U V : Conf (size k) G),
    (∀ l : Link (size k),
      l ∈ planeLinks (size k) (half k) ∨ l ∈ posLinks (size k) (half k) → U l = V l) →
    F k r U = F k r V

namespace WilsonLimitSchedule

variable {ι : Type*} {m : ℕ} (W : WilsonLimitSchedule ι m G)

/-- The literal Wilson–Gibbs measure at cutoff `k`. -/
noncomputable def measure (k : ℕ) : Measure (Conf (W.size k) G) :=
  gibbs (W.size k) G (W.beta k) W.chi

/-- The expectation of the selected Wilson loop `j` at cutoff `k`. -/
noncomputable def loopExpect (k : ℕ) (j : ι) : ℂ :=
  ∫ U, loopObs W.chi (W.site k j) (W.path k j) U ∂(W.measure k)

/-- The two-point function of the selected loops `i` and `j` at cutoff `k`. -/
noncomputable def prodExpect (k : ℕ) (i j : ι) : ℂ :=
  ∫ U, conj (loopObs W.chi (W.site k i) (W.path k i) U) *
    loopObs W.chi (W.site k j) (W.path k j) U ∂(W.measure k)

/-- The reflected pairing of the half-space observables `r` and `s`. -/
noncomputable def reflPairing (k : ℕ) (r s : Fin m) : ℂ :=
  ∫ U, conj (W.F k r (reflConf (W.even_extent k) U)) * W.F k s U ∂(W.measure k)

/-- The reflection schedule underlying `W`. -/
def toReflectionSchedule : ReflectionSchedule m G where
  size := W.size
  half := W.half
  even_extent := W.even_extent
  beta := W.beta
  chi := W.chi
  continuous_chi := W.continuous_chi
  conj_chi := W.conj_chi
  inv_chi := W.inv_chi
  F := W.F
  bound := W.fBound
  measurable_F := W.measurable_F
  norm_F_le := W.norm_F_le
  local_F := W.local_F

theorem reflPairing_eq (k : ℕ) (r s : Fin m) :
    W.reflPairing k r s = W.toReflectionSchedule.pairing k r s := rfl

theorem chiBound_nonneg : 0 ≤ W.chiBound := le_trans (abs_nonneg _) (W.norm_chi_le 1)

/-- The combined index: loops, two-point functions, reflected pairings. -/
abbrev Index (ι : Type*) (m : ℕ) := ι ⊕ ((ι × ι) ⊕ (Fin m × Fin m))

/-- All the selected observables of `W` in one cutoff schedule. -/
noncomputable def toCutoffSchedule : CutoffSchedule (Index ι m) G where
  size := W.size
  beta := W.beta
  chi := W.chi
  obs := fun k j => match j with
    | Sum.inl j => loopObs W.chi (W.site k j) (W.path k j)
    | Sum.inr (Sum.inl (i, j)) => fun U =>
        conj (loopObs W.chi (W.site k i) (W.path k i) U) *
          loopObs W.chi (W.site k j) (W.path k j) U
    | Sum.inr (Sum.inr (r, s)) => fun U =>
        conj (W.F k r (reflConf (W.even_extent k) U)) * W.F k s U
  bound := W.chiBound + W.chiBound ^ 2 + W.fBound ^ 2
  continuous_chi := W.continuous_chi
  measurable_obs := by
    rintro k (j | ⟨i, j⟩ | ⟨r, s⟩)
    · exact (continuous_loopObs W.continuous_chi _ _).measurable
    · exact ((Complex.continuous_conj.comp
        (continuous_loopObs W.continuous_chi _ _)).mul
        (continuous_loopObs W.continuous_chi _ _)).measurable
    · exact W.toReflectionSchedule.measurable_pairObs k r s
  norm_obs_le := by
    have hchi0 := W.chiBound_nonneg
    rintro k (j | ⟨i, j⟩ | ⟨r, s⟩) U
    · have h := norm_loopObs_le W.norm_chi_le (W.site k j) (W.path k j) U
      nlinarith [sq_nonneg W.chiBound, sq_nonneg W.fBound]
    · have h1 := norm_loopObs_le W.norm_chi_le (W.site k i) (W.path k i) U
      have h2 := norm_loopObs_le W.norm_chi_le (W.site k j) (W.path k j) U
      have h : ‖conj (loopObs W.chi (W.site k i) (W.path k i) U) *
          loopObs W.chi (W.site k j) (W.path k j) U‖ ≤ W.chiBound ^ 2 := by
        rw [norm_mul, RCLike.norm_conj]
        calc ‖loopObs W.chi (W.site k i) (W.path k i) U‖ *
              ‖loopObs W.chi (W.site k j) (W.path k j) U‖
            ≤ W.chiBound * W.chiBound := mul_le_mul h1 h2 (norm_nonneg _) hchi0
          _ = W.chiBound ^ 2 := by ring
      nlinarith [sq_nonneg W.fBound]
    · show ‖conj (W.F k r (reflConf (W.even_extent k) U)) * W.F k s U‖ ≤ _
      have h1 := W.norm_F_le k r (reflConf (W.even_extent k) U)
      have h2 := W.norm_F_le k s U
      have hf0 : (0 : ℝ) ≤ W.fBound := le_trans (norm_nonneg _) h2
      rw [norm_mul, RCLike.norm_conj]
      have hmul : ‖W.F k r (reflConf (W.even_extent k) U)‖ * ‖W.F k s U‖
          ≤ W.fBound * W.fBound := mul_le_mul h1 h2 (norm_nonneg _) hf0
      nlinarith [sq_nonneg W.chiBound]

@[simp] theorem expect_loop (k : ℕ) (j : ι) :
    W.toCutoffSchedule.expect k (Sum.inl j) = W.loopExpect k j := rfl

@[simp] theorem expect_prod (k : ℕ) (i j : ι) :
    W.toCutoffSchedule.expect k (Sum.inr (Sum.inl (i, j))) = W.prodExpect k i j := rfl

@[simp] theorem expect_refl (k : ℕ) (r s : Fin m) :
    W.toCutoffSchedule.expect k (Sum.inr (Sum.inr (r, s))) = W.reflPairing k r s := rfl

theorem norm_loopExpect_le (k : ℕ) (j : ι) : ‖W.loopExpect k j‖ ≤ W.chiBound :=
  norm_integral_loopObs_le W.continuous_chi W.norm_chi_le (W.beta k) _ _

end WilsonLimitSchedule

/-- **The same-object limit package.**

For one sequence of literal Wilson theories with even time extent there is one
subsequence of cutoffs and one limit functional along it such that:

1. all selected Wilson expectations converge, with the a-priori bound;
2. all selected two-point functions converge;
3. all reflected pairings converge;
4. loops of the same shape have the same limit (translation invariance), and a
   trivial loop has limit `chi 1`, so the limit functional is not the zero
   functional whenever `chi 1 ≠ 0`;
5. the limiting reflection Gram matrix is positive semidefinite (OS2);
6. any cutoff-uniform exponential clustering estimate for the finite connected
   two-point functions passes to the same limit functional.

Items 1–5 are unconditional; item 6 is an implication whose hypothesis is the
Route-`S` physical input. -/
theorem exists_wilson_limit_package {ι : Type*} [Countable ι] {m : ℕ}
    (W : WilsonLimitSchedule ι m G) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (Lloop : ι → ℂ) (Lprod : ι → ι → ℂ) (Lrefl : Fin m → Fin m → ℂ),
        (∀ j, Tendsto (fun k => W.loopExpect (φ k) j) atTop (𝓝 (Lloop j))) ∧
        (∀ i j, Tendsto (fun k => W.prodExpect (φ k) i j) atTop (𝓝 (Lprod i j))) ∧
        (∀ r s, Tendsto (fun k => W.reflPairing (φ k) r s) atTop (𝓝 (Lrefl r s))) ∧
        (∀ j, ‖Lloop j‖ ≤ W.chiBound) ∧
        (∀ i j : ι, (∀ k, W.path k i = W.path k j) → Lloop i = Lloop j) ∧
        (∀ j : ι, (∀ k, W.path k j = []) → Lloop j = (W.chi 1 : ℂ)) ∧
        (∀ c : Fin m → ℂ, 0 ≤ (∑ r, ∑ s, conj (c r) * c s * Lrefl r s).re) ∧
        (∀ (C alpha : ℝ) (a b : ℕ → ι),
          (∀ k t : ℕ, ‖connected (W.prodExpect k (a t) (b t)) (W.loopExpect k (a t))
              (W.loopExpect k (b t))‖ ≤ C * Real.exp (-(alpha * t))) →
          ∀ t : ℕ, ‖connected (Lprod (a t) (b t)) (Lloop (a t)) (Lloop (b t))‖
            ≤ C * Real.exp (-(alpha * t))) := by
  obtain ⟨φ, hφ, L, hconv, -, -, -, -⟩ := exists_limit_functional W.toCutoffSchedule
  refine ⟨φ, hφ, fun j => L (Sum.inl j), fun i j => L (Sum.inr (Sum.inl (i, j))),
    fun r s => L (Sum.inr (Sum.inr (r, s))), fun j => hconv (Sum.inl j),
    fun i j => hconv (Sum.inr (Sum.inl (i, j))), fun r s => hconv (Sum.inr (Sum.inr (r, s))),
    ?_, ?_, ?_, ?_, ?_⟩
  · -- a-priori bound on the Wilson limits
    intro j
    exact norm_le_of_tendsto_of_eventually_le (hconv (Sum.inl j))
      (Filter.Eventually.of_forall fun k => W.norm_loopExpect_le (φ k) j)
  · -- translation invariance
    intro i j hshape
    refine limit_eq_of_forall_eq_seq (hconv (Sum.inl i)) (hconv (Sum.inl j)) fun k => ?_
    show W.loopExpect (φ k) i = W.loopExpect (φ k) j
    rw [WilsonLimitSchedule.loopExpect, WilsonLimitSchedule.loopExpect, hshape (φ k)]
    exact integral_loopObs_congr_shape W.continuous_chi (W.beta (φ k)) _ _ _
  · -- the trivial loop pins the normalisation
    intro j htriv
    refine limit_eq_of_forall_eq (hconv (Sum.inl j)) fun k => ?_
    show W.loopExpect (φ k) j = (W.chi 1 : ℂ)
    rw [WilsonLimitSchedule.loopExpect, htriv (φ k)]
    exact integral_loopObs_nil W.continuous_chi (W.beta (φ k)) _
  · -- reflection positivity
    intro c
    have hsum : Tendsto (fun k => ∑ r, ∑ s, conj (c r) * c s * W.reflPairing (φ k) r s) atTop
        (𝓝 (∑ r, ∑ s, conj (c r) * c s * L (Sum.inr (Sum.inr (r, s))))) :=
      tendsto_finset_sum _ fun r _ => tendsto_finset_sum _ fun s _ =>
        tendsto_const_nhds.mul (hconv (Sum.inr (Sum.inr (r, s))))
    refine limit_re_nonneg hsum fun k => ?_
    have := W.toReflectionSchedule.gram_re_nonneg (φ k) c
    simpa [W.reflPairing_eq] using this
  · -- clustering of the same limit functional
    intro C alpha a b hfin
    exact continuum_clustering_of_expectation_limits
      (abF := fun k t => W.prodExpect (φ k) (a t) (b t))
      (aF := fun k t => W.loopExpect (φ k) (a t))
      (bF := fun k t => W.loopExpect (φ k) (b t))
      (fun t => hconv (Sum.inr (Sum.inl (a t, b t)))) (fun t => hconv (Sum.inl (a t)))
      (fun t => hconv (Sum.inl (b t))) (fun k t => hfin (φ k) t)

end RequestProject.YangMills.Continuum

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Continuum

#print axioms exists_wilson_limit_package

end Audit
