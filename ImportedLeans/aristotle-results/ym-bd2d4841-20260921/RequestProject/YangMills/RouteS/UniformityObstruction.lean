/-
# What Route `S` still owes, made precise

`RouteS/Covariance.lean` proves the compiler half of `S₄`:

* `continuum_clustering_of_finite_clustering` — *uniform* finite clustering
  (one pair `C`, `alpha` valid at **every** cutoff) plus convergence of the
  selected expectations gives the continuum clustering estimate.

This file pins down exactly how much of that hypothesis is genuinely needed,
and proves that the part that remains cannot be weakened to the form that a
cutoff-by-cutoff (lattice-native) estimate delivers.

Contents.

* `continuum_clustering_of_eventual_clustering` — the finite estimate is only
  needed *eventually along the cutoff filter*, not at every cutoff.
* `clustering_of_large_separation` — it is only needed at large Euclidean
  separations: a bound for `t ≥ T` plus any bound at all for `t < T` gives the
  full exponential estimate with an inflated constant.
* `counterCov`, `not_continuum_clustering_of_cutoff_dependent_clustering` — the
  sharpness statement: exponential clustering **at each cutoff separately**, at
  a common positive rate but with cutoff-dependent constants, together with
  convergence of the covariances at every fixed separation, does **not** imply
  any exponential clustering of the limit.  So the surviving Route-`S` debt is
  a uniform-in-cutoff estimate; no amount of per-cutoff (finite-lattice,
  strong-coupling, finite-volume) clustering can be composed into it.

Nothing here is an axiom, a flag or a receipt: everything is a theorem about
the same `connected`/covariance objects the Route-`S` lane consumes.
-/
import Mathlib
import RequestProject.YangMills.RouteS.Covariance

namespace RequestProject.YangMills.RouteS

open Filter Topology

variable {ι : Type*} {l : Filter ι}

/-! ## Two genuine relaxations of the surviving hypothesis -/

/-- **The finite clustering estimate is only needed eventually.**  It suffices
that, at each Euclidean separation, the exponential bound holds for all
sufficiently fine cutoffs (in the sense of the cutoff filter). -/
theorem continuum_clustering_of_eventual_clustering [l.NeBot] {covFinite : ι → ℕ → ℂ}
    {covInf : ℕ → ℂ} {C alpha : ℝ}
    (hlim : ∀ t : ℕ, Tendsto (fun k => covFinite k t) l (𝓝 (covInf t)))
    (hfin : ∀ t : ℕ, ∀ᶠ k in l, ‖covFinite k t‖ ≤ C * Real.exp (-(alpha * t))) :
    ∀ t : ℕ, ‖covInf t‖ ≤ C * Real.exp (-(alpha * t)) := fun t =>
  norm_le_of_tendsto_of_eventually_le (hlim t) (hfin t)

/-- **The clustering estimate is only needed at large separations.**  If the
exponential bound holds beyond some separation `T`, and the covariance is
bounded at all (which it is, for bounded observables), then the exponential
bound holds at every separation with the constant inflated by `exp (alpha * T)`.
-/
theorem clustering_of_large_separation {c : ℕ → ℂ} {C B alpha : ℝ} {T : ℕ}
    (halpha : 0 ≤ alpha) (hB : ∀ t : ℕ, ‖c t‖ ≤ B)
    (hfar : ∀ t : ℕ, T ≤ t → ‖c t‖ ≤ C * Real.exp (-(alpha * t))) :
    ∀ t : ℕ, ‖c t‖ ≤ max C (B * Real.exp (alpha * T)) * Real.exp (-(alpha * t)) := by
  intro t
  rcases le_or_gt T t with h | h
  · refine le_trans (hfar t h) (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    positivity
  · have hBt : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hB t)
    have hTt : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast h.le
    have hmono : Real.exp (alpha * T) * Real.exp (-(alpha * t)) ≥ 1 := by
      rw [← Real.exp_add]
      have hx : (0 : ℝ) ≤ alpha * T + -(alpha * t) := by
        nlinarith [mul_nonneg halpha (sub_nonneg.mpr hTt)]
      calc (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (alpha * T + -(alpha * t)) := Real.exp_le_exp.mpr hx
    have hle : B ≤ (B * Real.exp (alpha * T)) * Real.exp (-(alpha * t)) := by
      have := mul_le_mul_of_nonneg_left hmono hBt
      calc B = B * 1 := (mul_one B).symm
        _ ≤ B * (Real.exp (alpha * T) * Real.exp (-(alpha * t))) := this
        _ = (B * Real.exp (alpha * T)) * Real.exp (-(alpha * t)) := by ring
    refine le_trans (hB t) (le_trans hle ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-! ## Sharpness: per-cutoff clustering is not enough

The following family is the exact shape of what a finite-lattice /
finite-volume / strong-coupling argument produces: at each cutoff `k` the
covariance decays exponentially in the Euclidean separation at a fixed rate,
but the constant degrades with the cutoff.  The covariances converge at every
fixed separation, and yet the limit does not cluster at all. -/

/-- A covariance family: at cutoff `k` it equals `1` up to separation `k` and
vanishes beyond.  (Equivalently: an exponential bound at rate `1` with constant
`exp k`.) -/
noncomputable def counterCov (k t : ℕ) : ℂ := if t ≤ k then 1 else 0

theorem counterCov_bound (k : ℕ) (t : ℕ) :
    ‖counterCov k t‖ ≤ Real.exp k * Real.exp (-((1 : ℝ) * t)) := by
  unfold counterCov
  by_cases h : t ≤ k
  · simp only [h, if_true, norm_one]
    rw [← Real.exp_add]
    have : (0 : ℝ) ≤ (k : ℝ) + -((1 : ℝ) * t) := by
      have : (t : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr h
      linarith
    calc (1 : ℝ) = Real.exp 0 := by simp
      _ ≤ Real.exp ((k : ℝ) + -((1 : ℝ) * t)) := Real.exp_le_exp.mpr this
  · simp only [h, if_false, norm_zero]
    positivity

theorem counterCov_tendsto (t : ℕ) :
    Tendsto (fun k => counterCov k t) atTop (𝓝 (1 : ℂ)) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop t] with k hk
  simp [counterCov, hk]

theorem one_not_exp_decaying {C alpha : ℝ} (halpha : 0 < alpha) :
    ¬ ∀ t : ℕ, ‖(1 : ℂ)‖ ≤ C * Real.exp (-(alpha * t)) := by
  intro h
  have hC : (1 : ℝ) ≤ C := by simpa using h 0
  have hlim : Tendsto (fun t : ℕ => C * Real.exp (-(alpha * t))) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun t : ℕ => alpha * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop halpha tendsto_natCast_atTop_atTop
    have hexp : Tendsto (fun t : ℕ => Real.exp (-(alpha * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv
    simpa using hexp.const_mul C
  have hev : ∀ᶠ t : ℕ in atTop, C * Real.exp (-(alpha * t)) < 1 :=
    hlim.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨t, ht⟩ := hev.exists
  have := h t
  simp only [norm_one] at this
  linarith

/-- **Sharpness of the uniformity hypothesis.**  There is a covariance family
which, at every cutoff separately, clusters exponentially at the *same positive
rate* (only the constant depends on the cutoff), and which converges at every
fixed Euclidean separation, but whose limit satisfies **no** exponential
clustering bound whatsoever.

Consequently the surviving Route-`S` input cannot be assembled out of
cutoff-by-cutoff estimates: it has to be an estimate whose constant and rate do
not depend on the cutoff.  This is precisely the content that a finite lattice,
a finite volume, or a strong-coupling expansion at fixed lattice spacing does
not supply. -/
theorem not_continuum_clustering_of_cutoff_dependent_clustering :
    ∃ covFinite : ℕ → ℕ → ℂ, ∃ covInf : ℕ → ℂ,
      (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, ‖covFinite k t‖ ≤ C * Real.exp (-((1 : ℝ) * t))) ∧
      (∀ t : ℕ, Tendsto (fun k => covFinite k t) atTop (𝓝 (covInf t))) ∧
      (∀ C alpha : ℝ, 0 < alpha → ¬ ∀ t : ℕ, ‖covInf t‖ ≤ C * Real.exp (-(alpha * t))) := by
  refine ⟨counterCov, fun _ => 1, ?_, counterCov_tendsto, ?_⟩
  · exact fun k => ⟨Real.exp k, (Real.exp_pos _).le, counterCov_bound k⟩
  · intro C alpha halpha
    exact one_not_exp_decaying halpha

end RequestProject.YangMills.RouteS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.RouteS

#print axioms continuum_clustering_of_eventual_clustering
#print axioms clustering_of_large_separation
#print axioms not_continuum_clustering_of_cutoff_dependent_clustering

end Audit
