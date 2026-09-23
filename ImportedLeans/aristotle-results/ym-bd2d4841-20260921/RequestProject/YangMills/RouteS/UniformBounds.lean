/-
# Unconditional uniform bounds for the literal Wilson observables

Route `S` consumes a clustering estimate for the literal Wilson-loop covariance
`loopCov` at *every* cutoff.  This file proves, with no hypothesis beyond
boundedness of the class function `chi` (automatic for a character of a compact
group), the part of that estimate which is unconditional:

* `norm_loopObs_le` — the literal Wilson-loop observable is bounded by `M`
  pointwise;
* `norm_integral_loopObs_le` — hence so is its Wilson–Gibbs expectation, at
  every lattice size, every coupling and every loop;
* `norm_loopCov_le` — hence the literal covariance obeys the uniform a-priori
  bound `2 M²`, again at every cutoff.

Consequence (`wilson_clustering_of_large_separation`): the surviving physical
input of Route `S` only has to be proved *at large Euclidean separations*.  A
uniform-in-cutoff exponential bound valid for `t ≥ T` automatically upgrades to
one valid for all `t`, with the constant `max C (2 M² e^{α T})`.  Together with
`RouteS/UniformityObstruction.lean` this delimits the debt exactly: what is
still missing is a bound that is uniform in the cutoff, and it is missing only
in the large-separation regime.
-/
import Mathlib
import RequestProject.YangMills.RouteS.WilsonCovariance
import RequestProject.YangMills.RouteS.UniformityObstruction

namespace RequestProject.YangMills.RouteS

open MeasureTheory
open RequestProject.YangMills.Lattice
open scoped ComplexConjugate

variable {n : ℕ}
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] in
/-- A bounded class function gives a pointwise bounded Wilson-loop observable. -/
theorem norm_loopObs_le {chi : G → ℝ} {M : ℝ} (hM : ∀ g : G, |chi g| ≤ M)
    (x : Site n) (p : List Step) (U : Conf n G) :
    ‖loopObs chi x p U‖ ≤ M := by
  simpa [loopObs, wilsonLoop, Complex.norm_real, Real.norm_eq_abs] using hM (pathHol U x p)

/-- **Uniform bound on the literal Wilson expectations.**  At every lattice
size, every coupling and every loop, the Wilson–Gibbs expectation of a Wilson
loop is bounded by the bound of the class function. -/
theorem norm_integral_loopObs_le {chi : G → ℝ} (hchi : Continuous chi) {M : ℝ}
    (hM : ∀ g : G, |chi g| ≤ M) (beta : ℝ) (x : Site n) (p : List Step) :
    ‖∫ U, loopObs chi x p U ∂(gibbs n G beta chi)‖ ≤ M := by
  haveI := isProbabilityMeasure_gibbs (n := n) (G := G) hchi beta
  have h := norm_integral_le_of_norm_le_const (μ := gibbs n G beta chi)
    (f := loopObs chi x p) (C := M)
    (Filter.Eventually.of_forall fun U => norm_loopObs_le hM x p U)
  simpa using h

/-- **Uniform a-priori bound on the literal Wilson covariance.**  No coupling
condition, no volume condition: `2 M²` bounds `loopCov` at every cutoff. -/
theorem norm_loopCov_le {chi : G → ℝ} (hchi : Continuous chi) {M : ℝ}
    (hM : ∀ g : G, |chi g| ≤ M) (beta : ℝ) (x y : Site n) (p q : List Step) (t : ℕ) :
    ‖loopCov n G beta chi x y p q t‖ ≤ M ^ 2 + M ^ 2 := by
  haveI := isProbabilityMeasure_gibbs (n := n) (G := G) hchi beta
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM 1)
  have hprod : ‖∫ U, conj (loopObs chi x p U) * loopObs chi (y + timeVec n t) q U
      ∂(gibbs n G beta chi)‖ ≤ M ^ 2 := by
    have hb : ∀ U : Conf n G,
        ‖conj (loopObs chi x p U) * loopObs chi (y + timeVec n t) q U‖ ≤ M ^ 2 := by
      intro U
      rw [norm_mul, RCLike.norm_conj]
      have h1 := norm_loopObs_le hM x p U
      have h2 := norm_loopObs_le hM (y + timeVec n t) q U
      calc ‖loopObs chi x p U‖ * ‖loopObs chi (y + timeVec n t) q U‖
          ≤ M * M := by
            exact mul_le_mul h1 h2 (norm_nonneg _) hM0
        _ = M ^ 2 := by ring
    simpa using norm_integral_le_of_norm_le_const (μ := gibbs n G beta chi)
      (f := fun U => conj (loopObs chi x p U) * loopObs chi (y + timeVec n t) q U)
      (C := M ^ 2) (Filter.Eventually.of_forall hb)
  have hsingle : ‖conj (∫ U, loopObs chi x p U ∂(gibbs n G beta chi)) *
      ∫ U, loopObs chi (y + timeVec n t) q U ∂(gibbs n G beta chi)‖ ≤ M ^ 2 := by
    rw [norm_mul, RCLike.norm_conj]
    have h1 := norm_integral_loopObs_le hchi hM beta x p
    have h2 := norm_integral_loopObs_le hchi hM beta (y + timeVec n t) q
    calc ‖∫ U, loopObs chi x p U ∂(gibbs n G beta chi)‖ *
          ‖∫ U, loopObs chi (y + timeVec n t) q U ∂(gibbs n G beta chi)‖
        ≤ M * M := mul_le_mul h1 h2 (norm_nonneg _) hM0
      _ = M ^ 2 := by ring
  rw [loopCov_eq_connected, connected]
  exact le_trans (norm_sub_le _ _) (add_le_add hprod hsingle)

/-- **Only large separations matter.**  If the literal Wilson covariance obeys a
uniform exponential bound beyond some Euclidean separation `T`, it obeys one at
every separation, with the constant inflated by the a-priori bound `2 M²`.  So
the surviving Route-`S` physical input may be assumed to be a large-separation
statement. -/
theorem wilson_clustering_of_large_separation {chi : G → ℝ} (hchi : Continuous chi) {M : ℝ}
    (hM : ∀ g : G, |chi g| ≤ M) (beta : ℝ) (x y : Site n) (p q : List Step)
    {C alpha : ℝ} {T : ℕ} (halpha : 0 ≤ alpha)
    (hfar : ∀ t : ℕ, T ≤ t → ‖loopCov n G beta chi x y p q t‖ ≤ C * Real.exp (-(alpha * t))) :
    ∀ t : ℕ, ‖loopCov n G beta chi x y p q t‖
      ≤ max C ((M ^ 2 + M ^ 2) * Real.exp (alpha * T)) * Real.exp (-(alpha * t)) :=
  clustering_of_large_separation (c := fun t => loopCov n G beta chi x y p q t)
    halpha (fun t => norm_loopCov_le hchi hM beta x y p q t) hfar

end RequestProject.YangMills.RouteS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.RouteS

#print axioms norm_loopObs_le
#print axioms norm_integral_loopObs_le
#print axioms norm_loopCov_le
#print axioms wilson_clustering_of_large_separation

end Audit
