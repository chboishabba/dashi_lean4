/-
# The literal object Route `S` is about: Wilson-loop covariances at Euclidean
# separation `t`

This file puts `S₁`–`S₄` on one literal carrier.  Everything is stated for the
Wilson–Gibbs measure of `Lattice/Wilson.lean` and the Wilson-loop observables of
`Lattice/WilsonLoop.lean`; no auxiliary or synthetic model appears.

* `loopObs` — a literal Wilson-loop observable, viewed as a complex observable;
* `continuous_translateConf`, `measurable_translateConf` — continuity and
  measurability of the lattice translations;
* `integrable_loopObs` — Wilson-loop observables are integrable in the Wilson
  state (continuity on a compact configuration space, probability measure);
* `integral_comp_timeTranslate` — Euclidean time translation invariance of the
  literal Wilson expectations;
* `loopCov` — the connected covariance `Cov_k(W_{x,p}, τ_t W_{y,q})` of the
  literal translated pair;
* `loopCov_eq_cov_translatedLoop` — **`S₂`+`S₃` together**: that covariance is
  the covariance of two literal Wilson loops whose base points differ by `t`
  steps along the Euclidean time axis;
* `loopCov_gaugeInvariant` — the observables entering it are gauge invariant;
* `loopCov_eq_connected` — the covariance is the connected part of three
  literal Wilson expectations, which is the form the `S₄` limit compiler
  consumes.
-/
import Mathlib
import RequestProject.YangMills.RouteS.Covariance
import RequestProject.YangMills.RouteS.EuclideanTime

namespace RequestProject.YangMills.RouteS

open RequestProject.YangMills.Lattice
open MeasureTheory
open scoped ComplexConjugate

variable {n : ℕ}
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

/-! ## Observables -/

/-- A literal Wilson-loop observable as a complex-valued observable. -/
noncomputable def loopObs (chi : G → ℝ) (x : Site n) (p : List Step) :
    Conf n G → ℂ := fun U => (wilsonLoop chi x p U : ℂ)

omit [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
theorem continuous_loopObs {chi : G → ℝ} (hchi : Continuous chi) (x : Site n) (p : List Step) :
    Continuous (loopObs chi x p : Conf n G → ℂ) :=
  Complex.continuous_ofReal.comp (continuous_wilsonLoop hchi x p)

theorem integrable_loopObs {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ) (x : Site n)
    (p : List Step) :
    Integrable (loopObs chi x p : Conf n G → ℂ) (gibbs n G beta chi) := by
  haveI := isProbabilityMeasure_gibbs (n := n) (G := G) hchi beta
  exact (continuous_loopObs hchi x p).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integrable_loopObs_mul {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ)
    (x y : Site n) (p q : List Step) :
    Integrable (fun U : Conf n G => conj (loopObs chi x p U) * loopObs chi y q U)
      (gibbs n G beta chi) := by
  haveI := isProbabilityMeasure_gibbs (n := n) (G := G) hchi beta
  refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
  exact (Complex.continuous_conj.comp (continuous_loopObs hchi x p)).mul
    (continuous_loopObs hchi y q)

/-! ## Translations act measurably -/

omit [Group G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] in
theorem continuous_translateConf (v : Site n) :
    Continuous (translate (n := n) (G := G) v) := by
  refine continuous_pi fun l => ?_
  exact continuous_apply ((l.1 + v, l.2) : Link n)

omit [Group G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] in
theorem measurable_translateConf (v : Site n) :
    Measurable (translate (n := n) (G := G) v) :=
  (continuous_translateConf v).measurable

omit [Group G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] in
theorem measurable_timeTranslate (t : ℕ) :
    Measurable (timeTranslate (G := G) n t) :=
  measurable_translateConf _

/-- **Euclidean time translation invariance of the literal Wilson
expectations.** -/
theorem integral_comp_timeTranslate {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ)
    (t : ℕ) {A : Conf n G → ℂ} (hA : AEStronglyMeasurable A (gibbs n G beta chi)) :
    ∫ U, A (timeTranslate n t U) ∂(gibbs n G beta chi) = ∫ U, A U ∂(gibbs n G beta chi) := by
  have hmp := measurePreserving_timeTranslate_gibbs (n := n) (G := G) hchi beta t
  have hmap : Measure.map (timeTranslate (G := G) n t) (gibbs n G beta chi)
      = gibbs n G beta chi := hmp.map_eq
  have := integral_map (μ := gibbs n G beta chi)
    (φ := timeTranslate (G := G) n t) (f := A)
    (measurable_timeTranslate t).aemeasurable (by rwa [hmap])
  rw [hmap] at this
  exact this.symm

/-! ## The literal covariance of a translated pair -/

/-- The connected covariance of the literal Wilson loops `W_{x,p}` and
`τ_t W_{y,q}` in the literal Wilson state. -/
noncomputable def loopCov (n : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (beta : ℝ) (chi : G → ℝ) (x y : Site n) (p q : List Step)
    (t : ℕ) : ℂ :=
  cov (gibbs n G beta chi) (loopObs chi x p)
    (fun U => loopObs chi y q (timeTranslate n t U))

/-- **`S₂` and `S₃` on the literal object.**  The translated member of the pair
is the literal Wilson loop of the same shape based `t` steps later in Euclidean
time, so the separation coordinate of the covariance is physical Euclidean
separation of the supports. -/
theorem loopCov_eq_cov_translatedLoop (beta : ℝ) (chi : G → ℝ) (x y : Site n)
    (p q : List Step) (t : ℕ) :
    loopCov n G beta chi x y p q t =
      cov (gibbs n G beta chi) (loopObs chi x p) (loopObs chi (y + timeVec n t) q) := by
  have h : (fun U : Conf n G => loopObs chi y q (timeTranslate n t U))
      = loopObs chi (y + timeVec n t) q := by
    funext U
    simp [loopObs, wilsonLoop_timeTranslate]
  rw [loopCov, h]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- The observables entering the literal covariance are gauge invariant. -/
theorem loopObs_gaugeTransform {chi : G → ℝ}
    (hchi : ∀ a g : G, chi (a * g * a⁻¹) = chi g) {x : Site n} {p : List Step}
    (hp : IsLoop n x p) (g : Site n → G) (U : Conf n G) :
    loopObs chi x p (gaugeTransform g U) = loopObs chi x p U := by
  simp [loopObs, wilsonLoop_gaugeTransform hchi hp]

/-- The covariance is the connected part of three literal Wilson expectations —
the form consumed by the `S₄` limit compiler. -/
theorem loopCov_eq_connected (beta : ℝ) (chi : G → ℝ) (x y : Site n) (p q : List Step)
    (t : ℕ) :
    loopCov n G beta chi x y p q t =
      connected
        (∫ U, conj (loopObs chi x p U) * loopObs chi (y + timeVec n t) q U
          ∂(gibbs n G beta chi))
        (∫ U, loopObs chi x p U ∂(gibbs n G beta chi))
        (∫ U, loopObs chi (y + timeVec n t) q U ∂(gibbs n G beta chi)) := by
  rw [loopCov_eq_cov_translatedLoop, cov_eq_connected]

/-- The literal variance of a Wilson loop is nonnegative: the state is a genuine
positive expectation, not a formal functional. -/
theorem loopCov_self_nonneg {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ) (x : Site n)
    (p : List Step) :
    0 ≤ (cov (gibbs n G beta chi) (loopObs chi x p) (loopObs chi x p)).re := by
  haveI := isProbabilityMeasure_gibbs (n := n) (G := G) hchi beta
  exact cov_self_nonneg _ (integrable_loopObs hchi beta x p)
    (integrable_loopObs_mul hchi beta x x p p)

end RequestProject.YangMills.RouteS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.RouteS

#print axioms integral_comp_timeTranslate
#print axioms loopCov_eq_cov_translatedLoop
#print axioms loopCov_eq_connected
#print axioms loopCov_self_nonneg

end Audit
