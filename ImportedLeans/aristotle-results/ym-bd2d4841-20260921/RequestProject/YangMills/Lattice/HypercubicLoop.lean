/-
# Wilson loops under the hypercubic group

`Lattice/Hypercubic.lean` proves that the Wilson–Gibbs measure is invariant
under the hypercubic point group.  This file transports that invariance to the
*observables*: the literal Wilson loop of a rotated or reflected loop is the
pullback of the Wilson loop of the original loop, so

    E[ W_{σ C} ] = E[ W_C ],        E[ W_{θ C} ] = E[ W_C ]

for every permutation `σ` of the coordinate axes and every reflection `θ` in a
coordinate hyperplane.  Together with the translation statement already
available this is the finite-lattice Euclidean invariance of the Wilson
expectations in loop form, the shape the continuum limit consumes.

* `rotStep`, `refStep` — the action of the point group on a directed lattice
  step;
* `pathHol_rotate`, `pathHol_reflect` — the holonomy identities, proved by
  induction along the path;
* `integral_loopObs_rotate`, `integral_loopObs_reflect` — the expectation
  identities.
-/
import Mathlib
import RequestProject.YangMills.Lattice.Hypercubic
import RequestProject.YangMills.RouteS.WilsonCovariance

namespace RequestProject.YangMills.Lattice

open MeasureTheory
open RequestProject.YangMills.RouteS

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

variable {n : ℕ}

/-! ## Axis permutations -/

/-- A permutation of the coordinate axes acting on a directed step. -/
def rotStep (sig : Equiv.Perm (Fin 4)) (s : Step) : Step := (sig s.1, s.2)

theorem rotSite_neg (sig : Equiv.Perm (Fin 4)) (x : Site n) :
    rotSite sig (-x) = -(rotSite sig x) := rfl

theorem rotSite_stepShift (sig : Equiv.Perm (Fin 4)) (s : Step) :
    rotSite sig (stepShift n s) = stepShift n (rotStep sig s) := by
  cases s with
  | mk d b =>
    cases b
    · simp [stepShift, rotStep, rotSite_neg, rotSite_unitVec]
    · simp [stepShift, rotStep, rotSite_unitVec]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem stepHol_rotate (sig : Equiv.Perm (Fin 4)) (U : Conf n G) (x : Site n) (s : Step) :
    stepHol (rotate sig U) x s = stepHol U (rotSite sig.symm x) (rotStep sig.symm s) := by
  cases s with
  | mk d b =>
    cases b
    · have h : rotSite sig.symm (x - unitVec n d)
          = rotSite sig.symm x - unitVec n (sig.symm d) := by
        rw [sub_eq_add_neg, rotSite_add, rotSite_neg, rotSite_unitVec, ← sub_eq_add_neg]
      simp [stepHol, rotate, rotStep, h]
    · simp [stepHol, rotate, rotStep]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem pathHol_rotate (sig : Equiv.Perm (Fin 4)) (U : Conf n G) (x : Site n) (p : List Step) :
    pathHol (rotate sig U) x p
      = pathHol U (rotSite sig.symm x) (p.map (rotStep sig.symm)) := by
  induction p generalizing x with
  | nil => simp
  | cons s p ih =>
      have hshift : rotSite sig.symm (x + stepShift n s)
          = rotSite sig.symm x + stepShift n (rotStep sig.symm s) := by
        rw [rotSite_add, rotSite_stepShift]
      simp only [List.map_cons, pathHol_cons, ih, stepHol_rotate, hshift]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem wilsonLoop_rotate (chi : G → ℝ) (sig : Equiv.Perm (Fin 4)) (x : Site n) (p : List Step)
    (U : Conf n G) :
    wilsonLoop chi x p (rotate sig U)
      = wilsonLoop chi (rotSite sig.symm x) (p.map (rotStep sig.symm)) U := by
  simp [wilsonLoop, pathHol_rotate]

/-- **Invariance of the Wilson expectation under a permutation of the coordinate
axes**: a Wilson loop and its rotated image have the same expectation. -/
theorem integral_loopObs_rotate {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ)
    (sig : Equiv.Perm (Fin 4)) (x : Site n) (p : List Step) :
    ∫ U, loopObs chi (rotSite sig x) (p.map (rotStep sig)) U ∂(gibbs n G beta chi)
      = ∫ U, loopObs chi x p U ∂(gibbs n G beta chi) := by
  have hpull : ∀ U : Conf n G,
      loopObs chi (rotSite sig x) (p.map (rotStep sig)) (rotate sig U) = loopObs chi x p U := by
    intro U
    have hx : rotSite sig.symm (rotSite (n := n) sig x) = x := rotSite_leftInverse sig x
    have hp : ((p.map (rotStep sig)).map (rotStep sig.symm)) = p := by
      have hcomp : (rotStep sig.symm ∘ rotStep sig) = id := by
        funext s; simp [rotStep]
      rw [List.map_map, hcomp, List.map_id]
    simp only [loopObs, wilsonLoop_rotate, hx, hp]
  calc ∫ U, loopObs chi (rotSite sig x) (p.map (rotStep sig)) U ∂(gibbs n G beta chi)
      = ∫ U, loopObs chi (rotSite sig x) (p.map (rotStep sig)) (rotate sig U)
          ∂(gibbs n G beta chi) := by
        refine (integral_comp_measurePreserving (measurePreserving_rotate_gibbs hchi beta sig)
          (f := fun U => loopObs chi (rotSite sig x) (p.map (rotStep sig)) U) ?_).symm
        exact (continuous_loopObs hchi _ _).measurable.aestronglyMeasurable
    _ = ∫ U, loopObs chi x p U ∂(gibbs n G beta chi) := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpull)

/-! ## Reflections -/

/-- A reflection in the hyperplane orthogonal to `d0` acting on a directed step:
a step along `d0` reverses its orientation. -/
def refStep (d0 : Fin 4) (s : Step) : Step := if s.1 = d0 then (s.1, !s.2) else s

theorem refStep_refStep (d0 : Fin 4) (s : Step) : refStep d0 (refStep d0 s) = s := by
  cases s with
  | mk d b => by_cases h : d = d0 <;> simp [refStep, h]

theorem refSite_stepShift (d0 : Fin 4) (s : Step) :
    refSite d0 (stepShift n s) = stepShift n (refStep d0 s) := by
  cases s with
  | mk d b =>
    by_cases h : d = d0
    · subst h
      cases b
      · simp [stepShift, refStep, refSite_neg, refSite_unitVec_self]
      · simp [stepShift, refStep, refSite_unitVec_self]
    · cases b
      · simp [stepShift, refStep, h, refSite_neg, refSite_unitVec_ne h]
      · simp [stepShift, refStep, h, refSite_unitVec_ne h]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem stepHol_reflect (d0 : Fin 4) (U : Conf n G) (x : Site n) (s : Step) :
    stepHol (reflect d0 U) x s = stepHol U (refSite d0 x) (refStep d0 s) := by
  cases s with
  | mk d b =>
    by_cases h : d = d0
    · subst h
      have hsub : refSite d (x - unitVec n d) = refSite d x + unitVec n d := by
        rw [refSite_sub, refSite_unitVec_self]; ring
      cases b
      · simp only [stepHol, reflect, refStep, Bool.not_false, hsub]
        simp
      · simp only [stepHol, reflect, refStep, Bool.not_true]
        simp
    · have hsub : refSite d0 (x - unitVec n d) = refSite d0 x - unitVec n d := by
        rw [refSite_sub, refSite_unitVec_ne h]
      cases b
      · simp [stepHol, reflect, refStep, h, hsub]
      · simp [stepHol, reflect, refStep, h]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem pathHol_reflect (d0 : Fin 4) (U : Conf n G) (x : Site n) (p : List Step) :
    pathHol (reflect d0 U) x p = pathHol U (refSite d0 x) (p.map (refStep d0)) := by
  induction p generalizing x with
  | nil => simp
  | cons s p ih =>
      have hshift : refSite d0 (x + stepShift n s)
          = refSite d0 x + stepShift n (refStep d0 s) := by
        rw [refSite_add, refSite_stepShift]
      simp only [List.map_cons, pathHol_cons, ih, stepHol_reflect, hshift]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem wilsonLoop_reflect (chi : G → ℝ) (d0 : Fin 4) (x : Site n) (p : List Step)
    (U : Conf n G) :
    wilsonLoop chi x p (reflect d0 U)
      = wilsonLoop chi (refSite d0 x) (p.map (refStep d0)) U := by
  simp [wilsonLoop, pathHol_reflect]

/-- **Invariance of the Wilson expectation under a reflection in a coordinate
hyperplane**: a Wilson loop and its reflected image have the same
expectation. -/
theorem integral_loopObs_reflect {chi : G → ℝ} (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ) (d0 : Fin 4)
    (x : Site n) (p : List Step) :
    ∫ U, loopObs chi (refSite d0 x) (p.map (refStep d0)) U ∂(gibbs n G beta chi)
      = ∫ U, loopObs chi x p U ∂(gibbs n G beta chi) := by
  have hpull : ∀ U : Conf n G,
      loopObs chi (refSite d0 x) (p.map (refStep d0)) (reflect d0 U) = loopObs chi x p U := by
    intro U
    have hx : refSite d0 (refSite (n := n) d0 x) = x := refSite_refSite d0 x
    have hp : ((p.map (refStep d0)).map (refStep d0)) = p := by
      have hcomp : (refStep d0 ∘ refStep d0) = id := by
        funext s; simp [refStep_refStep]
      rw [List.map_map, hcomp, List.map_id]
    simp only [loopObs, wilsonLoop_reflect, hx, hp]
  calc ∫ U, loopObs chi (refSite d0 x) (p.map (refStep d0)) U ∂(gibbs n G beta chi)
      = ∫ U, loopObs chi (refSite d0 x) (p.map (refStep d0)) (reflect d0 U)
          ∂(gibbs n G beta chi) := by
        refine (integral_comp_measurePreserving
          (measurePreserving_reflect_gibbs hchi hconj beta d0)
          (f := fun U => loopObs chi (refSite d0 x) (p.map (refStep d0)) U) ?_).symm
        exact (continuous_loopObs hchi _ _).measurable.aestronglyMeasurable
    _ = ∫ U, loopObs chi x p U ∂(gibbs n G beta chi) := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpull)

/-! ## The lattice Euclidean group acting on loops -/

/-- **Invariance of the Wilson expectation under a lattice translation of the
loop.** -/
theorem integral_loopObs_translate' {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ)
    (x v : Site n) (p : List Step) :
    ∫ U, loopObs chi (x + v) p U ∂(gibbs n G beta chi)
      = ∫ U, loopObs chi x p U ∂(gibbs n G beta chi) := by
  have hpull : ∀ U : Conf n G, loopObs chi x p (translate v U) = loopObs chi (x + v) p U := by
    intro U; simp [loopObs, wilsonLoop_translate]
  calc ∫ U, loopObs chi (x + v) p U ∂(gibbs n G beta chi)
      = ∫ U, loopObs chi x p (translate v U) ∂(gibbs n G beta chi) :=
        integral_congr_ae (Filter.Eventually.of_forall fun U => (hpull U).symm)
    _ = ∫ U, loopObs chi x p U ∂(gibbs n G beta chi) :=
        integral_comp_measurePreserving (measurePreserving_translate_gibbs hchi beta v)
          (continuous_loopObs hchi _ _).measurable.aestronglyMeasurable

/-- Two based loops are **lattice Euclidean related** when one is carried to the
other by a composition of lattice translations, permutations of the coordinate
axes and reflections in coordinate hyperplanes: the symmetries generating the
Euclidean group of the periodic lattice. -/
inductive EuclideanRelated (n : ℕ) : Site n × List Step → Site n × List Step → Prop
  | rfl' (a : Site n × List Step) : EuclideanRelated n a a
  | translate (x v : Site n) (p : List Step) :
      EuclideanRelated n (x, p) (x + v, p)
  | rotate (x : Site n) (p : List Step) (sig : Equiv.Perm (Fin 4)) :
      EuclideanRelated n (x, p) (rotSite sig x, p.map (rotStep sig))
  | reflect (x : Site n) (p : List Step) (d0 : Fin 4) :
      EuclideanRelated n (x, p) (refSite d0 x, p.map (refStep d0))
  | trans {a b c : Site n × List Step} :
      EuclideanRelated n a b → EuclideanRelated n b c → EuclideanRelated n a c

/-- **Finite-volume Euclidean invariance of the Wilson expectations, loop
form**: Euclidean related loops have the same Wilson expectation at every
cutoff. -/
theorem integral_loopObs_euclidean {chi : G → ℝ} (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ)
    {a b : Site n × List Step} (h : EuclideanRelated n a b) :
    ∫ U, loopObs chi b.1 b.2 U ∂(gibbs n G beta chi)
      = ∫ U, loopObs chi a.1 a.2 U ∂(gibbs n G beta chi) := by
  induction h with
  | rfl' a => rfl
  | translate x v p => exact integral_loopObs_translate' hchi beta x v p
  | rotate x p sig => exact integral_loopObs_rotate hchi beta sig x p
  | reflect x p d0 => exact integral_loopObs_reflect hchi hconj beta d0 x p
  | trans _ _ ih1 ih2 => exact ih2.trans ih1

/-! ## Axiom audit -/

#print axioms integral_loopObs_rotate
#print axioms integral_loopObs_reflect
#print axioms integral_loopObs_euclidean

end RequestProject.YangMills.Lattice
