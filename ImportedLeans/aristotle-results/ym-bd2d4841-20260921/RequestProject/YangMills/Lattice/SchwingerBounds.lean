/-
# The lattice Wilson Schwinger functions: uniform bounds and Euclidean invariance

The finite-volume Schwinger functions of the literal Wilson sector are the
expectations of products of Wilson-loop observables,

    S(C₁,…,C_m) = E[ W_{C₁} ⋯ W_{C_m} ].

This file proves, for arbitrary order `m`, the two properties that the continuum
limit consumes:

* `norm_integral_prod_loopObs_le` — the *cutoff-uniform* bound `|S| ≤ M^m`,
  where `M` bounds the character.  No coupling condition and no volume
  condition: this is the regularity/temperedness input of the Wilson sector, and
  it is uniform in the lattice size and in the coupling.
* `integral_prod_loopObs_translate`, `integral_prod_loopObs_rotate`,
  `integral_prod_loopObs_reflect` — Euclidean invariance: moving *all* the loops
  by one lattice translation, one permutation of the coordinate axes or one
  reflection in a coordinate hyperplane leaves the Schwinger function unchanged.

Both are proved from the Wilson–Gibbs measure itself, with no placeholder.
-/
import Mathlib
import RequestProject.YangMills.Lattice.HypercubicLoop
import RequestProject.YangMills.RouteS.UniformBounds

namespace RequestProject.YangMills.Lattice

open MeasureTheory
open RequestProject.YangMills.RouteS

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

variable {n m : ℕ}

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
/-- The product of `m` Wilson-loop observables is bounded by `M ^ m`. -/
theorem norm_prod_loopObs_le {chi : G → ℝ} {M : ℝ} (hM : ∀ g : G, |chi g| ≤ M)
    (x : Fin m → Site n) (p : Fin m → List Step) (U : Conf n G) :
    ‖∏ i, loopObs chi (x i) (p i) U‖ ≤ M ^ m := by
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM 1)
  calc ‖∏ i, loopObs chi (x i) (p i) U‖
      = ∏ i, ‖loopObs chi (x i) (p i) U‖ := by rw [norm_prod]
    _ ≤ ∏ _i : Fin m, M :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _)
          (fun i _ => norm_loopObs_le hM (x i) (p i) U)
    _ = M ^ m := by simp

omit [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
/-- Products of Wilson-loop observables are continuous. -/
theorem continuous_prod_loopObs {chi : G → ℝ} (hchi : Continuous chi)
    (x : Fin m → Site n) (p : Fin m → List Step) :
    Continuous fun U : Conf n G => ∏ i, loopObs chi (x i) (p i) U :=
  continuous_finset_prod _ fun i _ => continuous_loopObs hchi (x i) (p i)

/-- **Cutoff-uniform bound on the literal Wilson Schwinger functions.**  At
every lattice size, every coupling and every family of loops, the Wilson–Gibbs
expectation of a product of `m` Wilson loops is bounded by `M ^ m`. -/
theorem norm_integral_prod_loopObs_le {chi : G → ℝ} (hchi : Continuous chi) {M : ℝ}
    (hM : ∀ g : G, |chi g| ≤ M) (beta : ℝ) (x : Fin m → Site n) (p : Fin m → List Step) :
    ‖∫ U, (∏ i, loopObs chi (x i) (p i) U) ∂(gibbs n G beta chi)‖ ≤ M ^ m := by
  haveI := isProbabilityMeasure_gibbs (n := n) (G := G) hchi beta
  have h := norm_integral_le_of_norm_le_const (μ := gibbs n G beta chi)
    (f := fun U => ∏ i, loopObs chi (x i) (p i) U) (C := M ^ m)
    (Filter.Eventually.of_forall fun U => norm_prod_loopObs_le hM x p U)
  simpa using h

/-! ## Euclidean invariance of the Schwinger functions -/

/-- **Translation invariance of the Wilson Schwinger functions.** -/
theorem integral_prod_loopObs_translate {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ)
    (v : Site n) (x : Fin m → Site n) (p : Fin m → List Step) :
    ∫ U, (∏ i, loopObs chi (x i + v) (p i) U) ∂(gibbs n G beta chi)
      = ∫ U, (∏ i, loopObs chi (x i) (p i) U) ∂(gibbs n G beta chi) := by
  have hpull : ∀ U : Conf n G,
      (∏ i, loopObs chi (x i) (p i) (translate v U)) = ∏ i, loopObs chi (x i + v) (p i) U := by
    intro U
    exact Finset.prod_congr rfl fun i _ => by simp [loopObs, wilsonLoop_translate]
  calc ∫ U, (∏ i, loopObs chi (x i + v) (p i) U) ∂(gibbs n G beta chi)
      = ∫ U, (∏ i, loopObs chi (x i) (p i) (translate v U)) ∂(gibbs n G beta chi) :=
        integral_congr_ae (Filter.Eventually.of_forall fun U => (hpull U).symm)
    _ = ∫ U, (∏ i, loopObs chi (x i) (p i) U) ∂(gibbs n G beta chi) :=
        integral_comp_measurePreserving (measurePreserving_translate_gibbs hchi beta v)
          (continuous_prod_loopObs hchi x p).measurable.aestronglyMeasurable

/-- **Invariance of the Wilson Schwinger functions under a permutation of the
coordinate axes.** -/
theorem integral_prod_loopObs_rotate {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ)
    (sig : Equiv.Perm (Fin 4)) (x : Fin m → Site n) (p : Fin m → List Step) :
    ∫ U, (∏ i, loopObs chi (rotSite sig (x i)) ((p i).map (rotStep sig)) U)
        ∂(gibbs n G beta chi)
      = ∫ U, (∏ i, loopObs chi (x i) (p i) U) ∂(gibbs n G beta chi) := by
  have hcomp : (rotStep sig.symm ∘ rotStep sig) = id := by funext s; simp [rotStep]
  have hpull : ∀ U : Conf n G,
      (∏ i, loopObs chi (rotSite sig (x i)) ((p i).map (rotStep sig)) (rotate sig U))
        = ∏ i, loopObs chi (x i) (p i) U := by
    intro U
    refine Finset.prod_congr rfl fun i _ => ?_
    have hx : rotSite sig.symm (rotSite (n := n) sig (x i)) = x i := rotSite_leftInverse sig (x i)
    have hp : (((p i).map (rotStep sig)).map (rotStep sig.symm)) = p i := by
      rw [List.map_map, hcomp, List.map_id]
    simp only [loopObs, wilsonLoop_rotate, hx, hp]
  calc ∫ U, (∏ i, loopObs chi (rotSite sig (x i)) ((p i).map (rotStep sig)) U)
          ∂(gibbs n G beta chi)
      = ∫ U, (∏ i, loopObs chi (rotSite sig (x i)) ((p i).map (rotStep sig)) (rotate sig U))
          ∂(gibbs n G beta chi) := by
        refine (integral_comp_measurePreserving (measurePreserving_rotate_gibbs hchi beta sig)
          (f := fun U => ∏ i, loopObs chi (rotSite sig (x i)) ((p i).map (rotStep sig)) U) ?_).symm
        exact (continuous_prod_loopObs hchi _ _).measurable.aestronglyMeasurable
    _ = ∫ U, (∏ i, loopObs chi (x i) (p i) U) ∂(gibbs n G beta chi) :=
        integral_congr_ae (Filter.Eventually.of_forall hpull)

/-- **Invariance of the Wilson Schwinger functions under a reflection in a
coordinate hyperplane.** -/
theorem integral_prod_loopObs_reflect {chi : G → ℝ} (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ) (d0 : Fin 4)
    (x : Fin m → Site n) (p : Fin m → List Step) :
    ∫ U, (∏ i, loopObs chi (refSite d0 (x i)) ((p i).map (refStep d0)) U)
        ∂(gibbs n G beta chi)
      = ∫ U, (∏ i, loopObs chi (x i) (p i) U) ∂(gibbs n G beta chi) := by
  have hcomp : (refStep d0 ∘ refStep d0) = id := by funext s; simp [refStep_refStep]
  have hpull : ∀ U : Conf n G,
      (∏ i, loopObs chi (refSite d0 (x i)) ((p i).map (refStep d0)) (reflect d0 U))
        = ∏ i, loopObs chi (x i) (p i) U := by
    intro U
    refine Finset.prod_congr rfl fun i _ => ?_
    have hx : refSite d0 (refSite (n := n) d0 (x i)) = x i := refSite_refSite d0 (x i)
    have hp : (((p i).map (refStep d0)).map (refStep d0)) = p i := by
      rw [List.map_map, hcomp, List.map_id]
    simp only [loopObs, wilsonLoop_reflect, hx, hp]
  calc ∫ U, (∏ i, loopObs chi (refSite d0 (x i)) ((p i).map (refStep d0)) U)
          ∂(gibbs n G beta chi)
      = ∫ U, (∏ i, loopObs chi (refSite d0 (x i)) ((p i).map (refStep d0)) (reflect d0 U))
          ∂(gibbs n G beta chi) := by
        refine (integral_comp_measurePreserving
          (measurePreserving_reflect_gibbs hchi hconj beta d0)
          (f := fun U => ∏ i, loopObs chi (refSite d0 (x i)) ((p i).map (refStep d0)) U) ?_).symm
        exact (continuous_prod_loopObs hchi _ _).measurable.aestronglyMeasurable
    _ = ∫ U, (∏ i, loopObs chi (x i) (p i) U) ∂(gibbs n G beta chi) :=
        integral_congr_ae (Filter.Eventually.of_forall hpull)

/-! ## Compositions of lattice Euclidean moves -/

/-- A generator of the Euclidean group of the periodic lattice. -/
inductive LatticeMove (n : ℕ) where
  | translate (v : Site n)
  | rotate (sig : Equiv.Perm (Fin 4))
  | reflect (d0 : Fin 4)

/-- The action of a generator on a base point. -/
def LatticeMove.onSite : LatticeMove n → Site n → Site n
  | .translate v, x => x + v
  | .rotate sig, x => rotSite sig x
  | .reflect d0, x => refSite d0 x

/-- The action of a generator on the steps of a loop. -/
def LatticeMove.onPath : LatticeMove n → List Step → List Step
  | .translate _, p => p
  | .rotate sig, p => p.map (rotStep sig)
  | .reflect d0, p => p.map (refStep d0)

/-- The base point moved by a composition of generators. -/
def moveSite (gs : List (LatticeMove n)) (x : Site n) : Site n :=
  gs.foldl (fun y g => g.onSite y) x

/-- The steps moved by a composition of generators. -/
def movePath (gs : List (LatticeMove n)) (p : List Step) : List Step :=
  gs.foldl (fun q g => g.onPath q) p

@[simp] theorem moveSite_nil (x : Site n) : moveSite ([] : List (LatticeMove n)) x = x := rfl

@[simp] theorem movePath_nil (p : List Step) :
    movePath ([] : List (LatticeMove n)) p = p := rfl

@[simp] theorem moveSite_cons (g : LatticeMove n) (gs : List (LatticeMove n)) (x : Site n) :
    moveSite (g :: gs) x = moveSite gs (g.onSite x) := rfl

@[simp] theorem movePath_cons (g : LatticeMove n) (gs : List (LatticeMove n)) (p : List Step) :
    movePath (g :: gs) p = movePath gs (g.onPath p) := rfl

/-- **Invariance of the Wilson Schwinger functions under one Euclidean
generator applied to all the loops.** -/
theorem integral_prod_loopObs_move {chi : G → ℝ} (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ) (g : LatticeMove n)
    (x : Fin m → Site n) (p : Fin m → List Step) :
    ∫ U, (∏ i, loopObs chi (g.onSite (x i)) (g.onPath (p i)) U) ∂(gibbs n G beta chi)
      = ∫ U, (∏ i, loopObs chi (x i) (p i) U) ∂(gibbs n G beta chi) := by
  cases g with
  | translate v => exact integral_prod_loopObs_translate hchi beta v x p
  | rotate sig => exact integral_prod_loopObs_rotate hchi beta sig x p
  | reflect d0 => exact integral_prod_loopObs_reflect hchi hconj beta d0 x p

/-- **Invariance of the Wilson Schwinger functions under any lattice Euclidean
transformation applied to all the loops.** -/
theorem integral_prod_loopObs_moves {chi : G → ℝ} (hchi : Continuous chi)
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (beta : ℝ) (gs : List (LatticeMove n))
    (x : Fin m → Site n) (p : Fin m → List Step) :
    ∫ U, (∏ i, loopObs chi (moveSite gs (x i)) (movePath gs (p i)) U) ∂(gibbs n G beta chi)
      = ∫ U, (∏ i, loopObs chi (x i) (p i) U) ∂(gibbs n G beta chi) := by
  induction gs generalizing x p with
  | nil => simp
  | cons g gs ih =>
      simp only [moveSite_cons, movePath_cons]
      rw [ih (fun i => g.onSite (x i)) (fun i => g.onPath (p i))]
      exact integral_prod_loopObs_move hchi hconj beta g x p

/-! ## Axiom audit -/

#print axioms integral_prod_loopObs_moves
#print axioms norm_integral_prod_loopObs_le
#print axioms integral_prod_loopObs_translate
#print axioms integral_prod_loopObs_rotate
#print axioms integral_prod_loopObs_reflect

end RequestProject.YangMills.Lattice
