import LeanDojoJetTransport
import LeanDojoDifferentialTransport
import Problems.Common.Euclidean

/-!
# Coordinate-word derivatives are evaluations of the full Frechet jet

LeanDojo writes Fefferman's force-decay hypotheses using repeated coordinate
partials.  The frozen comparator controls the operator norm of the full
`iteratedFDerivWithin`.  At positive time the closed half-space is a
neighbourhood, so the two are the same derivative after evaluation on standard
basis directions.  This file pays that representation seam; no Navier--Stokes
estimate is used.
-/

noncomputable section

open Filter Set
open NavierStokes
open scoped ContDiff

namespace DASHILiteralClayNS

/-- The coordinate directions selected by a word of Euclidean indices. -/
def coordinateWordDirections {n : ℕ} (α : List (Fin n)) :
    Fin α.length → EuclideanCoordinateSpace ℝ n :=
  fun k => standard_basis (n := n) (α.get k)

@[simp] theorem coordinateWordDirections_nil {n : ℕ} :
    coordinateWordDirections (n := n) [] = Fin.elim0 := by
  funext k
  exact Fin.elim0 k

/-- Local recursive identification of LeanDojo's nested coordinate partials
with evaluation of the ordinary iterated Frechet derivative.  Finite-order
smoothness one order beyond the requested word is enough for the induction. -/
theorem iteratedPartialDeriv_eq_iteratedFDeriv_apply
    {n : ℕ} {f : EuclideanCoordinateSpace ℝ n → ℝ}
    (α : List (Fin n)) (x : EuclideanCoordinateSpace ℝ n)
    (hf : ContDiffAt ℝ (α.length + 1 : ℕ) f x) :
    iterated_partial_deriv (n := n) α f x =
      iteratedFDeriv ℝ α.length f x (coordinateWordDirections α) := by
  induction α generalizing x with
  | nil =>
      simp [iterated_partial_deriv, coordinateWordDirections]
  | cons i α ih =>
      rw [iterated_partial_deriv]
      let g : EuclideanCoordinateSpace ℝ n → ℝ :=
        fun y => iteratedFDeriv ℝ α.length f y (coordinateWordDirections α)
      have hnear :
          (fun y => iterated_partial_deriv (n := n) α f y) =ᶠ[𝓝 x] g := by
        have hev := hf.eventually (by simp)
        filter_upwards [hev] with y hy
        exact ih y (hy.of_le (by simp))
      rw [partial_deriv_eq_fderiv_apply]
      rw [hnear.fderiv_eq]
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ α.length f) x :=
        hf.differentiableAt_iteratedFDeriv (by
          simp only [Nat.cast_add, Nat.cast_one]
          exact_mod_cast Nat.lt_succ_self α.length)
      rw [show fderiv ℝ g x (standard_basis (n := n) i) =
          (fderiv ℝ (iteratedFDeriv ℝ α.length f) x
            (standard_basis (n := n) i)) (coordinateWordDirections α) by
        exact fderiv_continuousMultilinear_apply_const_apply
          hdiff (coordinateWordDirections α) (standard_basis (n := n) i)]
      rw [← iteratedFDeriv_succ_apply_left]
      congr 1
      funext k
      refine Fin.cases ?_ ?_ k
      · rfl
      · intro j
        rfl

/-- Operator-norm consequence: every displayed coordinate word is bounded by
the norm of the full jet because every standard basis direction has norm one. -/
theorem norm_iteratedPartialDeriv_le_fullJet
    {n : ℕ} {f : EuclideanCoordinateSpace ℝ n → ℝ}
    (α : List (Fin n)) (x : EuclideanCoordinateSpace ℝ n)
    (hf : ContDiffAt ℝ (α.length + 1 : ℕ) f x) :
    ‖iterated_partial_deriv (n := n) α f x‖ ≤
      ‖iteratedFDeriv ℝ α.length f x‖ := by
  rw [iteratedPartialDeriv_eq_iteratedFDeriv_apply α x hf]
  calc
    ‖iteratedFDeriv ℝ α.length f x (coordinateWordDirections α)‖ ≤
        ‖iteratedFDeriv ℝ α.length f x‖ *
          ∏ k : Fin α.length, ‖coordinateWordDirections α k‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ α.length f x‖ := by
      simp [coordinateWordDirections, standard_basis]

end DASHILiteralClayNS
