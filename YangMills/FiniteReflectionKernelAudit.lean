import Mathlib

/-!
# Finite reflection kernel audit: positivity of a Gibbs weight is NOT OS positivity

Reflection positivity is the positivity of the *matrix* whose rows/columns
index positive-time observables.  A strictly positive pointwise Gibbs
density does not imply this matrix is positive semidefinite.

This file proves a concrete two-state counterexample, then proves a
source-applicable sufficient condition: a reflected product of separate
positive-half contributions preserves every pre-existing finite Gram
inequality.  In particular, a regular/R/boundary/vacuum CMP119 correction
which crosses the reflection plane cannot be dropped or treated as
reflection-positive merely because exp(-S) is positive.

Everything here is a finite exact algebra calculation.  The *physical*
source obligation is to show that the selected complete action has a
suitable reflection-plane decomposition (or a positive character/kernel
expansion).  Nothing in this file assumes such a decomposition exists.
-/

namespace RequestProject.YangMills

/-- Reflected real Gram form on a finite positive-half configuration space. -/
def finiteReflectionGram
    {X : Type*} (sites : Finset X) (K : X → X → ℝ)
    (test : X → ℝ) : ℝ :=
  ∑ x ∈ sites, ∑ y ∈ sites,
    test x * K x y * test y

/-- A strictly positive pointwise kernel need not be positive semidefinite. -/
def twoStatePositiveKernel (x y : Fin 2) : ℝ :=
  if x = y then 1 else 2

/-- The odd two-state positive-time probe. -/
def twoStateOddTest (x : Fin 2) : ℝ :=
  if x = 0 then 1 else -1

theorem two_state_kernel_strictly_positive (x y : Fin 2) :
    0 < twoStatePositiveKernel x y := by
  unfold twoStatePositiveKernel
  split_ifs <;> norm_num

/--
The strict positivity of the full (two-half) density does not imply
reflection positivity: the odd probe has *negative* Gram square.
-/
theorem positive_gibbs_density_not_enough_for_os2 :
    finiteReflectionGram (Finset.univ : Finset (Fin 2))
      twoStatePositiveKernel twoStateOddTest = -2 := by
  simp [finiteReflectionGram, twoStatePositiveKernel,
    twoStateOddTest, Fin.sum_univ_two]
  norm_num

/-- A product of one half-space weight and its reflected copy. -/
def multiplyReflectedHalfWeights
    {X : Type*} (K : X → X → ℝ) (halfWeight : X → ℝ) :
    X → X → ℝ :=
  fun x y => halfWeight x * K x y * halfWeight y

/--
Reweighting the two sides of the reflected kernel is EXACTLY
reweighting the test observable.  Consequently positivity of the
original Gram survives without any new positivity assumption.
-/
theorem finite_reflection_gram_half_weight_identity
    {X : Type*} (sites : Finset X) (K : X → X → ℝ)
    (halfWeight test : X → ℝ) :
    finiteReflectionGram sites
      (multiplyReflectedHalfWeights K halfWeight) test =
    finiteReflectionGram sites K (fun x => test x * halfWeight x) := by
  unfold finiteReflectionGram multiplyReflectedHalfWeights
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

/--
The reflection-positive cone is closed under reflected multiplication
by a half-space weight, regardless of its sign.  Source action
corrections of form S_+(x)+S_+(y) yield such weights via exp(-S_+).

A cross-plane correction S_cross(x,y) requires its OWN kernel
positivity, not merely boundedness of its action.
-/
theorem finite_reflection_positive_of_half_factorization
    {X : Type*} (sites : Finset X) (K : X → X → ℝ)
    (halfWeight : X → ℝ)
    (hRP : ∀ test : X → ℝ,
      0 ≤ finiteReflectionGram sites K test) :
    ∀ test : X → ℝ,
      0 ≤ finiteReflectionGram sites
        (multiplyReflectedHalfWeights K halfWeight) test := by
  intro test
  rw [finite_reflection_gram_half_weight_identity]
  exact hRP _

/--
Exact exponential factorization when a COMPLETE selected
regular/R/boundary/vacuum residual splits across the reflection plane.
The difficult step is showing that the CMP119 source actually has this
property, especially for boundary-crossing RG terms.
-/
theorem exp_reflected_additive_action_factorization
    {X : Type*} (halfAction : X → ℝ) (x y : X) :
    Real.exp (-(halfAction x + halfAction y)) =
      Real.exp (-halfAction x) * Real.exp (-halfAction y) := by
  rw [neg_add, Real.exp_add]

/--
If the residual effective action is exactly the sum of two
reflection-related half-actions, then multiplying any baseline
reflection-positive Wilson kernel by its full Gibbs weight keeps OS2.
No assertion is made about the actual CMP119 effective action until
the decomposition is verified directly on the source.
-/
theorem finite_reflection_positive_of_additive_residual
    {X : Type*} (sites : Finset X)
    (wilsonKernel : X → X → ℝ)
    (halfAction : X → ℝ)
    (hWilsonRP : ∀ test : X → ℝ,
      0 ≤ finiteReflectionGram sites wilsonKernel test) :
    ∀ test : X → ℝ,
      0 ≤ finiteReflectionGram sites
        (fun x y => wilsonKernel x y *
          Real.exp (-(halfAction x + halfAction y))) test := by
  intro test
  have hEq :
      (fun x y => wilsonKernel x y *
        Real.exp (-(halfAction x + halfAction y))) =
      multiplyReflectedHalfWeights wilsonKernel
        (fun x => Real.exp (-halfAction x)) := by
    funext x y
    rw [exp_reflected_additive_action_factorization]
    dsimp [multiplyReflectedHalfWeights]
    ring
  rw [hEq]
  exact finite_reflection_positive_of_half_factorization
    sites wilsonKernel _ hWilsonRP test

end RequestProject.YangMills
