import Mathlib

/-!
# Independent Clay Navier–Stokes specification

Normative source: Charles L. Fefferman, *Existence and Smoothness of the
Navier–Stokes Equation*, official Clay Mathematics Institute problem statement,
including the erratum printed at the end of the PDF.

This file intentionally imports Mathlib only.  It was written and frozen before
the clause-by-clause comparison with OpenAI's `ComparatorDefinitions.lean`.

Interpretation choices are isolated in the declarations carrying the
`TrustBoundary` prefix.  In particular, smoothness on the closed time half-space
is represented by Mathlib's `ContDiffOn`, and the conventional multi-index
notation is represented by finite words of coordinate directions.  The latter
contains every repeated coordinate derivative occurring in a multi-index.
-/

noncomputable section

open scoped Topology
open MeasureTheory Set
open ContDiff

namespace ClaySpec

abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev SpaceTime := R3 × ℝ
abbrev Velocity := SpaceTime → R3
abbrev Pressure := SpaceTime → ℝ
abbrev InitialVelocity := R3 → R3
abbrev Force := SpaceTime → R3

/-! ## Domain and coordinate derivatives -/

/-- The domain `ℝ³ × [0, ∞)` in the Clay statement. -/
def nonnegativeTime : Set SpaceTime := {z | 0 ≤ z.2}

/-- The `i`-th Euclidean coordinate vector in `ℝ³`. -/
def spatialBasis (i : Fin 3) : R3 := EuclideanSpace.single i 1

/-- The spatial coordinate direction `(eᵢ, 0)` in space-time. -/
def spatialDirection (i : Fin 3) : SpaceTime := (spatialBasis i, 0)

/-- The positive time direction `(0, 1)` in space-time. -/
def timeDirection : SpaceTime := (0, 1)

/--
TRUST BOUNDARY (closed-half-space smoothness): throughout this specification,
`C∞(ℝ³ × [0,∞))` means `ContDiffOn ℝ ∞` on `nonnegativeTime`.
-/
def TrustBoundarySmoothOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : SpaceTime → E) : Prop :=
  ContDiffOn ℝ ∞ g nonnegativeTime

/-- Iterated Fréchet directional derivatives on the closed time half-space. -/
def iteratedDirectionalWithin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    List SpaceTime → (SpaceTime → E) → SpaceTime → E
  | [], g => g
  | v :: vs, g => fun z =>
      fderivWithin ℝ (iteratedDirectionalWithin vs g) nonnegativeTime z v

/-- Iterated Fréchet directional derivatives on all of `ℝ³`. -/
def iteratedSpatialDirectional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    List R3 → (R3 → E) → R3 → E
  | [], g => g
  | v :: vs, g => fun x => fderiv ℝ (iteratedSpatialDirectional vs g) x v

/--
TRUST BOUNDARY (multi-index notation): a Clay spatial multi-index is encoded by
a finite word in the three coordinate directions.  Repetition records the
coordinate multiplicities.  Smoothness makes the ordering immaterial, but no
quotient by permutations is needed by the statement below.
-/
abbrev TrustBoundarySpatialMultiIndex := List (Fin 3)

def spatialWord (α : TrustBoundarySpatialMultiIndex) : List SpaceTime :=
  α.map spatialDirection

def initialSpatialWord (α : TrustBoundarySpatialMultiIndex) : List R3 :=
  α.map spatialBasis

/-- The derivative `∂ₓ^α ∂ₜ^m`, represented as a word of directions. -/
def mixedWord (α : TrustBoundarySpatialMultiIndex) (m : ℕ) : List SpaceTime :=
  spatialWord α ++ List.replicate m timeDirection

def partialSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (g : SpaceTime → E) (z : SpaceTime) : E :=
  fderivWithin ℝ g nonnegativeTime z (spatialDirection i)

def partialTime {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : SpaceTime → E) (z : SpaceTime) : E :=
  fderivWithin ℝ g nonnegativeTime z timeDirection

/-! ## Equations (1)--(3) -/

/-- `div u`, equation (2), written component by component. -/
def divergence (u : Velocity) (z : SpaceTime) : ℝ :=
  ∑ i : Fin 3, partialSpace i (fun w => u w i) z

/-- The spatial Laplacian of velocity component `i`. -/
def spatialLaplacianComponent (u : Velocity) (i : Fin 3) (z : SpaceTime) : ℝ :=
  ∑ j : Fin 3, partialSpace j (partialSpace j (fun w => u w i)) z

/-- The component `i` of `(u · ∇)u`. -/
def convectionComponent (u : Velocity) (i : Fin 3) (z : SpaceTime) : ℝ :=
  ∑ j : Fin 3, u z j * partialSpace j (fun w => u w i) z

/-- Equation (1), for all three components and all nonnegative times. -/
def EquationOne (ν : ℝ) (u : Velocity) (p : Pressure) (f : Force) : Prop :=
  ∀ z ∈ nonnegativeTime, ∀ i : Fin 3,
    partialTime (fun w => u w i) z + convectionComponent u i z =
      ν * spatialLaplacianComponent u i z - partialSpace i p z + f z i

/-- Equation (2): incompressibility for nonnegative time. -/
def EquationTwo (u : Velocity) : Prop :=
  ∀ z ∈ nonnegativeTime, divergence u z = 0

/-- Equation (3): the prescribed initial velocity. -/
def EquationThree (u₀ : InitialVelocity) (u : Velocity) : Prop :=
  ∀ x : R3, u (x, 0) = u₀ x

/-! ## Data conditions (4), (5), (8), and (9) -/

def initialDivergence (u₀ : InitialVelocity) (x : R3) : ℝ :=
  ∑ i : Fin 3,
    fderiv ℝ (fun y => u₀ y i) x (spatialBasis i)

def InitialDivergenceFree (u₀ : InitialVelocity) : Prop :=
  ∀ x : R3, initialDivergence u₀ x = 0

/-- Equation (4): rapid spatial decay of every coordinate derivative. -/
def InitialRapidDecay (u₀ : InitialVelocity) : Prop :=
  ∀ (α : TrustBoundarySpatialMultiIndex) (K : ℕ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3,
      ‖iteratedSpatialDirectional (initialSpatialWord α) u₀ x‖ ≤
        C / (1 + ‖x‖) ^ K

/-- Equation (5): rapid joint space-time decay of every displayed derivative. -/
def ForceRapidDecayR3 (f : Force) : Prop :=
  ∀ (α : TrustBoundarySpatialMultiIndex) (m K : ℕ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ nonnegativeTime,
      ‖iteratedDirectionalWithin (mixedWord α m) f z‖ ≤
        C / (1 + ‖z.1‖ + z.2) ^ K

def SpatiallyPeriodicInitial (u₀ : InitialVelocity) : Prop :=
  ∀ (x : R3) (j : Fin 3), u₀ (x + spatialBasis j) = u₀ x

def SpatiallyPeriodic {E : Type*} (g : SpaceTime → E) : Prop :=
  ∀ z ∈ nonnegativeTime, ∀ j : Fin 3,
    g (z.1 + spatialBasis j, z.2) = g z

/-- Equation (9): every force derivative decays rapidly in time, uniformly in space. -/
def ForceRapidDecayPeriodic (f : Force) : Prop :=
  ∀ (α : TrustBoundarySpatialMultiIndex) (m K : ℕ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ nonnegativeTime,
      ‖iteratedDirectionalWithin (mixedWord α m) f z‖ ≤
        C / (1 + |z.2|) ^ K

/-! ## Accepted solutions: (6), (7), (10), (11), and the erratum -/

/--
Equation (7).  `MemLp` records that the displayed Lebesgue integral is genuine;
one constant `C` bounds the energy for every `t ≥ 0`, as required by the words
“bounded energy”.
-/
def BoundedEnergy (u : Velocity) : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
    MemLp (fun x : R3 => u (x, t)) 2 volume ∧
      (∫ x : R3, ‖u (x, t)‖ ^ 2 ∂volume) < C

/-- Conditions (6) and (7), together with equations (1)--(3). -/
def ClaySolutionR3 (ν : ℝ) (u₀ : InitialVelocity) (f : Force)
    (u : Velocity) (p : Pressure) : Prop :=
  TrustBoundarySmoothOn u ∧
  TrustBoundarySmoothOn p ∧
  EquationOne ν u p f ∧
  EquationTwo u ∧
  EquationThree u₀ u ∧
  BoundedEnergy u

/--
Conditions (10), (11), and the official erratum.  The erratum requires the
pressure, as well as the velocity, to be spatially periodic.
-/
def ClaySolutionPeriodic (ν : ℝ) (u₀ : InitialVelocity) (f : Force)
    (u : Velocity) (p : Pressure) : Prop :=
  TrustBoundarySmoothOn u ∧
  TrustBoundarySmoothOn p ∧
  EquationOne ν u p f ∧
  EquationTwo u ∧
  EquationThree u₀ u ∧
  SpatiallyPeriodic u ∧
  SpatiallyPeriodic p

def AdmissibleDataR3 (u₀ : InitialVelocity) (f : Force) : Prop :=
  ContDiff ℝ ∞ u₀ ∧
  InitialDivergenceFree u₀ ∧
  InitialRapidDecay u₀ ∧
  TrustBoundarySmoothOn f ∧
  ForceRapidDecayR3 f

def AdmissibleDataPeriodic (u₀ : InitialVelocity) (f : Force) : Prop :=
  ContDiff ℝ ∞ u₀ ∧
  InitialDivergenceFree u₀ ∧
  SpatiallyPeriodicInitial u₀ ∧
  TrustBoundarySmoothOn f ∧
  SpatiallyPeriodic f ∧
  ForceRapidDecayPeriodic f

/-! ## Alternatives (C) and (D) -/

/-- Fefferman alternative (C), with the quantifier order printed in the PDF. -/
def ClayOptionC : Prop :=
  ∀ ν : ℝ, 0 < ν →
    ∃ u₀ : InitialVelocity, ∃ f : Force,
      AdmissibleDataR3 u₀ f ∧
      ¬ ∃ u : Velocity, ∃ p : Pressure, ClaySolutionR3 ν u₀ f u p

/-- Fefferman alternative (D), including pressure periodicity from the erratum. -/
def ClayOptionD : Prop :=
  ∀ ν : ℝ, 0 < ν →
    ∃ u₀ : InitialVelocity, ∃ f : Force,
      AdmissibleDataPeriodic u₀ f ∧
      ¬ ∃ u : Velocity, ∃ p : Pressure, ClaySolutionPeriodic ν u₀ f u p

end ClaySpec
