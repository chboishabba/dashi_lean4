import Integration.MoonshineNormalizedJPhaseReadout
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Tactic

/-!
# Boundary-safe C6 observer on Real.Angle

The normalized-j lane already owns the exact continuous reflection law

  jPhase(reflect τ) = -jPhase(τ)

in `Real.Angle`.  This file supplies the missing finite presentation layer:
six open sectors of angular radius π/6 around the six sixth-root directions.

The observer is deliberately *boundary-safe*: a point is observed only together
with a proof that it lies strictly inside a chosen sector.  Therefore no
arbitrary tie-break at sector boundaries enters the reflection theorem.

This is the minimal finite phase observer needed by the canonical fibred
renderer.  No phase-9 or phase-27 quantizer is introduced.
-/

namespace Integration.MoonshineAngleC6SectorObserver

open Real
open scoped Real

noncomputable section

namespace J
abbrev jPhase := Integration.MoonshineNormalizedJPhaseReadout.jPhase
abbrev jValue := Integration.MoonshineNormalizedJPhaseReadout.jValue
abbrev reflectTau (τ : ℍ) : ℍ :=
  ModularGroup.S • Integration.MoonshineEisensteinAgdaTarget.negConj τ

theorem jPhase_reflects :=
  Integration.MoonshineNormalizedJPhaseReadout.jPhase_reflects
end J

/-- Six oriented phase sectors. -/
inductive C6Sector
  | s0 | s1 | s2 | s3 | s4 | s5
  deriving DecidableEq, Repr

/-- Modular/conjugation reflection k ↦ -k mod 6. -/
def reflect6 : C6Sector → C6Sector
  | .s0 => .s0
  | .s1 => .s5
  | .s2 => .s4
  | .s3 => .s3
  | .s4 => .s2
  | .s5 => .s1

@[simp] theorem reflect6_involutive (s : C6Sector) :
    reflect6 (reflect6 s) = s := by
  cases s <;> rfl

/-- The six sector centres as genuine angles modulo one turn. -/
def centre : C6Sector → Real.Angle
  | .s0 => (0 : ℝ)
  | .s1 => (Real.pi / 3 : ℝ)
  | .s2 => (2 * Real.pi / 3 : ℝ)
  | .s3 => (Real.pi : ℝ)
  | .s4 => (-2 * Real.pi / 3 : ℝ)
  | .s5 => (-Real.pi / 3 : ℝ)

@[simp] theorem centre_reflect (s : C6Sector) :
    centre (reflect6 s) = - centre s := by
  cases s <;>
    simp [centre, reflect6, ← Real.Angle.coe_neg, ← Real.Angle.coe_add,
      ← Real.Angle.coe_sub] <;>
    ring_nf

/-- Strict sector interior: angular distance from the selected centre is < π/6.

Using `toReal` only on the *difference angle* makes this branch-safe on the
circle; `abs_toReal_neg` is exactly the reflection lemma we need.
-/
def InSector (θ : Real.Angle) (s : C6Sector) : Prop :=
  |(θ - centre s).toReal| < Real.pi / 6

/-- Reflection transports strict sector membership exactly. -/
theorem inSector_neg_iff (θ : Real.Angle) (s : C6Sector) :
    InSector (-θ) (reflect6 s) ↔ InSector θ s := by
  unfold InSector
  have hangle :
      -θ - centre (reflect6 s) = -(θ - centre s) := by
    rw [centre_reflect]
    abel
  rw [hangle, Real.Angle.abs_toReal_neg]

/-- A phase supplied with a strict-sector certificate.

The sector proof is data precisely because boundary points should not be
silently assigned by a presentation convention.
-/
structure BoundarySafePhase where
  angle : Real.Angle
  sector : C6Sector
  interior : InSector angle sector

/-- The actual finite observer on its certified domain. -/
def observe6 (x : BoundarySafePhase) : C6Sector :=
  x.sector

/-- Reflect a certified phase without any boundary convention. -/
def reflectSafe (x : BoundarySafePhase) : BoundarySafePhase where
  angle := -x.angle
  sector := reflect6 x.sector
  interior := (inSector_neg_iff x.angle x.sector).2 x.interior

/-- The finite observer intertwines exact angle negation with k ↦ -k mod 6. -/
theorem observe6_reflects (x : BoundarySafePhase) :
    observe6 (reflectSafe x) = reflect6 (observe6 x) :=
  rfl

/-- A normalized-j point with a certified C6 sector. -/
structure SafeJPhasePoint where
  tau : ℍ
  sector : C6Sector
  interior : InSector (J.jPhase tau) sector

/-- Canonical analytic reflection point used by the normalized-j lane. -/
def reflectTau (τ : ℍ) : ℍ :=
  J.reflectTau τ

/-- Continuous normalized-j reflection carries an interior C6 sector to its
finite reflected sector. -/
theorem jPhase_reflection_preserves_safe_sector
    (x : SafeJPhasePoint) :
    InSector (J.jPhase (reflectTau x.tau)) (reflect6 x.sector) := by
  rw [reflectTau, J.jPhase_reflects]
  exact (inSector_neg_iff (J.jPhase x.tau) x.sector).2 x.interior

/-- The certified normalized-j C6 observer after reflection. -/
def reflectSafeJPhasePoint (x : SafeJPhasePoint) : SafeJPhasePoint where
  tau := reflectTau x.tau
  sector := reflect6 x.sector
  interior := jPhase_reflection_preserves_safe_sector x

def observeJ6 (x : SafeJPhasePoint) : C6Sector :=
  x.sector

theorem observeJ6_reflects (x : SafeJPhasePoint) :
    observeJ6 (reflectSafeJPhasePoint x) = reflect6 (observeJ6 x) :=
  rfl

/-- The theorem closes the *reflection* min-cut, but does not choose a sector
for phase values sitting exactly on a π/6 boundary. -/
structure C6SectorObserverBoundary where
  continuousAngleReadoutOwned : Bool
  sixOpenSectorsConstructed : Bool
  exactNegationEquivarianceOwned : Bool
  normalizedJReflectionIntertwinerOwned : Bool
  phaseC6ObserverBoundarySafe : Bool
  boundaryTieBreakChosen : Bool
  phase9QuantizerNeeded : Bool
  phase27QuantizerNeeded : Bool
  deriving Repr

def c6SectorObserverBoundary : C6SectorObserverBoundary where
  continuousAngleReadoutOwned := true
  sixOpenSectorsConstructed := true
  exactNegationEquivarianceOwned := true
  normalizedJReflectionIntertwinerOwned := true
  phaseC6ObserverBoundarySafe := true
  boundaryTieBreakChosen := false
  phase9QuantizerNeeded := false
  phase27QuantizerNeeded := false

end

end Integration.MoonshineAngleC6SectorObserver
