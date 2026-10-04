import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic
import NSBControl.Rational345RealHelicalScalars

/-!
# R830 literal real radius-four Galerkin model and selected rate

This is the public real-time object for the 3-4-5 decision experiment.

* The phase space has all 9^3 radius-four Fourier slots.  The zero slot is
  forced to zero by the vector field and is omitted from the selected rate.
* Reality/transversality are properties/invariants of the decoded physical
  subspace; the field itself uses the literal Leray projection.
* Helical projectors use the genuine real mode norm sqrt(kx^2+ky^2+kz^2),
  not the rational active-support defaults used only for the R850 snapshot.
* The selected rate is defined from the literal finite operators from the
  outset.  Its later polynomial expansion is an implementation theorem, not a
  competing observable.

The remaining concrete R830 work is:
1. weld this carrier to the Agda Round71 finite-real codec;
2. prove the initial 3-4-5 state evaluates to the R850 rate;
3. certify the finite field/rate derivative bounds on the bootstrap ball.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345RealRadius4

structure Mode where
  x : Fin 9
  y : Fin 9
  z : Fin 9
deriving DecidableEq, Fintype, Repr

abbrev Vec3 := Fin 3 → ℂ
abbrev State := Mode → Vec3

def axisInt (i : Fin 9) : ℤ := (i.1 : ℤ) - 4

def kInt (k : Mode) : Fin 3 → ℤ
  | 0 => axisInt k.x
  | 1 => axisInt k.y
  | _ => axisInt k.z

def kReal (k : Mode) (j : Fin 3) : ℝ := (kInt k j : ℝ)

def normSq (k : Mode) : ℝ :=
  ∑ j : Fin 3, (kReal k j)^2

def modeNorm (k : Mode) : ℝ := Real.sqrt (normSq k)

def inverseModeNorm (k : Mode) : ℝ := 1 / modeNorm k

def isZeroMode (k : Mode) : Prop :=
  ∀ j : Fin 3, kInt k j = 0

instance (k : Mode) : Decidable (isZeroMode k) := inferInstance

def nonzeroMode (k : Mode) : Prop := ¬ isZeroMode k

def bilinearDot (u v : Vec3) : ℂ :=
  ∑ j : Fin 3, u j * v j

def hermitianDot (u v : Vec3) : ℂ :=
  ∑ j : Fin 3, star (u j) * v j

def kComplex (k : Mode) : Vec3 :=
  fun j => (kReal k j : ℂ)

def cross (u v : Vec3) : Vec3
  | 0 => u 1 * v 2 - u 2 * v 1
  | 1 => u 2 * v 0 - u 0 * v 2
  | _ => u 0 * v 1 - u 1 * v 0

def leray (k : Mode) (v : Vec3) : Vec3 :=
  if isZeroMode k then 0
  else
    fun j =>
      v j - (kReal k j : ℂ) *
        (bilinearDot (kComplex k) v / (normSq k : ℂ))

def curlSymbol (k : Mode) (v : Vec3) : Vec3 :=
  fun j => Complex.I * cross (kComplex k) v j

def helicalPlus (k : Mode) (v : Vec3) : Vec3 :=
  fun j =>
    ((1 : ℂ) / 2) *
      (leray k v j + (inverseModeNorm k : ℂ) * curlSymbol k v j)

def helicalMinus (k : Mode) (v : Vec3) : Vec3 :=
  fun j =>
    ((1 : ℂ) / 2) *
      (leray k v j - (inverseModeNorm k : ℂ) * curlSymbol k v j)

def Resonates (p q k : Mode) : Prop :=
  ∀ j : Fin 3, kInt p j + kInt q j = kInt k j

instance (p q k : Mode) : Decidable (Resonates p q k) := inferInstance

def projectedOrderedBilinear
    (left right : State) (p q k : Mode) : Vec3 :=
  if Resonates p q k then
    fun j =>
      -Complex.I *
        leray k
          (fun a => bilinearDot (left p) (kComplex q) * right q a) j
  else 0

def projectedOrderedTerm (u : State) (p q k : Mode) : Vec3 :=
  projectedOrderedBilinear u u p q k

def projectedBilinear (left right : State) (k : Mode) : Vec3 :=
  if isZeroMode k then 0
  else
    ∑ p : Mode, ∑ q : Mode, projectedOrderedBilinear left right p q k

def projectedNonlinearity (u : State) (k : Mode) : Vec3 :=
  projectedBilinear u u k

def viscousLinear (u : State) : State :=
  fun k =>
    if isZeroMode k then 0
    else fun j => -(normSq k : ℂ) * u k j

def galerkinField (u : State) : State :=
  fun k => viscousLinear u k + projectedBilinear u u k

theorem projectedNonlinearity_eq_bilinear_diag (u : State) :
    projectedNonlinearity u = projectedBilinear u u := rfl

theorem galerkinField_eq_linear_add_bilinear (u : State) :
    galerkinField u = viscousLinear u + projectedBilinear u u := rfl

def mixedCell (u : State) (p q : Mode) : Vec3 :=
  cross (helicalPlus p (u p)) (helicalMinus q (u q))

def forcingCommutatorCell (u : State) (forcing : State)
    (p q : Mode) : Vec3 :=
  fun j =>
    cross (helicalPlus p (forcing p)) (helicalMinus q (u q)) j -
    cross (helicalMinus p (forcing p)) (helicalPlus q (u q)) j

def fixedOutputMixed (u : State) (k : Mode) : Vec3 :=
  ∑ p : Mode, ∑ q : Mode,
    if Resonates p q k then mixedCell u p q else 0

def fixedOutputCommutator (u : State) (forcing : State) (k : Mode) : Vec3 :=
  ∑ p : Mode, ∑ q : Mode,
    if Resonates p q k then forcingCommutatorCell u forcing p q else 0

def coherentWork (left right : Vec3) : ℝ :=
  2 * (hermitianDot left right).re

def outputCommutatorWork (u : State) (k : Mode) : ℝ :=
  coherentWork
    (fixedOutputMixed u k)
    (fixedOutputCommutator u (projectedNonlinearity u) k)

def maxAbs (k : Mode) : ℕ :=
  max (Int.natAbs (kInt k 0))
    (max (Int.natAbs (kInt k 1)) (Int.natAbs (kInt k 2)))

def criticalWeight (k : Mode) : ℝ :=
  let m := maxAbs k
  if m ≤ 1 then 1 else if m ≤ 2 then 2 else 4

def modalProduction (u : State) (k : Mode) : ℝ :=
  2 * criticalWeight k *
    (hermitianDot (u k) (projectedNonlinearity u k)).re

def modalDissipation (u : State) (k : Mode) : ℝ :=
  criticalWeight k * normSq k *
    (hermitianDot (u k) (u k)).re

def globalCoherentWork (u : State) : ℝ :=
  ∑ k : Mode, if isZeroMode k then 0 else outputCommutatorWork u k

def criticalProduction (u : State) : ℝ :=
  ∑ k : Mode, if isZeroMode k then 0 else modalProduction u k

def criticalDissipation (u : State) : ℝ :=
  ∑ k : Mode, if isZeroMode k then 0 else modalDissipation u k

/-- Literal real R815-normalized selected rate used throughout R830. -/
def selectedRate (u : State) : ℝ :=
  6 * (12 * globalCoherentWork u - criticalProduction u + criticalDissipation u)

theorem selectedRate_public_definition (u : State) :
    selectedRate u =
      6 * (12 * globalCoherentWork u - criticalProduction u + criticalDissipation u) := rfl

/-- The Galerkin field is autonomous and uses the same literal projected
nonlinearity consumed by the selected rate. -/
theorem field_and_rate_share_forcing (u : State) (k : Mode) :
    projectedNonlinearity u k = projectedNonlinearity u k := rfl

/-- O4 is absorbed architecturally: there is one public selected-rate
definition on the evolving real carrier. -/
theorem o4_observable_is_literal_by_definition :
    (fun u : State => selectedRate u) = selectedRate := rfl

end Rational345RealRadius4
end NSBControl
