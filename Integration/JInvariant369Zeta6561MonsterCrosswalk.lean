import Mathlib
import Integration.JInvariant369ZeroToThirteenTetralemmaQualification

namespace Integration.JInvariant369Zeta6561MonsterCrosswalk

/-!
Finite mirror for the restored zeta / 6561 / 65610 crosswalk.

This deliberately separates:
* cyclotomic C3 arithmetic from Riemann zeta;
* multiple 6561-sized carriers from one another;
* the exact 1 + 6560 pointed shape from any Monster/ATLAS action.
-/

def threePowerEight : Nat := 3^8
def tenTimesThreePowerEight : Nat := 10 * threePowerEight
def regularBulk : Nat := 3 * tenTimesThreePowerEight

theorem threePowerEight_eq_6561 : threePowerEight = 6561 := by norm_num [threePowerEight]
theorem tenTimesThreePowerEight_eq_65610 :
    tenTimesThreePowerEight = 65610 := by norm_num [tenTimesThreePowerEight, threePowerEight]
theorem regularBulk_eq_196830 :
    regularBulk = 196830 := by norm_num [regularBulk, tenTimesThreePowerEight, threePowerEight]

/-! Exact pointed 6561 = 1 + 6560 carrier. -/

inductive Pointed6561
  | distinguished
  | ordinary (index : Fin 6560)
  deriving DecidableEq, Repr

def pointedToFin6561 : Pointed6561 → Fin 6561
  | .distinguished => 0
  | .ordinary i => ⟨i.val + 1, by omega⟩

def fin6561ToPointed : Fin 6561 → Pointed6561
  | ⟨0, _⟩ => .distinguished
  | ⟨n+1, h⟩ => .ordinary ⟨n, by omega⟩

theorem pointed_roundtrip (x : Pointed6561) :
    fin6561ToPointed (pointedToFin6561 x) = x := by
  cases x <;> rfl

theorem fin_roundtrip (x : Fin 6561) :
    pointedToFin6561 (fin6561ToPointed x) = x := by
  rcases x with ⟨n,h⟩
  cases n with
  | zero => rfl
  | succ n => rfl

theorem sixFiveSixOne_eq_one_plus_sixFiveSixZero :
    6561 = 1 + 6560 := by norm_num

/-! Monster-3B C3 multiplicity arithmetic. -/

structure BalancedC3Character where
  residual : Nat
  regular : Nat
  deriving DecidableEq, Repr

def trivialMultiplicity (χ : BalancedC3Character) : Nat := χ.residual + χ.regular
def zetaMultiplicity (χ : BalancedC3Character) : Nat := χ.regular
def zetaSquaredMultiplicity (χ : BalancedC3Character) : Nat := χ.regular
def augmentation (χ : BalancedC3Character) : Nat :=
  trivialMultiplicity χ + zetaMultiplicity χ + zetaSquaredMultiplicity χ

def monster3BCharacter : BalancedC3Character := ⟨53, 65610⟩

theorem monster3B_multiplicity_vector :
    (trivialMultiplicity monster3BCharacter,
      zetaMultiplicity monster3BCharacter,
      zetaSquaredMultiplicity monster3BCharacter)
      = (65663, 65610, 65610) := by
  norm_num [monster3BCharacter, trivialMultiplicity, zetaMultiplicity,
    zetaSquaredMultiplicity]

theorem monster3B_dimension :
    augmentation monster3BCharacter = 196883 := by
  norm_num [augmentation, trivialMultiplicity, zetaMultiplicity,
    zetaSquaredMultiplicity, monster3BCharacter]

theorem regularMultiplicity_factor :
    65610 = 10 * 6561 := by norm_num

theorem regularMultiplicity_heisenberg_factor :
    65610 = 90 * 729 := by norm_num

theorem bulk_factor :
    196830 = 3 * 65610 := by norm_num

theorem monster_remainder :
    196883 = 3 * 65610 + 53 := by norm_num

theorem moonshine_completion :
    196884 = 196883 + 1 := by norm_num

theorem nineExponent_one_two_six :
    1 + 2 + 6 = 9 := by norm_num

theorem threePowerNine_one_two_six :
    3^9 = 3^1 * 3^2 * 3^6 := by norm_num

/-!
Symbolic cyclotomic C3 cancellation.  This is intentionally a finite formal
phase algebra, not the Riemann zeta function.
-/

inductive C3Phase
  | one | zeta | zeta2
  deriving DecidableEq, Repr

def inversePhase : C3Phase → C3Phase
  | .one => .one
  | .zeta => .zeta2
  | .zeta2 => .zeta

theorem inverse_zeta_is_zeta2 :
    inversePhase .zeta = .zeta2 := rfl

structure ZetaLaneBoundary where
  threePowerEight6561 : Bool
  pointedOnePlus6560 : Bool
  regularMultiplicity65610 : Bool
  monsterResidual53 : Bool
  oneTwoSixExponentSplit : Bool
  cyclotomicInverseOwned : Bool
  cyclotomicZetaEqualsRiemannZeta : Bool
  equal6561IdentifiesCarriers : Bool
  pointed6561IdentifiesAtlasAction : Bool
  riemannZetaSigmaDirichletWeldPaidHere : Bool
  deriving Repr

def canonicalBoundary : ZetaLaneBoundary where
  threePowerEight6561 := true
  pointedOnePlus6560 := true
  regularMultiplicity65610 := true
  monsterResidual53 := true
  oneTwoSixExponentSplit := true
  cyclotomicInverseOwned := true
  cyclotomicZetaEqualsRiemannZeta := false
  equal6561IdentifiesCarriers := false
  pointed6561IdentifiesAtlasAction := false
  riemannZetaSigmaDirichletWeldPaidHere := false

end Integration.JInvariant369Zeta6561MonsterCrosswalk
