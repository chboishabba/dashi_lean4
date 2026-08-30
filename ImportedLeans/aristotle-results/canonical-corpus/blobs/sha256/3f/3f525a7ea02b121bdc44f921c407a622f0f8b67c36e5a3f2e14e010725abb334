import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Lane 1a — dimensional types for scientific quantities

The experiment calculus needs a carrier for *typed* quantities before it can
have laws, uncertainty or protocols.  This file supplies the smallest one that
does real work: a dimension is a vector of integer exponents over six base
dimensions, a quantity is a rational value tagged with a dimension, and the
additive operation is **partial** — it is defined exactly when the two operands
carry the same dimension.

The headline negative is `three_volt_plus_two_coulomb_rejected`: the expression
`3 V + 2 C` has no value in this calculus, and the rejection is a computation,
not a convention.

## Contents

* `§1` `Dim`, its commutative-group laws, and the six base dimensions;
* `§2` the SI-derived dimensions the electrochemical lane needs;
* `§3` `Quantity`, total multiplication, partial addition, and the exact
  definedness criterion (`add_isSome_iff`);
* `§4` the rejection theorems, and the honest limit of dimensional typing:
  dimensional consistency is **necessary and not sufficient** for a law
  (`dimensional_consistency_does_not_determine_the_law`).

Nothing here asserts a physical fact.  `Dim` is a record of six integers and
`Quantity` is a rational tagged with one; the names `volt`, `coulomb`, … are
labels for particular exponent vectors.
-/

namespace Integration.Experiment.Dimension

/-! ## §1 Dimensions -/

/-- A physical dimension as a vector of integer exponents over six base
dimensions: time, electric current, mass, length, amount of substance and
thermodynamic temperature. -/
structure Dim where
  /-- Exponent of time. -/
  time : ℤ
  /-- Exponent of electric current. -/
  current : ℤ
  /-- Exponent of mass. -/
  mass : ℤ
  /-- Exponent of length. -/
  length : ℤ
  /-- Exponent of amount of substance. -/
  amount : ℤ
  /-- Exponent of thermodynamic temperature. -/
  temperature : ℤ
  deriving DecidableEq, Repr

namespace Dim

/-- The dimensionless dimension: all exponents zero. -/
def one : Dim := ⟨0, 0, 0, 0, 0, 0⟩

/-- Product of dimensions: exponents add. -/
def mul (a b : Dim) : Dim :=
  ⟨a.time + b.time, a.current + b.current, a.mass + b.mass,
   a.length + b.length, a.amount + b.amount, a.temperature + b.temperature⟩

/-- Reciprocal of a dimension: exponents negate. -/
def inv (a : Dim) : Dim :=
  ⟨-a.time, -a.current, -a.mass, -a.length, -a.amount, -a.temperature⟩

/-- Quotient of dimensions. -/
def div (a b : Dim) : Dim := mul a (inv b)

theorem mul_comm (a b : Dim) : mul a b = mul b a := by
  cases a; cases b; simp [mul, Int.add_comm]

theorem mul_assoc (a b c : Dim) : mul (mul a b) c = mul a (mul b c) := by
  cases a; cases b; cases c; simp [mul, Int.add_assoc]

theorem one_mul (a : Dim) : mul one a = a := by cases a; simp [mul, one]

theorem mul_one (a : Dim) : mul a one = a := by cases a; simp [mul, one]

theorem mul_inv (a : Dim) : mul a (inv a) = one := by cases a; simp [mul, inv, one]

theorem div_self (a : Dim) : div a a = one := mul_inv a

/-! ### The base dimensions -/

/-- The dimension of a duration. -/
def second : Dim := ⟨1, 0, 0, 0, 0, 0⟩
/-- The dimension of an electric current. -/
def ampere : Dim := ⟨0, 1, 0, 0, 0, 0⟩
/-- The dimension of a mass. -/
def kilogram : Dim := ⟨0, 0, 1, 0, 0, 0⟩
/-- The dimension of a length. -/
def metre : Dim := ⟨0, 0, 0, 1, 0, 0⟩
/-- The dimension of an amount of substance. -/
def mole : Dim := ⟨0, 0, 0, 0, 1, 0⟩
/-- The dimension of a temperature. -/
def kelvin : Dim := ⟨0, 0, 0, 0, 0, 1⟩

/-! ## §2 The derived dimensions the electrochemical lane needs -/

/-- Charge = current × time. -/
def coulomb : Dim := mul ampere second
/-- Energy = mass × length² / time². -/
def joule : Dim := ⟨-2, 0, 1, 2, 0, 0⟩
/-- Electric potential = energy / charge. -/
def volt : Dim := div joule coulomb
/-- Power = energy / time. -/
def watt : Dim := div joule second
/-- Molar mass = mass / amount. -/
def kgPerMole : Dim := div kilogram mole
/-- The Faraday constant's dimension: charge per amount. -/
def coulombPerMole : Dim := div coulomb mole
/-- Electrical resistance = potential / current. -/
def ohm : Dim := div volt ampere

theorem coulomb_eq : coulomb = ⟨1, 1, 0, 0, 0, 0⟩ := rfl
theorem volt_eq : volt = ⟨-3, -1, 1, 2, 0, 0⟩ := rfl

/-- Charge and potential are different dimensions — the fact that makes the
headline rejection below a rejection. -/
theorem volt_ne_coulomb : volt ≠ coulomb := by decide

/-- Energy is potential × charge: the dimensional content of `E = V Q`. -/
theorem joule_eq_volt_mul_coulomb : mul volt coulomb = joule := by decide

end Dim

/-! ## §3 Typed quantities -/

/-- A scientific quantity: a rational magnitude tagged with its dimension. -/
structure Quantity where
  /-- The dimension of the quantity. -/
  dim : Dim
  /-- Its magnitude in the coherent base units. -/
  value : ℚ
  deriving DecidableEq, Repr

namespace Quantity

/-- Multiplication of quantities is total: dimensions multiply, values
multiply. -/
def mul (a b : Quantity) : Quantity := ⟨Dim.mul a.dim b.dim, a.value * b.value⟩

/-- Division of quantities is total on this carrier (division by a zero value
returns the value `0`, as in `ℚ`); dimensions divide. -/
def div (a b : Quantity) : Quantity := ⟨Dim.div a.dim b.dim, a.value / b.value⟩

/-- **Addition is partial.**  It is defined exactly when the operands carry the
same dimension. -/
def add (a b : Quantity) : Option Quantity :=
  if a.dim = b.dim then some ⟨a.dim, a.value + b.value⟩ else none

/-- Subtraction, partial for the same reason. -/
def sub (a b : Quantity) : Option Quantity :=
  if a.dim = b.dim then some ⟨a.dim, a.value - b.value⟩ else none

/-- **The definedness criterion**, exactly. -/
theorem add_isSome_iff (a b : Quantity) : (add a b).isSome = true ↔ a.dim = b.dim := by
  unfold add; split <;> simp_all

/-- When defined, addition keeps the common dimension and adds the values. -/
theorem add_eq_of_dim_eq {a b : Quantity} (h : a.dim = b.dim) :
    add a b = some ⟨a.dim, a.value + b.value⟩ := by simp [add, h]

/-- Multiplication's dimension is the product of the dimensions — the typing
rule for products, which unlike addition never fails. -/
@[simp] theorem mul_dim (a b : Quantity) : (mul a b).dim = Dim.mul a.dim b.dim := rfl

@[simp] theorem div_dim (a b : Quantity) : (div a b).dim = Dim.div a.dim b.dim := rfl

end Quantity

/-! ## §4 Rejection, and the limits of dimensional typing -/

/-- A potential of 3 volts. -/
def threeVolts : Quantity := ⟨Dim.volt, 3⟩
/-- A charge of 2 coulombs. -/
def twoCoulombs : Quantity := ⟨Dim.coulomb, 2⟩

/-- **The headline rejection.**  `3 V + 2 C` has no value: the sum is `none`,
computed from the exponent vectors. -/
theorem three_volt_plus_two_coulomb_rejected :
    Quantity.add threeVolts twoCoulombs = none := by decide

/-- The *product* of the same two quantities is well typed, and it is an
energy: the calculus rejects the nonsense without rejecting the physics. -/
theorem three_volt_times_two_coulomb_is_six_joules :
    Quantity.mul threeVolts twoCoulombs = ⟨Dim.joule, 6⟩ := by
  simp [Quantity.mul, threeVolts, twoCoulombs, Dim.joule_eq_volt_mul_coulomb]
  norm_num

/-- Adding two charges is defined. -/
theorem charges_add : Quantity.add ⟨Dim.coulomb, 2⟩ ⟨Dim.coulomb, 5⟩ =
    some ⟨Dim.coulomb, 7⟩ := by
  simp [Quantity.add]
  norm_num

/-- **The honest limit of dimensional typing.**  Dimensional consistency is a
*necessary* condition on a law and not a sufficient one: two different functions
of current and time are both dimensionally impeccable as laws for charge, and
they disagree.  So the typed graph of the next file must carry provenance and
assumptions, not just dimensions. -/
theorem dimensional_consistency_does_not_determine_the_law :
    ∃ f g : Quantity → Quantity → Quantity,
      (∀ I t, I.dim = Dim.ampere → t.dim = Dim.second → (f I t).dim = Dim.coulomb) ∧
      (∀ I t, I.dim = Dim.ampere → t.dim = Dim.second → (g I t).dim = Dim.coulomb) ∧
      f ≠ g := by
  refine ⟨fun I t => Quantity.mul I t,
          fun I t => ⟨Dim.mul I.dim t.dim, 2 * I.value * t.value⟩, ?_, ?_, ?_⟩
  · intro I t hI ht; simp [Quantity.mul, hI, ht, Dim.coulomb]
  · intro I t hI ht; simp [hI, ht, Dim.coulomb]
  · intro h
    have := congrFun (congrFun h ⟨Dim.ampere, 1⟩) ⟨Dim.second, 1⟩
    simp [Quantity.mul] at this

end Integration.Experiment.Dimension
