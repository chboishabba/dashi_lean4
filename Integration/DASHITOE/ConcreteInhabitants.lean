import Mathlib

namespace DASHITOE

/-!
Concrete inhabitants for the TOE integration layer.

The distinction is deliberate:
* native theorem inhabitants below are proved directly in this branch;
* imported formal inhabitants point to actual theorem values on sibling DASHI
  branches, but are not re-labelled as proof terms here;
* none of these by itself is a calibrated same-physical-object inhabitant.
-/

------------------------------------------------------------------------
-- Native interacting atomic inhabitant.
------------------------------------------------------------------------

inductive AtomicP2Basis where
  | negZero
  | negPos
  | zeroPos
  deriving DecidableEq, Repr

open AtomicP2Basis

def atomicP2C3 : AtomicP2Basis → AtomicP2Basis
  | negZero => zeroPos
  | negPos => negZero
  | zeroPos => negPos

@[simp] theorem atomicP2C3_order_three (x : AtomicP2Basis) :
    atomicP2C3 (atomicP2C3 (atomicP2C3 x)) = x := by
  cases x <;> rfl

def atomicP2CoulombEnergy : ℚ := 21 / 128

def atomicP2SlaterF0 : ℚ := 93 / 512

def atomicP2SlaterF2 : ℚ := 45 / 512

def atomicP2CoulombMatrix : AtomicP2Basis → AtomicP2Basis → ℚ
  | negZero, negZero => atomicP2CoulombEnergy
  | negPos, negPos => atomicP2CoulombEnergy
  | zeroPos, zeroPos => atomicP2CoulombEnergy
  | _, _ => 0

@[simp] theorem atomicP2Coulomb_c3_invariant (a b : AtomicP2Basis) :
    atomicP2CoulombMatrix (atomicP2C3 a) (atomicP2C3 b) =
      atomicP2CoulombMatrix a b := by
  cases a <;> cases b <;> rfl

structure AtomicP2HamiltonianInhabitant where
  basis : Type := AtomicP2Basis
  c3 : basis → basis
  orderThree : ∀ x, c3 (c3 (c3 x)) = x
  matrixElement : basis → basis → ℚ
  c3HamiltonianInvariant : ∀ a b, matrixElement (c3 a) (c3 b) = matrixElement a b
  sourceOwner : String

noncomputable def canonicalAtomicP2HamiltonianInhabitant : AtomicP2HamiltonianInhabitant where
  basis := AtomicP2Basis
  c3 := atomicP2C3
  orderThree := atomicP2C3_order_three
  matrixElement := atomicP2CoulombMatrix
  c3HamiltonianInvariant := atomicP2Coulomb_c3_invariant
  sourceOwner := "Agda PR #1194: selected common-spin hydrogenic 2p^2 Coulomb carrier, Vee=(21/128) I3"

------------------------------------------------------------------------
-- Native Eisenstein C3 inhabitant.
------------------------------------------------------------------------

abbrev EisensteinField := QuadraticAlgebra ℚ (-1) (-1)

def eisensteinOmega : EisensteinField := QuadraticAlgebra.omega

@[simp] theorem eisensteinOmega_square :
    eisensteinOmega ^ 2 = -(1 : EisensteinField) - eisensteinOmega := by
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
  ext <;> norm_num [eisensteinOmega]

@[simp] theorem eisensteinOmega_cube :
    eisensteinOmega ^ 3 = (1 : EisensteinField) := by
  calc
    eisensteinOmega ^ 3 = eisensteinOmega * eisensteinOmega ^ 2 := by ring
    _ = eisensteinOmega * (-1 - eisensteinOmega) := by rw [eisensteinOmega_square]
    _ = 1 := by
      rw [mul_sub, mul_neg, mul_one, ← pow_two, eisensteinOmega_square]
      ring

structure EisensteinC3Inhabitant where
  carrier : Type := EisensteinField
  omega : carrier
  orderThree : omega ^ 3 = 1

noncomputable def canonicalEisensteinC3Inhabitant : EisensteinC3Inhabitant where
  carrier := EisensteinField
  omega := eisensteinOmega
  orderThree := eisensteinOmega_cube

------------------------------------------------------------------------
-- Exact cross-branch formal inhabitants.
------------------------------------------------------------------------

inductive InhabitantAuthority where
  | nativeLeanInhabitant
  | importedFormalInhabitant
  | calibratedPhysicalInhabitant
  deriving Repr, DecidableEq

structure FormalInhabitantReceipt where
  prover : String
  repository : String
  pullRequest : Nat
  headCommit : String
  moduleName : String
  declaration : String
  propositionScope : String
  authority : InhabitantAuthority
  importedAsLocalTheorem : Bool := false
  deriving Repr

def lean68RTInhabitant : FormalInhabitantReceipt :=
  { prover := "Lean4"
    repository := "chboishabba/dashi_lean4"
    pullRequest := 68
    headCommit := "1b3772daa785d29f119e1a8ce92764819e12b941"
    moduleName := "Synthesis.TerminalConcreteInstantiation"
    declaration := "canonicalTerminalRT"
    propositionScope := "For every k, the actual corrected independent-Bell tree has actualEntropy = actualCutEntropy."
    authority := .importedFormalInhabitant }

def lean68JacobsonInhabitant : FormalInhabitantReceipt :=
  { prover := "Lean4"
    repository := "chboishabba/dashi_lean4"
    pullRequest := 68
    headCommit := "1b3772daa785d29f119e1a8ce92764819e12b941"
    moduleName := "Synthesis.TerminalConcreteInstantiation"
    declaration := "canonicalTerminalVacuumEinstein"
    propositionScope := "Concrete flat-vacuum Jacobson benchmark with recovered Lambda=0 and exact terminal Einstein equality."
    authority := .importedFormalInhabitant }

def lean73CMInhabitant : FormalInhabitantReceipt :=
  { prover := "Lean4"
    repository := "chboishabba/dashi_lean4"
    pullRequest := 73
    headCommit := "4dde2b77cbdb76bdb21db852966db2ffa0ca88d3"
    moduleName := "Dashi.EisensteinJZeroPointCMExact"
    declaration := "omegaPointEndomorphism"
    propositionScope := "Actual order-three additive endomorphism of the nonsingular j=0 elliptic point group over Q(omega)."
    authority := .importedFormalInhabitant }

structure ConcreteInhabitantBundle where
  atomicHamiltonian : AtomicP2HamiltonianInhabitant
  eisensteinC3 : EisensteinC3Inhabitant
  rtFormal : FormalInhabitantReceipt
  jacobsonFormal : FormalInhabitantReceipt
  cmPointFormal : FormalInhabitantReceipt

noncomputable def canonicalConcreteInhabitantBundle : ConcreteInhabitantBundle where
  atomicHamiltonian := canonicalAtomicP2HamiltonianInhabitant
  eisensteinC3 := canonicalEisensteinC3Inhabitant
  rtFormal := lean68RTInhabitant
  jacobsonFormal := lean68JacobsonInhabitant
  cmPointFormal := lean73CMInhabitant

end DASHITOE
