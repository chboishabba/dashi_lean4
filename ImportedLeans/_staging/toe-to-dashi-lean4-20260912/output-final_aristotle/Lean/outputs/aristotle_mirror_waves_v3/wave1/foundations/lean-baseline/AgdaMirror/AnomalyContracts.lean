import Mathlib

/-!
# Lean mirror of `DASHI/Algebra/AnomalyContracts.agda` (genuine, strengthened)

The Agda `AnomalyContracts.agda` records the four Standard-Model anomaly-balance
contracts but sets the computed anomaly numerators to **placeholder zeros**
(`anomalyU1Cubed = 0`, etc.), so its `cancel-*` lemmas are the trivial `0 = 0`.

Here we keep the same four contracts but **compute the genuine anomaly sums**
from the one-generation Standard-Model matter content with its signed
hypercharges (in units of `1/6`) and color/isospin multiplicities, and prove
that each of the four anomaly coefficients genuinely vanishes:

* gravitational (linear) `U(1)_Y`;
* `SU(2)²·U(1)_Y`;
* `SU(3)²·U(1)_Y`;
* cubic `U(1)_Y³`.

These are real arithmetic identities over `ℤ`, not placeholders.
-/

namespace AgdaMirror.AnomalyContracts

/-- One generation of left-handed Weyl multiplets (including a right-handed
neutrino as `nuC`). -/
inductive Particle
  | QL | uC | dC | LL | eC | nuC
deriving DecidableEq

open Particle

/-- Signed hypercharge in units of `1/6` (the "signed sixths"), all written as
left-handed Weyl fermions. -/
def Y6 : Particle → ℤ
  | QL => 1
  | uC => -4
  | dC => 2
  | LL => -3
  | eC => 6
  | nuC => 0

/-- `SU(3)` color multiplicity. -/
def colorMult : Particle → ℤ
  | QL => 3
  | uC => 3
  | dC => 3
  | LL => 1
  | eC => 1
  | nuC => 1

/-- `SU(2)` isospin multiplicity. -/
def isospinMult : Particle → ℤ
  | QL => 2
  | uC => 1
  | dC => 1
  | LL => 2
  | eC => 1
  | nuC => 1

/-- Total Weyl multiplicity (color × isospin). -/
def weylMult (p : Particle) : ℤ := colorMult p * isospinMult p

/-- Is this an `SU(2)` doublet? -/
def isSU2Doublet : Particle → Bool
  | QL => true
  | LL => true
  | _ => false

/-- Is this an `SU(3)` triplet? -/
def isSU3Triplet : Particle → Bool
  | QL => true
  | uC => true
  | dC => true
  | _ => false

/-- All multiplets of one generation. -/
def allParticles : List Particle := [QL, uC, dC, LL, eC, nuC]

/-- Gravitational (linear) `U(1)_Y` anomaly coefficient. -/
def anomalyGravitational : ℤ :=
  (allParticles.map (fun p => weylMult p * Y6 p)).sum

/-- `SU(2)²·U(1)_Y` anomaly coefficient (color multiplicity over `SU(2)` doublets). -/
def anomalySU2SU2U1 : ℤ :=
  ((allParticles.filter (fun p => isSU2Doublet p)).map (fun p => colorMult p * Y6 p)).sum

/-- `SU(3)²·U(1)_Y` anomaly coefficient (isospin multiplicity over `SU(3)` triplets). -/
def anomalySU3SU3U1 : ℤ :=
  ((allParticles.filter (fun p => isSU3Triplet p)).map (fun p => isospinMult p * Y6 p)).sum

/-- Cubic `U(1)_Y³` anomaly coefficient. -/
def anomalyU1Cubed : ℤ :=
  (allParticles.map (fun p => weylMult p * (Y6 p) ^ 3)).sum

/-- The gravitational anomaly genuinely cancels. -/
theorem cancel_gravitational : anomalyGravitational = 0 := by decide

/-- The `SU(2)²·U(1)_Y` anomaly genuinely cancels. -/
theorem cancel_SU2SU2U1 : anomalySU2SU2U1 = 0 := by decide

/-- The `SU(3)²·U(1)_Y` anomaly genuinely cancels. -/
theorem cancel_SU3SU3U1 : anomalySU3SU3U1 = 0 := by decide

/-- The cubic `U(1)_Y³` anomaly genuinely cancels. -/
theorem cancel_U1Cubed : anomalyU1Cubed = 0 := by decide

end AgdaMirror.AnomalyContracts
