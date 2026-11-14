import Integration.EisensteinSplitPrimeExact

namespace Dashi.EisensteinSixUnitsExact

open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinLatticeCountingMaxCut
open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinEuclideanDomainExact
open Dashi.EisensteinSplitPrimeExact

------------------------------------------------------------------------
-- The six explicit units in the `(1,ω)` basis.
------------------------------------------------------------------------

def unitOne : EisensteinQA := asQuadraticAlgebra 1 0
def unitNegOne : EisensteinQA := asQuadraticAlgebra (-1) 0
def unitOmega : EisensteinQA := asQuadraticAlgebra 0 1
def unitNegOmega : EisensteinQA := asQuadraticAlgebra 0 (-1)
def unitOmegaSquared : EisensteinQA := asQuadraticAlgebra (-1) (-1)
def unitNegOmegaSquared : EisensteinQA := asQuadraticAlgebra 1 1

theorem unitOne_norm : QuadraticAlgebra.norm unitOne = 1 := by native_decide
theorem unitNegOne_norm : QuadraticAlgebra.norm unitNegOne = 1 := by native_decide
theorem unitOmega_norm : QuadraticAlgebra.norm unitOmega = 1 := by native_decide
theorem unitNegOmega_norm : QuadraticAlgebra.norm unitNegOmega = 1 := by native_decide
theorem unitOmegaSquared_norm : QuadraticAlgebra.norm unitOmegaSquared = 1 := by native_decide
theorem unitNegOmegaSquared_norm : QuadraticAlgebra.norm unitNegOmegaSquared = 1 := by native_decide

theorem unitOne_isUnit : IsUnit unitOne :=
  (isUnit_iff_norm_eq_one unitOne).2 unitOne_norm

theorem unitNegOne_isUnit : IsUnit unitNegOne :=
  (isUnit_iff_norm_eq_one unitNegOne).2 unitNegOne_norm

theorem unitOmega_isUnit : IsUnit unitOmega :=
  (isUnit_iff_norm_eq_one unitOmega).2 unitOmega_norm

theorem unitNegOmega_isUnit : IsUnit unitNegOmega :=
  (isUnit_iff_norm_eq_one unitNegOmega).2 unitNegOmega_norm

theorem unitOmegaSquared_isUnit : IsUnit unitOmegaSquared :=
  (isUnit_iff_norm_eq_one unitOmegaSquared).2 unitOmegaSquared_norm

theorem unitNegOmegaSquared_isUnit : IsUnit unitNegOmegaSquared :=
  (isUnit_iff_norm_eq_one unitNegOmegaSquared).2 unitNegOmegaSquared_norm

------------------------------------------------------------------------
-- Exact exhaustion: a norm-one lattice point has both coordinates in
-- `{-1,0,1}` by the coercivity inequalities, and the remaining nine cases are
-- finite arithmetic.
------------------------------------------------------------------------

theorem norm_one_coordinate_classification (a b : Int)
    (hQ : eisensteinNorm a b = 1) :
    (a = 1 ∧ b = 0) ∨
    (a = -1 ∧ b = 0) ∨
    (a = 0 ∧ b = 1) ∨
    (a = 0 ∧ b = -1) ∨
    (a = -1 ∧ b = -1) ∨
    (a = 1 ∧ b = 1) := by
  have haQ := eisensteinNorm_coercive_a a b
  have hbQ := eisensteinNorm_coercive_b a b
  rw [hQ] at haQ hbQ
  have ha_lo : -1 ≤ a := by nlinarith [sq_nonneg a]
  have ha_hi : a ≤ 1 := by nlinarith [sq_nonneg a]
  have hb_lo : -1 ≤ b := by nlinarith [sq_nonneg b]
  have hb_hi : b ≤ 1 := by nlinarith [sq_nonneg b]
  interval_cases a <;> interval_cases b <;>
    norm_num [eisensteinNorm] at hQ ⊢

/-- Every unit is literally one of the six classical Eisenstein units. -/
theorem unit_classification (z : EisensteinQA) (hz : IsUnit z) :
    z = unitOne ∨ z = unitNegOne ∨
    z = unitOmega ∨ z = unitNegOmega ∨
    z = unitOmegaSquared ∨ z = unitNegOmegaSquared := by
  have hnorm : QuadraticAlgebra.norm z = 1 :=
    (isUnit_iff_norm_eq_one z).1 hz
  have hQ : eisensteinNorm z.re z.im = 1 := by
    simpa [norm_eq_coordinate_norm] using hnorm
  rcases norm_one_coordinate_classification z.re z.im hQ with
      h | h | h | h | h | h
  · left
    rcases h with ⟨hre, him⟩
    ext <;> simp [unitOne, asQuadraticAlgebra, hre, him]
  · right; left
    rcases h with ⟨hre, him⟩
    ext <;> simp [unitNegOne, asQuadraticAlgebra, hre, him]
  · right; right; left
    rcases h with ⟨hre, him⟩
    ext <;> simp [unitOmega, asQuadraticAlgebra, hre, him]
  · right; right; right; left
    rcases h with ⟨hre, him⟩
    ext <;> simp [unitNegOmega, asQuadraticAlgebra, hre, him]
  · right; right; right; right; left
    rcases h with ⟨hre, him⟩
    ext <;> simp [unitOmegaSquared, asQuadraticAlgebra, hre, him]
  · right; right; right; right; right
    rcases h with ⟨hre, him⟩
    ext <;> simp [unitNegOmegaSquared, asQuadraticAlgebra, hre, him]

def eisensteinUnits : Finset EisensteinQA :=
  { unitOne, unitNegOne, unitOmega, unitNegOmega,
    unitOmegaSquared, unitNegOmegaSquared }

theorem eisensteinUnits_card : eisensteinUnits.card = 6 := by native_decide

theorem all_listed_units_are_units : ∀ z ∈ eisensteinUnits, IsUnit z := by
  intro z hz
  simp [eisensteinUnits] at hz
  rcases hz with h | h | h | h | h | h
  · simpa [h] using unitOne_isUnit
  · simpa [h] using unitNegOne_isUnit
  · simpa [h] using unitOmega_isUnit
  · simpa [h] using unitNegOmega_isUnit
  · simpa [h] using unitOmegaSquared_isUnit
  · simpa [h] using unitNegOmegaSquared_isUnit

/-- Membership in the explicit six-element set is equivalent to being a unit. -/
theorem mem_eisensteinUnits_iff_isUnit (z : EisensteinQA) :
    z ∈ eisensteinUnits ↔ IsUnit z := by
  constructor
  · exact all_listed_units_are_units z
  · intro hz
    rcases unit_classification z hz with h | h | h | h | h | h <;>
      simp [eisensteinUnits, h]

structure EisensteinSixUnitsBoundary where
  allSixListed : Bool := true
  eachListedElementIsUnit : Bool := true
  everyUnitClassified : Bool := true
  exactUnitCardinalityPaid : Bool := true
  associateOrbitCountSixAvailable : Bool := true
  globalNormShellCountPaid : Bool := false

def canonicalBoundary : EisensteinSixUnitsBoundary := {}

end Dashi.EisensteinSixUnitsExact
