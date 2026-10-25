import Integration.EisensteinJZeroHeckeConductorExact
import Integration.EisensteinSixUnitsExact
import Mathlib.Data.Int.GCD

/-!
# The six invertible residue classes modulo 2*sqrt(-3)

For the literal conductor generator

    f = 2+4*omega,

a coordinate calculation gives

    f * (a+b*omega)
      = (2a-4b) + (4a-2b)omega.

Hence `f | (x+y*omega)` iff `x` and `y` are even and `x+y` is divisible by
three.  This makes the residue quotient completely explicit: an element is
prime to the two rational bad factors exactly when its mod-2 coordinate pair
is nonzero and its `(re+im) mod 3` value is nonzero.  Those `3*2=6`
invertible signatures are represented exactly once by the six classical
Eisenstein units.

This is the finite CRT-style payment behind the externally sourced statement
that a conductor-coprime generator admits a unique sixth-root-of-unity
normalization modulo `2*sqrt(-3)`.

Attribution: the CM interpretation of this modulus remains externally sourced.
The coordinate/divisibility and six-unit classification below are repo-owned;
generic integer divisibility and quadratic-algebra infrastructure are Mathlib.
-/

namespace Integration.EisensteinJZeroHeckeResidueUnitsExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinSixUnitsExact
open Dashi.EisensteinSixUnitOrbitExact
open Integration.EisensteinJZeroHeckeConductorExact

------------------------------------------------------------------------
-- Literal divisibility criterion for the conductor generator.
------------------------------------------------------------------------

/-- Coordinate CRT criterion for divisibility by `2+4*omega`. -/
theorem heckeConductor_dvd_iff_coordinates (z : EisensteinQA) :
    heckeConductorElement ∣ z ↔
      (2 : Int) ∣ z.re ∧ (2 : Int) ∣ z.im ∧ (3 : Int) ∣ (z.re + z.im) := by
  constructor
  · rintro ⟨q, hq⟩
    have hre := congrArg QuadraticAlgebra.re hq
    have him := congrArg QuadraticAlgebra.im hq
    rw [heckeConductorElement_coordinates] at hre him
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      asQuadraticAlgebra] at hre him
    constructor
    · refine ⟨q.re - 2 * q.im, ?_⟩
      linarith
    constructor
    · refine ⟨2 * q.re - q.im, ?_⟩
      linarith
    · refine ⟨2 * q.re - 2 * q.im, ?_⟩
      linarith
  · rintro ⟨hx2, hy2, hsum3⟩
    rcases hx2 with ⟨X, hX⟩
    rcases hy2 with ⟨Y, hY⟩
    rcases hsum3 with ⟨K, hK⟩
    have h2sum : (2 : Int) ∣ z.re + z.im := by
      exact dvd_add ⟨X, hX⟩ ⟨Y, hY⟩
    have h2threeK : (2 : Int) ∣ 3 * K := by
      rw [← hK]
      exact h2sum
    have h2K : (2 : Int) ∣ K := by
      rcases (Int.prime_two.dvd_mul.mp h2threeK) with h23 | h2K
      · norm_num at h23
      · exact h2K
    rcases h2K with ⟨k, hk⟩
    have hXY : X + Y = 3 * k := by
      omega
    refine ⟨asQuadraticAlgebra (2 * k - X) (k - X), ?_⟩
    ext <;>
      simp only [heckeConductorElement_coordinates,
        QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        asQuadraticAlgebra] <;>
      omega

------------------------------------------------------------------------
-- The six residue representatives.
------------------------------------------------------------------------

private def codeOne : EisensteinUnitCode :=
  ⟨unitOne, by simp [eisensteinUnits]⟩
private def codeNegOne : EisensteinUnitCode :=
  ⟨unitNegOne, by simp [eisensteinUnits]⟩
private def codeOmega : EisensteinUnitCode :=
  ⟨unitOmega, by simp [eisensteinUnits]⟩
private def codeNegOmega : EisensteinUnitCode :=
  ⟨unitNegOmega, by simp [eisensteinUnits]⟩
private def codeOmegaSquared : EisensteinUnitCode :=
  ⟨unitOmegaSquared, by simp [eisensteinUnits]⟩
private def codeNegOmegaSquared : EisensteinUnitCode :=
  ⟨unitNegOmegaSquared, by simp [eisensteinUnits]⟩

/-- Coordinate criterion for belonging to one of the six invertible conductor
residue classes.  The first conjunct excludes the zero class modulo the inert
prime `2`; the second excludes the zero class modulo the ramified factor above
`3`. -/
def HeckeResidueAdmissible (z : EisensteinQA) : Prop :=
  ¬ (z.re % 2 = 0 ∧ z.im % 2 = 0) ∧
    (z.re + z.im) % 3 ≠ 0

/-- Explicit six-way residue selector.  Impossible branches outside
`HeckeResidueAdmissible` use `1` as a harmless default. -/
def residueUnitCode (z : EisensteinQA) : EisensteinUnitCode :=
  if z.re % 2 = 1 then
    if z.im % 2 = 0 then
      if (z.re + z.im) % 3 = 1 then codeOne else codeNegOne
    else
      if (z.re + z.im) % 3 = 1 then codeOmegaSquared else codeNegOmegaSquared
  else if z.im % 2 = 1 then
    if (z.re + z.im) % 3 = 1 then codeOmega else codeNegOmega
  else codeOne

private theorem residueUnitCode_spec_raw
    (z : EisensteinQA) (h : HeckeResidueAdmissible z) :
    CongruentModHeckeConductor z (residueUnitCode z).1 := by
  unfold HeckeResidueAdmissible at h
  unfold CongruentModHeckeConductor
  rw [heckeConductor_dvd_iff_coordinates]
  have hre0or1 : z.re % 2 = 0 ∨ z.re % 2 = 1 := by omega
  have him0or1 : z.im % 2 = 0 ∨ z.im % 2 = 1 := by omega
  have hsum012 :
      (z.re + z.im) % 3 = 0 ∨
      (z.re + z.im) % 3 = 1 ∨
      (z.re + z.im) % 3 = 2 := by omega
  rcases hre0or1 with hre | hre <;>
    rcases him0or1 with him | him <;>
      rcases hsum012 with hsum | hsum | hsum
  all_goals
    try { exfalso; exact h.1 ⟨hre, him⟩ }
  all_goals
    try { exfalso; exact h.2 hsum }
  all_goals
    simp [residueUnitCode, hre, him, hsum,
      codeOne, codeNegOne, codeOmega, codeNegOmega,
      codeOmegaSquared, codeNegOmegaSquared,
      unitOne, unitNegOne, unitOmega, unitNegOmega,
      unitOmegaSquared, unitNegOmegaSquared,
      asQuadraticAlgebra, Int.dvd_iff_emod_eq_zero]

/-- Two listed units cannot occupy the same conductor residue class. -/
theorem listedUnits_congruent_iff_eq
    (u v : EisensteinUnitCode) :
    CongruentModHeckeConductor u.1 v.1 ↔ u = v := by
  constructor
  · intro huv
    apply Subtype.ext
    have huUnit : IsUnit u.1 :=
      (mem_eisensteinUnits_iff_isUnit u.1).1 u.2
    have hvUnit : IsUnit v.1 :=
      (mem_eisensteinUnits_iff_isUnit v.1).1 v.2
    rcases unit_classification u.1 huUnit with hu | hu | hu | hu | hu | hu <;>
      rcases unit_classification v.1 hvUnit with hv | hv | hv | hv | hv | hv <;>
      simp only [hu, hv] at huv ⊢ <;>
      native_decide at huv ⊢
  · rintro rfl
    unfold CongruentModHeckeConductor
    simp

/-- Any admissible element is congruent to exactly one of the six listed
units. -/
theorem heckeUnitNormalizable_of_residueAdmissible
    (z : EisensteinQA) (h : HeckeResidueAdmissible z) :
    HeckeUnitNormalizable z := by
  refine ⟨residueUnitCode z, residueUnitCode_spec_raw z h, ?_⟩
  intro u hu
  apply (listedUnits_congruent_iff_eq u (residueUnitCode z)).1
  unfold CongruentModHeckeConductor at hu ⊢
  rcases hu with ⟨a, ha⟩
  rcases residueUnitCode_spec_raw z h with ⟨b, hb⟩
  refine ⟨b - a, ?_⟩
  rw [ha, hb]
  ring

/-- Explicit normalizing unit for an admissible conductor residue. -/
def residueNormalizingUnit
    (z : EisensteinQA) (h : HeckeResidueAdmissible z) : EisensteinUnitCode :=
  residueUnitCode z

/-- The explicit selected unit satisfies the literal conductor congruence. -/
theorem residueNormalizingUnit_spec
    (z : EisensteinQA) (h : HeckeResidueAdmissible z) :
    CongruentModHeckeConductor z (residueNormalizingUnit z h).1 :=
  residueUnitCode_spec_raw z h

/-- The explicit selector agrees with the abstract unique-unit choice from the
conductor owner. -/
theorem residueNormalizingUnit_eq_abstract
    (z : EisensteinQA) (h : HeckeResidueAdmissible z) :
    residueNormalizingUnit z h =
      normalizedHeckeUnit z (heckeUnitNormalizable_of_residueAdmissible z h) := by
  apply normalizedHeckeUnit_unique
  exact residueNormalizingUnit_spec z h

structure HeckeResidueUnitsBoundary where
  conductorDivisibilityCoordinatesPaid : Bool := true
  sixInvertibleResidueSignaturesExplicit : Bool := true
  listedUnitsDistinctModuloConductorPaid : Bool := true
  admissibleResidueHasUniqueListedUnitPaid : Bool := true
  explicitNormalizerPaid : Bool := true
  idealCoprimeImpliesResidueAdmissiblePaid : Bool := false
  principalIdealCharacterMultiplicativePaid : Bool := false

/-- The finite residue-class part of Hecke normalization is paid. -/
def canonicalBoundary : HeckeResidueUnitsBoundary := {}

end Integration.EisensteinJZeroHeckeResidueUnitsExact
