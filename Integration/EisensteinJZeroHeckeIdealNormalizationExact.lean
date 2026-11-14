import Integration.EisensteinJZeroHeckeResidueUnitsExact
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Operations

/-!
# Conductor-coprime principal ideals have normalized Eisenstein generators

`EisensteinQA` is already Euclidean on this branch, hence Mathlib supplies a
principal generator for every ideal.  This file welds that generic PID
infrastructure to the conductor residue theorem.

The substantive steps are:

* `2 | z` iff both Eisenstein coordinates are even;
* `sqrt(-3) | z` iff `3 | (re z + im z)`;
* therefore element-level coprimality with
  `2*sqrt(-3)` implies the explicit residue-admissibility predicate;
* the six-residue theorem then gives a unique normalizing unit;
* an ideal coprime to the conductor has a chosen PID generator coprime to the
  conductor, hence a normalized generator spanning exactly the same ideal.

This pays existence of a conductor-normalized generator for every coprime
integral ideal.  The next global seam is multiplicativity / generator-choice
independence of the resulting ideal-valued character; that is not inferred
merely from the existence of normalized generators.

Attribution: Mathlib owns the PID generator and generic ideal-coprimality API.
DASHI/Lean owns the Eisenstein coordinate specialization and its composition
with the previously paid six-residue theorem.  The CM interpretation of the
modulus remains externally sourced.
-/

namespace Integration.EisensteinJZeroHeckeIdealNormalizationExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinSixUnitsExact
open Integration.EisensteinJZeroHeckeConductorExact
open Integration.EisensteinJZeroHeckeResidueUnitsExact

------------------------------------------------------------------------
-- Prime-factor coordinate tests inside the conductor.
------------------------------------------------------------------------

/-- Divisibility by the inert rational prime two is coordinatewise parity. -/
theorem twoEisenstein_dvd_iff_coordinates (z : EisensteinQA) :
    (2 : EisensteinQA) ∣ z ↔
      (2 : Int) ∣ z.re ∧ (2 : Int) ∣ z.im := by
  constructor
  · rintro ⟨q, hq⟩
    have hre := congrArg QuadraticAlgebra.re hq
    have him := congrArg QuadraticAlgebra.im hq
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
      Int.cast_ofNat, mul_zero, add_zero, zero_mul] at hre him
    exact ⟨⟨q.re, hre⟩, ⟨q.im, him⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨asQuadraticAlgebra a b, ?_⟩
    ext <;>
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
        asQuadraticAlgebra, Int.cast_ofNat, mul_zero, add_zero, zero_mul] <;>
      omega

/-- Divisibility by `sqrt(-3)=1+2*omega` is the single residue condition
`3 | re+im`. -/
theorem sqrtMinusThree_dvd_iff_coordinateSum (z : EisensteinQA) :
    sqrtMinusThreeEisenstein ∣ z ↔
      (3 : Int) ∣ (z.re + z.im) := by
  constructor
  · rintro ⟨q, hq⟩
    have hre := congrArg QuadraticAlgebra.re hq
    have him := congrArg QuadraticAlgebra.im hq
    rw [sqrtMinusThreeEisenstein_coordinates] at hre him
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      asQuadraticAlgebra] at hre him
    refine ⟨q.re - q.im, ?_⟩
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨asQuadraticAlgebra (2 * k - z.re) (k - z.re), ?_⟩
    ext <;>
      rw [sqrtMinusThreeEisenstein_coordinates] <;>
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        asQuadraticAlgebra] <;>
      omega

private theorem commonDivisor_dvd_one_of_isCoprime
    {x y d : EisensteinQA}
    (h : IsCoprime x y) (hdx : d ∣ x) (hdy : d ∣ y) :
    d ∣ 1 := by
  rcases h with ⟨a, b, hab⟩
  rcases hdx with ⟨x', hx'⟩
  rcases hdy with ⟨y', hy'⟩
  refine ⟨a * x' + b * y', ?_⟩
  calc
    1 = a * x + b * y := hab.symm
    _ = a * (d * x') + b * (d * y') := by rw [hx', hy']
    _ = d * (a * x' + b * y') := by ring

/-- Element-level coprimality to the full conductor forces membership in one
of the six invertible residue signatures. -/
theorem residueAdmissible_of_isCoprime_conductor
    (z : EisensteinQA)
    (h : IsCoprime z heckeConductorElement) :
    HeckeResidueAdmissible z := by
  constructor
  · rintro ⟨hre2, him2⟩
    have h2z : (2 : EisensteinQA) ∣ z :=
      (twoEisenstein_dvd_iff_coordinates z).2
        ⟨(Int.dvd_iff_emod_eq_zero).2 hre2,
          (Int.dvd_iff_emod_eq_zero).2 him2⟩
    have h2f : (2 : EisensteinQA) ∣ heckeConductorElement := by
      refine ⟨sqrtMinusThreeEisenstein, ?_⟩
      rfl
    have h21 := commonDivisor_dvd_one_of_isCoprime h h2z h2f
    have hc := (twoEisenstein_dvd_iff_coordinates (1 : EisensteinQA)).1 h21
    norm_num at hc
  · intro hsum
    have h3 : (3 : Int) ∣ (z.re + z.im) :=
      (Int.dvd_iff_emod_eq_zero).2 hsum
    have hsz : sqrtMinusThreeEisenstein ∣ z :=
      (sqrtMinusThree_dvd_iff_coordinateSum z).2 h3
    have hsf : sqrtMinusThreeEisenstein ∣ heckeConductorElement := by
      refine ⟨2, ?_⟩
      rw [heckeConductorElement]
      ring
    have hs1 := commonDivisor_dvd_one_of_isCoprime h hsz hsf
    have hc :=
      (sqrtMinusThree_dvd_iff_coordinateSum (1 : EisensteinQA)).1 hs1
    norm_num at hc

------------------------------------------------------------------------
-- Descent to conductor-coprime integral ideals.
------------------------------------------------------------------------

/-- Literal conductor ideal generated by `2*sqrt(-3)`. -/
def heckeConductorIdeal : Ideal EisensteinQA :=
  Ideal.span ({heckeConductorElement} : Set EisensteinQA)

/-- Integral ideals eligible for conductor normalization. -/
def IdealCoprimeToHeckeConductor (I : Ideal EisensteinQA) : Prop :=
  Ideal.IsCoprime I heckeConductorIdeal

/-- Mathlib's principal generator, available because `EisensteinQA` is already
Euclidean/PID in this branch. -/
noncomputable def rawIdealGenerator (I : Ideal EisensteinQA) : EisensteinQA :=
  Submodule.IsPrincipal.generator I

/-- The chosen raw generator really spans the ideal. -/
theorem rawIdealGenerator_spans (I : Ideal EisensteinQA) :
    Ideal.span ({rawIdealGenerator I} : Set EisensteinQA) = I := by
  exact Submodule.IsPrincipal.span_singleton_generator I

/-- Ideal-level conductor coprimality transfers to the chosen generator. -/
theorem rawIdealGenerator_isCoprime
    (I : Ideal EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I) :
    IsCoprime (rawIdealGenerator I) heckeConductorElement := by
  unfold IdealCoprimeToHeckeConductor heckeConductorIdeal at hI
  rw [← rawIdealGenerator_spans I] at hI
  exact (Ideal.isCoprime_span_singleton_iff _ _).1 hI

/-- Every conductor-coprime ideal's chosen PID generator lies in one of the six
invertible conductor residue classes. -/
theorem rawIdealGenerator_residueAdmissible
    (I : Ideal EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I) :
    HeckeResidueAdmissible (rawIdealGenerator I) :=
  residueAdmissible_of_isCoprime_conductor _
    (rawIdealGenerator_isCoprime I hI)

/-- Therefore every conductor-coprime ideal has a unique six-unit
normalization. -/
theorem rawIdealGenerator_normalizable
    (I : Ideal EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I) :
    HeckeUnitNormalizable (rawIdealGenerator I) :=
  heckeUnitNormalizable_of_residueAdmissible _
    (rawIdealGenerator_residueAdmissible I hI)

/-- The normalized generator attached to a conductor-coprime ideal. -/
noncomputable def normalizedIdealGenerator
    (I : Ideal EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I) : EisensteinQA :=
  heckeNormalizedElement (rawIdealGenerator I)
    (rawIdealGenerator_normalizable I hI)

/-- Unit normalization preserves the principal ideal exactly. -/
theorem normalizedIdealGenerator_spans
    (I : Ideal EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I) :
    Ideal.span ({normalizedIdealGenerator I hI} : Set EisensteinQA) = I := by
  rw [← rawIdealGenerator_spans I]
  apply Ideal.span_singleton_eq_span_singleton.mpr
  let U := normalizedHeckeUnitAsUnit (rawIdealGenerator I)
    (rawIdealGenerator_normalizable I hI)
  change Associated ((↑(U⁻¹) : EisensteinQA) * rawIdealGenerator I)
    (rawIdealGenerator I)
  exact ⟨U⁻¹, rfl⟩

structure HeckeIdealNormalizationBoundary where
  factorTwoCoordinateCriterionPaid : Bool := true
  ramifiedThreeCoordinateCriterionPaid : Bool := true
  coprimeElementImpliesAdmissibleResiduePaid : Bool := true
  pidGeneratorAvailable : Bool := true
  idealCoprimeImpliesGeneratorNormalizablePaid : Bool := true
  normalizedGeneratorSpansSameIdealPaid : Bool := true
  normalizedGeneratorIndependentOfPidChoicePaid : Bool := false
  normalizedGeneratorMultiplicativeOnIdealProductPaid : Bool := false
  groessencharacterPaid : Bool := false

/-- Existence of normalized generators is paid; ideal-character
multiplicativity is now the first internal global seam. -/
def canonicalBoundary : HeckeIdealNormalizationBoundary := {}

end Integration.EisensteinJZeroHeckeIdealNormalizationExact
