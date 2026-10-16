import Integration.EisensteinJZeroHeckeMultiplicativityExact

/-!
# Integral conductor-coprime Hecke character

The previous tranche proves that every integral Eisenstein ideal coprime to
the literal conductor `2*sqrt(-3)` has a unique generator congruent to one
modulo that conductor, and that these generators multiply.

This file packages exactly that theorem as a `MonoidHom` on the submonoid of
conductor-coprime integral ideals.  It is the integral ideal-character core of
the j=0 Groessencharacter construction.

Attribution boundary:
* the CM interpretation of the modulus remains externally sourced;
* Mathlib owns ideal/submonoid/monoid-hom infrastructure;
* DASHI/Lean owns the explicit normalization and multiplicativity theorem;
* no fractional-ideal extension, archimedean type, analytic Hecke L-series or
  elliptic/Hecke L-function equality is claimed here.
-/

namespace Integration.EisensteinJZeroIntegralHeckeCharacterExact

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroHeckeConductorExact
open Integration.EisensteinJZeroHeckeIdealNormalizationExact
open Integration.EisensteinJZeroHeckeMultiplicativityExact

/-- The multiplicative monoid of integral Eisenstein ideals prime to the
literal Hecke conductor. -/
def heckeCoprimeIdealSubmonoid : Submonoid (Ideal EisensteinQA) where
  carrier := {I | IdealCoprimeToHeckeConductor I}
  one_mem' := by
    unfold IdealCoprimeToHeckeConductor
    simp [heckeConductorIdeal]
  mul_mem' := by
    intro I J hI hJ
    exact idealMul_coprime_conductor I J hI hJ

/-- Short carrier name used by the global CM lane. -/
abbrev HeckeIdealMonoid := heckeCoprimeIdealSubmonoid

private theorem normalizedIdealGenerator_top :
    normalizedIdealGenerator (⊤ : Ideal EisensteinQA)
      (show IdealCoprimeToHeckeConductor (⊤ : Ideal EisensteinQA) by
        unfold IdealCoprimeToHeckeConductor
        simp [heckeConductorIdeal]) = 1 := by
  let htop : IdealCoprimeToHeckeConductor (⊤ : Ideal EisensteinQA) := by
    unfold IdealCoprimeToHeckeConductor
    simp [heckeConductorIdeal]
  apply heckeNormalizedGenerator_unique (⊤ : Ideal EisensteinQA) htop
  · exact normalizedIdealGenerator_isNormalized (⊤ : Ideal EisensteinQA) htop
  · constructor
    · simp
    · exact congruentModHeckeConductor_refl 1

/-- The conductor-normalized integral ideal character. -/
noncomputable def integralHeckeCharacter : HeckeIdealMonoid →* EisensteinQA where
  toFun I := normalizedIdealGenerator I.1 I.2
  map_one' := by
    simpa [HeckeIdealMonoid, heckeCoprimeIdealSubmonoid] using
      normalizedIdealGenerator_top
  map_mul' := by
    intro I J
    change normalizedIdealGenerator (I.1 * J.1) _ =
      normalizedIdealGenerator I.1 I.2 * normalizedIdealGenerator J.1 J.2
    simpa using normalizedIdealGenerator_mul I.1 J.1 I.2 J.2

/-- The character value is a genuine generator of the input ideal. -/
theorem integralHeckeCharacter_spans (I : HeckeIdealMonoid) :
    Ideal.span ({integralHeckeCharacter I} : Set EisensteinQA) = I.1 := by
  exact normalizedIdealGenerator_spans I.1 I.2

/-- The character value has the defining conductor normalization. -/
theorem integralHeckeCharacter_congruent_one (I : HeckeIdealMonoid) :
    CongruentModHeckeConductor (integralHeckeCharacter I) 1 := by
  exact (normalizedIdealGenerator_isNormalized I.1 I.2).2

/-- Intrinsic uniqueness: any other generator of the same conductor-coprime
ideal congruent to one is exactly the character value. -/
theorem integralHeckeCharacter_eq_of_normalized
    (I : HeckeIdealMonoid) (z : EisensteinQA)
    (hzSpan : Ideal.span ({z} : Set EisensteinQA) = I.1)
    (hzCong : CongruentModHeckeConductor z 1) :
    integralHeckeCharacter I = z := by
  apply heckeNormalizedGenerator_unique I.1 I.2
  · exact normalizedIdealGenerator_isNormalized I.1 I.2
  · exact ⟨hzSpan, hzCong⟩

/-- Norm compatibility is intentionally stated only conditionally here:
once an ideal-norm owner is selected, the value already spans the ideal and
therefore supplies the correct principal generator.  No hidden analytic norm
or fractional-ideal semantics are introduced by this packaging layer. -/
structure IntegralHeckeCharacterBoundary where
  conductorCoprimeIdealSubmonoidPaid : Bool := true
  normalizedIdealValuePaid : Bool := true
  monoidHomMultiplicativityPaid : Bool := true
  valueSpansInputIdealPaid : Bool := true
  conductorNormalizationPaid : Bool := true
  intrinsicValueUniquenessPaid : Bool := true
  fractionalIdealCharacterPaid : Bool := false
  archimedeanInfinityTypePaid : Bool := false
  primeIdealEllipticLocalMatchPaid : Bool := false
  analyticHeckeLSeriesPaid : Bool := false
  ellipticHeckeLSeriesAgreementPaid : Bool := false

/-- The integral ideal-character core is complete. -/
def canonicalBoundary : IntegralHeckeCharacterBoundary := {}

end Integration.EisensteinJZeroIntegralHeckeCharacterExact
