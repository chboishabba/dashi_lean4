import Integration.EisensteinJZeroHeckeIdealNormalizationExact
import Mathlib.RingTheory.Coprime.Basic

/-!
# Multiplicative finite ideal character for the j=0 Eisenstein curve

The preceding owners prove that every integral ideal coprime to the literal
conductor `f = 2*sqrt(-3)` has a generator normalized by the condition

    alpha_I ≡ 1 (mod f).

This file pays the crucial global algebraic step: that normalized generator is
unique at the IDEAL level and multiplicative under ideal product.  Hence it
defines a literal monoid homomorphism from the submonoid of conductor-coprime
integral ideals to the multiplicative monoid of `EisensteinQA`.

This is the finite-ideal algebraic core of the classical CM Hecke character.
We deliberately do not call the full Grössencharacter/L-function theorem paid:
its archimedean type, bad-prime local factors and analytic Euler-product
identification remain separate owners.

Attribution:
* Mathlib owns the generic ideal monoid, PID and coprimality infrastructure;
* DASHI/Lean owns the conductor-normalization specialization and the proof that
  its normalized generators multiply;
* the identification of this normalization rule with the classical Hecke
  character of `y^2=x^3+1` remains externally sourced.
-/

namespace Integration.EisensteinJZeroHeckeIdealCharacterExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinSixUnitsExact
open Dashi.EisensteinSixUnitOrbitExact
open Integration.EisensteinJZeroHeckeConductorExact
open Integration.EisensteinJZeroHeckeResidueUnitsExact
open Integration.EisensteinJZeroHeckeIdealNormalizationExact

------------------------------------------------------------------------
-- Normalized generators are congruent to one.
------------------------------------------------------------------------

/-- Element normalization really enforces the conductor congruence `≡ 1`. -/
theorem heckeNormalizedElement_congruent_one
    (z : EisensteinQA) (h : HeckeUnitNormalizable z) :
    CongruentModHeckeConductor (heckeNormalizedElement z h) 1 := by
  let U := normalizedHeckeUnitAsUnit z h
  have hU : (U : EisensteinQA) = (normalizedHeckeUnit z h).1 :=
    normalizedHeckeUnitAsUnit_val z h
  rcases normalizedHeckeUnit_spec z h with ⟨q, hq⟩
  unfold CongruentModHeckeConductor
  refine ⟨(↑(U⁻¹) : EisensteinQA) * q, ?_⟩
  unfold heckeNormalizedElement
  change (↑(U⁻¹) : EisensteinQA) * z - 1 =
    heckeConductorElement * ((↑(U⁻¹) : EisensteinQA) * q)
  calc
    (↑(U⁻¹) : EisensteinQA) * z - 1
        = (↑(U⁻¹) : EisensteinQA) * z -
            (↑(U⁻¹) : EisensteinQA) * (U : EisensteinQA) := by simp
    _ = (↑(U⁻¹) : EisensteinQA) * (z - (U : EisensteinQA)) := by ring
    _ = (↑(U⁻¹) : EisensteinQA) *
          (z - (normalizedHeckeUnit z h).1) := by rw [hU]
    _ = (↑(U⁻¹) : EisensteinQA) * (heckeConductorElement * q) := by rw [hq]
    _ = heckeConductorElement * ((↑(U⁻¹) : EisensteinQA) * q) := by ring

/-- Therefore the normalized PID generator of a conductor-coprime ideal is
congruent to one. -/
theorem normalizedIdealGenerator_congruent_one
    (I : Ideal EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I) :
    CongruentModHeckeConductor (normalizedIdealGenerator I hI) 1 :=
  heckeNormalizedElement_congruent_one _
    (rawIdealGenerator_normalizable I hI)

------------------------------------------------------------------------
-- Ideal-level uniqueness.
------------------------------------------------------------------------

private def unitCodeOfUnit (U : EisensteinQAˣ) : EisensteinUnitCode :=
  ⟨(U : EisensteinQA),
    (mem_eisensteinUnits_iff_isUnit (U : EisensteinQA)).2 U.isUnit⟩

private def codeOne : EisensteinUnitCode :=
  ⟨unitOne, by simp [eisensteinUnits]⟩

private theorem codeOne_val : (codeOne : EisensteinUnitCode).1 = (1 : EisensteinQA) := by
  ext <;> norm_num [codeOne, unitOne, asQuadraticAlgebra]

/-- If associated elements are both `1 mod f`, their associating unit is
itself `1 mod f`, hence is literally the unit one by the six-residue theorem. -/
private theorem associated_congruent_one_eq
    {x y : EisensteinQA}
    (hassoc : Associated x y)
    (hx : CongruentModHeckeConductor x 1)
    (hy : CongruentModHeckeConductor y 1) :
    x = y := by
  rcases hassoc with ⟨U, hU⟩
  have hUcong : CongruentModHeckeConductor (U : EisensteinQA) 1 := by
    unfold CongruentModHeckeConductor at hx hy ⊢
    rcases hx with ⟨a, ha⟩
    rcases hy with ⟨b, hb⟩
    refine ⟨a - (U : EisensteinQA) * b, ?_⟩
    calc
      (U : EisensteinQA) - 1
          = (x - 1) - (U : EisensteinQA) * (y - 1) := by
              rw [hU]
              ring
      _ = heckeConductorElement * a -
          (U : EisensteinQA) * (heckeConductorElement * b) := by rw [ha, hb]
      _ = heckeConductorElement * (a - (U : EisensteinQA) * b) := by ring
  have hcode : unitCodeOfUnit U = codeOne :=
    (listedUnits_congruent_iff_eq (unitCodeOfUnit U) codeOne).1 <| by
      simpa [unitCodeOfUnit, codeOne, codeOne_val] using hUcong
  have hval := congrArg (fun c : EisensteinUnitCode => c.1) hcode
  have hUone : (U : EisensteinQA) = 1 := by
    simpa [unitCodeOfUnit, codeOne_val] using hval
  rw [hU, hUone, one_mul]

/-- Any generator of the same conductor-coprime ideal that is congruent to one
must equal the repository's normalized generator.  Thus the construction is
independent of Mathlib's noncomputable PID generator choice. -/
theorem normalizedIdealGenerator_unique
    (I : Ideal EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I)
    (x : EisensteinQA)
    (hxSpan : Ideal.span ({x} : Set EisensteinQA) = I)
    (hxOne : CongruentModHeckeConductor x 1) :
    x = normalizedIdealGenerator I hI := by
  apply associated_congruent_one_eq
  · exact Ideal.span_singleton_eq_span_singleton.mp <|
      hxSpan.trans (normalizedIdealGenerator_spans I hI).symm
  · exact hxOne
  · exact normalizedIdealGenerator_congruent_one I hI

------------------------------------------------------------------------
-- Closure under ideal product and multiplicativity.
------------------------------------------------------------------------

/-- Products of conductor-coprime ideals remain conductor-coprime. -/
theorem idealMul_coprime_conductor
    (I J : Ideal EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I)
    (hJ : IdealCoprimeToHeckeConductor J) :
    IdealCoprimeToHeckeConductor (I * J) := by
  unfold IdealCoprimeToHeckeConductor heckeConductorIdeal
  rw [← rawIdealGenerator_spans I, ← rawIdealGenerator_spans J,
    Ideal.span_singleton_mul_span_singleton]
  exact (Ideal.isCoprime_span_singleton_iff _ _).2 <|
    (rawIdealGenerator_isCoprime I hI).mul_left
      (rawIdealGenerator_isCoprime J hJ)

private theorem normalizedProduct_congruent_one
    (I J : Ideal EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I)
    (hJ : IdealCoprimeToHeckeConductor J) :
    CongruentModHeckeConductor
      (normalizedIdealGenerator I hI * normalizedIdealGenerator J hJ) 1 := by
  unfold CongruentModHeckeConductor at *
  rcases normalizedIdealGenerator_congruent_one I hI with ⟨a, ha⟩
  rcases normalizedIdealGenerator_congruent_one J hJ with ⟨b, hb⟩
  refine ⟨a + b + heckeConductorElement * a * b, ?_⟩
  calc
    normalizedIdealGenerator I hI * normalizedIdealGenerator J hJ - 1
        = (1 + heckeConductorElement * a) *
            (1 + heckeConductorElement * b) - 1 := by
              rw [← ha, ← hb]
              ring
    _ = heckeConductorElement *
          (a + b + heckeConductorElement * a * b) := by ring

private theorem normalizedProduct_spans
    (I J : Ideal EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I)
    (hJ : IdealCoprimeToHeckeConductor J) :
    Ideal.span ({normalizedIdealGenerator I hI *
      normalizedIdealGenerator J hJ} : Set EisensteinQA) = I * J := by
  rw [← Ideal.span_singleton_mul_span_singleton,
    normalizedIdealGenerator_spans I hI,
    normalizedIdealGenerator_spans J hJ]

/-- The conductor-normalized ideal generator is exactly multiplicative. -/
theorem normalizedIdealGenerator_mul
    (I J : Ideal EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I)
    (hJ : IdealCoprimeToHeckeConductor J) :
    normalizedIdealGenerator (I * J)
        (idealMul_coprime_conductor I J hI hJ) =
      normalizedIdealGenerator I hI * normalizedIdealGenerator J hJ := by
  symm
  exact normalizedIdealGenerator_unique (I * J)
    (idealMul_coprime_conductor I J hI hJ)
    _ (normalizedProduct_spans I J hI hJ)
    (normalizedProduct_congruent_one I J hI hJ)

/-- The unit ideal normalizes to one. -/
theorem normalizedIdealGenerator_one :
    normalizedIdealGenerator (⊤ : Ideal EisensteinQA)
      (by simp [IdealCoprimeToHeckeConductor]) = 1 := by
  symm
  apply normalizedIdealGenerator_unique (⊤ : Ideal EisensteinQA)
    (by simp [IdealCoprimeToHeckeConductor]) 1
  · simp
  · unfold CongruentModHeckeConductor
    simp

------------------------------------------------------------------------
-- Literal finite-ideal character.
------------------------------------------------------------------------

/-- Submonoid of integral Eisenstein ideals coprime to the Hecke conductor. -/
def HeckeCoprimeIdealSubmonoid : Submonoid (Ideal EisensteinQA) where
  carrier := {I | IdealCoprimeToHeckeConductor I}
  one_mem' := by simp [IdealCoprimeToHeckeConductor]
  mul_mem' := by
    intro I J hI hJ
    exact idealMul_coprime_conductor I J hI hJ

/-- The conductor-normalized finite ideal character.  This is a genuine monoid
homomorphism on integral ideals coprime to the conductor. -/
noncomputable def finiteIdealHeckeCharacter :
    HeckeCoprimeIdealSubmonoid →* EisensteinQA where
  toFun I := normalizedIdealGenerator I.1 I.2
  map_one' := by
    simpa using normalizedIdealGenerator_one
  map_mul' I J := by
    simpa using normalizedIdealGenerator_mul I.1 J.1 I.2 J.2

structure HeckeIdealCharacterBoundary where
  normalizedGeneratorCongruentOnePaid : Bool := true
  normalizedGeneratorIdealLevelUniquePaid : Bool := true
  idealCoprimeClosedUnderProductPaid : Bool := true
  normalizedGeneratorMultiplicativePaid : Bool := true
  finiteCoprimeIdealMonoidPaid : Bool := true
  finiteIdealCharacterMonoidHomPaid : Bool := true
  archimedeanInfinityTypePaid : Bool := false
  badPrimeLocalCharactersPaid : Bool := false
  globalHeckeLSeriesPaid : Bool := false
  ellipticEulerProductAgreementPaid : Bool := false

/-- The finite ideal-character algebra is paid.  Remaining work is local at the
bad primes and analytic/global, not ideal-generator normalization. -/
def canonicalBoundary : HeckeIdealCharacterBoundary := {}

end Integration.EisensteinJZeroHeckeIdealCharacterExact
