import Integration.EisensteinJZeroHeckeIdealNormalizationExact
import Mathlib.RingTheory.Coprime.Basic

/-!
# Multiplicativity of conductor-normalized Eisenstein ideal generators

The preceding owner gives every integral ideal coprime to the literal
`2*sqrt(-3)` conductor a normalized generator.  This file pays the next
internal globalization seam.

The key intrinsic characterization is:

  a normalized generator of I
    = an element z with (z)=I and z ≡ 1 mod f.

For conductor-coprime I this characterization is unique.  Indeed, two such
generators differ by a unit; their congruences imply `(u-1)z` is divisible by
f, and coprimality cancels z.  The six-unit residue theorem then forces u=1.
The product of two normalized generators again spans the product ideal and is
congruent to one, so uniqueness gives multiplicativity.

Everything below is repo-owned algebra over Mathlib's PID/coprimality APIs.
The external CM literature is not used as proof authority.  This is the
integral-ideal multiplicativity theorem needed for the Groessencharacter lane;
analytic Euler products and global L-function identities remain separate.
-/

namespace Integration.EisensteinJZeroHeckeMultiplicativityExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinSixUnitsExact
open Dashi.EisensteinSixUnitOrbitExact
open Integration.EisensteinJZeroHeckeConductorExact
open Integration.EisensteinJZeroHeckeResidueUnitsExact
open Integration.EisensteinJZeroHeckeIdealNormalizationExact

------------------------------------------------------------------------
-- Conductor congruence is a multiplicative ring congruence.
------------------------------------------------------------------------

theorem congruentModHeckeConductor_refl (z : EisensteinQA) :
    CongruentModHeckeConductor z z := by
  unfold CongruentModHeckeConductor
  simp

theorem congruentModHeckeConductor_symm {z w : EisensteinQA}
    (h : CongruentModHeckeConductor z w) :
    CongruentModHeckeConductor w z := by
  unfold CongruentModHeckeConductor at h ⊢
  rcases h with ⟨a, ha⟩
  refine ⟨-a, ?_⟩
  rw [ha]
  ring

theorem congruentModHeckeConductor_trans {x y z : EisensteinQA}
    (hxy : CongruentModHeckeConductor x y)
    (hyz : CongruentModHeckeConductor y z) :
    CongruentModHeckeConductor x z := by
  unfold CongruentModHeckeConductor at hxy hyz ⊢
  rcases hxy with ⟨a, ha⟩
  rcases hyz with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  rw [show x - z = (x - y) + (y - z) by ring, ha, hb]
  ring

/-- Multiplication respects the literal conductor congruence. -/
theorem congruentModHeckeConductor_mul
    {z w z' w' : EisensteinQA}
    (hz : CongruentModHeckeConductor z z')
    (hw : CongruentModHeckeConductor w w') :
    CongruentModHeckeConductor (z * w) (z' * w') := by
  unfold CongruentModHeckeConductor at hz hw ⊢
  rcases hz with ⟨a, ha⟩
  rcases hw with ⟨b, hb⟩
  refine ⟨z * b + a * w', ?_⟩
  calc
    z * w - z' * w' = z * (w - w') + (z - z') * w' := by ring
    _ = z * (heckeConductorElement * b) +
          (heckeConductorElement * a) * w' := by rw [ha, hb]
    _ = heckeConductorElement * (z * b + a * w') := by ring

------------------------------------------------------------------------
-- Element normalization.
------------------------------------------------------------------------

/-- The normalized element is literally one modulo the conductor. -/
theorem heckeNormalizedElement_congruent_one
    (z : EisensteinQA) (hz : HeckeUnitNormalizable z) :
    CongruentModHeckeConductor (heckeNormalizedElement z hz) 1 := by
  let U := normalizedHeckeUnitAsUnit z hz
  have hu := normalizedHeckeUnit_spec z hz
  have hleft : CongruentModHeckeConductor
      ((↑(U⁻¹) : EisensteinQA)) ((↑(U⁻¹) : EisensteinQA)) :=
    congruentModHeckeConductor_refl _
  have hm := congruentModHeckeConductor_mul hleft hu
  change CongruentModHeckeConductor
    ((↑(U⁻¹) : EisensteinQA) * z)
    ((↑(U⁻¹) : EisensteinQA) * (normalizedHeckeUnit z hz).1) at hm
  have hunit :
      (↑(U⁻¹) : EisensteinQA) * (normalizedHeckeUnit z hz).1 = 1 := by
    rw [← normalizedHeckeUnitAsUnit_val z hz]
    exact Units.inv_mul U
  simpa [heckeNormalizedElement, U, hunit] using hm

/-- Product of two listed unit codes, retained on the exact six-unit carrier. -/
def mulUnitCode (u v : EisensteinUnitCode) : EisensteinUnitCode :=
  ⟨u.1 * v.1,
    (mem_eisensteinUnits_iff_isUnit _).2
      ((all_listed_units_are_units u.1 u.2).mul
        (all_listed_units_are_units v.1 v.2))⟩

/-- Normalizability is closed under multiplication. -/
theorem heckeUnitNormalizable_mul
    (z w : EisensteinQA)
    (hz : HeckeUnitNormalizable z) (hw : HeckeUnitNormalizable w) :
    HeckeUnitNormalizable (z * w) := by
  let u := normalizedHeckeUnit z hz
  let v := normalizedHeckeUnit w hw
  let uv := mulUnitCode u v
  have hprod : CongruentModHeckeConductor (z * w) uv.1 := by
    simpa [u, v, uv, mulUnitCode] using
      congruentModHeckeConductor_mul
        (normalizedHeckeUnit_spec z hz)
        (normalizedHeckeUnit_spec w hw)
  refine ⟨uv, hprod, ?_⟩
  intro q hq
  apply (listedUnits_congruent_iff_eq q uv).1
  exact congruentModHeckeConductor_trans
    (congruentModHeckeConductor_symm hq) hprod

private theorem normalizedHeckeUnit_mul
    (z w : EisensteinQA)
    (hz : HeckeUnitNormalizable z) (hw : HeckeUnitNormalizable w) :
    normalizedHeckeUnit (z * w) (heckeUnitNormalizable_mul z w hz hw) =
      mulUnitCode (normalizedHeckeUnit z hz) (normalizedHeckeUnit w hw) := by
  apply Eq.symm
  apply normalizedHeckeUnit_unique
  simpa [mulUnitCode] using
    congruentModHeckeConductor_mul
      (normalizedHeckeUnit_spec z hz)
      (normalizedHeckeUnit_spec w hw)

private theorem normalizedHeckeUnitAsUnit_mul
    (z w : EisensteinQA)
    (hz : HeckeUnitNormalizable z) (hw : HeckeUnitNormalizable w) :
    normalizedHeckeUnitAsUnit (z * w) (heckeUnitNormalizable_mul z w hz hw) =
      normalizedHeckeUnitAsUnit z hz * normalizedHeckeUnitAsUnit w hw := by
  apply Units.ext
  rw [normalizedHeckeUnitAsUnit_val, normalizedHeckeUnitAsUnit_val,
    normalizedHeckeUnitAsUnit_val, normalizedHeckeUnit_mul]
  rfl

/-- The element-level conductor normalization is multiplicative. -/
theorem heckeNormalizedElement_mul
    (z w : EisensteinQA)
    (hz : HeckeUnitNormalizable z) (hw : HeckeUnitNormalizable w) :
    heckeNormalizedElement (z * w) (heckeUnitNormalizable_mul z w hz hw) =
      heckeNormalizedElement z hz * heckeNormalizedElement w hw := by
  unfold heckeNormalizedElement
  rw [normalizedHeckeUnitAsUnit_mul z w hz hw]
  simp only [mul_inv_rev]
  ring

------------------------------------------------------------------------
-- Intrinsic normalized-generator characterization and uniqueness.
------------------------------------------------------------------------

def IsHeckeNormalizedGenerator (I : Ideal EisensteinQA) (z : EisensteinQA) : Prop :=
  Ideal.span ({z} : Set EisensteinQA) = I ∧
    CongruentModHeckeConductor z 1

/-- The chosen normalized PID generator has the intrinsic characterization. -/
theorem normalizedIdealGenerator_isNormalized
    (I : Ideal EisensteinQA) (hI : IdealCoprimeToHeckeConductor I) :
    IsHeckeNormalizedGenerator I (normalizedIdealGenerator I hI) := by
  exact ⟨normalizedIdealGenerator_spans I hI,
    heckeNormalizedElement_congruent_one _ _⟩

private theorem generator_isCoprime_conductor_of_normalized
    (I : Ideal EisensteinQA) (hI : IdealCoprimeToHeckeConductor I)
    (z : EisensteinQA) (hz : IsHeckeNormalizedGenerator I z) :
    IsCoprime z heckeConductorElement := by
  unfold IdealCoprimeToHeckeConductor heckeConductorIdeal at hI
  rw [← hz.1] at hI
  exact (Ideal.isCoprime_span_singleton_iff _ _).1 hI

/-- A conductor-coprime ideal has at most one generator congruent to one modulo
its conductor.  This removes dependence on the arbitrary PID generator. -/
theorem heckeNormalizedGenerator_unique
    (I : Ideal EisensteinQA) (hI : IdealCoprimeToHeckeConductor I)
    {z w : EisensteinQA}
    (hz : IsHeckeNormalizedGenerator I z)
    (hw : IsHeckeNormalizedGenerator I w) : z = w := by
  have hassoc : Associated z w :=
    Ideal.span_singleton_eq_span_singleton.mp (hz.1.trans hw.1.symm)
  rcases hassoc with ⟨U, hU⟩
  have hzw : heckeConductorElement ∣ w - z := by
    unfold CongruentModHeckeConductor at hz hw
    rcases hz.2 with ⟨a, ha⟩
    rcases hw.2 with ⟨b, hb⟩
    refine ⟨b - a, ?_⟩
    rw [show w - z = (w - 1) - (z - 1) by ring, ha, hb]
    ring
  have hprod : heckeConductorElement ∣ z * ((U : EisensteinQA) - 1) := by
    rw [← hU]
    simpa [mul_sub] using hzw
  have hcop : IsCoprime heckeConductorElement z :=
    isCoprime_comm.mp (generator_isCoprime_conductor_of_normalized I hI z hz)
  have hunitCong : CongruentModHeckeConductor (U : EisensteinQA) 1 := by
    unfold CongruentModHeckeConductor
    apply hcop.dvd_of_dvd_mul_right
    simpa [mul_comm] using hprod
  let ucode : EisensteinUnitCode :=
    ⟨(U : EisensteinQA),
      (mem_eisensteinUnits_iff_isUnit _).2 U.isUnit⟩
  let onecode : EisensteinUnitCode :=
    ⟨unitOne, by simp [eisensteinUnits]⟩
  have hcodes : ucode = onecode := by
    apply (listedUnits_congruent_iff_eq ucode onecode).1
    simpa [ucode, onecode, unitOne, asQuadraticAlgebra] using hunitCong
  have hUone : U = 1 := by
    apply Units.ext
    have := congrArg (fun q : EisensteinUnitCode => q.1) hcodes
    simpa [ucode, onecode, unitOne, asQuadraticAlgebra] using this
  rw [hUone] at hU
  simpa using hU

------------------------------------------------------------------------
-- Multiplication on conductor-coprime ideals.
------------------------------------------------------------------------

/-- The product of conductor-coprime ideals is conductor-coprime. -/
theorem idealMul_coprime_conductor
    (I J : Ideal EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I)
    (hJ : IdealCoprimeToHeckeConductor J) :
    IdealCoprimeToHeckeConductor (I * J) := by
  have hi := rawIdealGenerator_isCoprime I hI
  have hj := rawIdealGenerator_isCoprime J hJ
  have hij : IsCoprime
      (rawIdealGenerator I * rawIdealGenerator J) heckeConductorElement :=
    IsCoprime.mul_left hi hj
  unfold IdealCoprimeToHeckeConductor heckeConductorIdeal
  rw [← rawIdealGenerator_spans I, ← rawIdealGenerator_spans J,
    Ideal.span_singleton_mul_span_singleton]
  exact (Ideal.isCoprime_span_singleton_iff _ _).2 hij

/-- Product of the two normalized generators is itself the intrinsic
normalized generator of the product ideal. -/
theorem normalizedIdealGenerator_mul
    (I J : Ideal EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I)
    (hJ : IdealCoprimeToHeckeConductor J) :
    normalizedIdealGenerator (I * J) (idealMul_coprime_conductor I J hI hJ) =
      normalizedIdealGenerator I hI * normalizedIdealGenerator J hJ := by
  let hIJ := idealMul_coprime_conductor I J hI hJ
  apply heckeNormalizedGenerator_unique (I * J) hIJ
  · exact normalizedIdealGenerator_isNormalized (I * J) hIJ
  · constructor
    · rw [← Ideal.span_singleton_mul_span_singleton,
        normalizedIdealGenerator_spans I hI,
        normalizedIdealGenerator_spans J hJ]
    · simpa using congruentModHeckeConductor_mul
        (normalizedIdealGenerator_isNormalized I hI).2
        (normalizedIdealGenerator_isNormalized J hJ).2

structure HeckeMultiplicativityBoundary where
  conductorCongruenceMultiplicativePaid : Bool := true
  elementNormalizationMultiplicativePaid : Bool := true
  intrinsicNormalizedGeneratorUniquenessPaid : Bool := true
  pidChoiceIndependencePaid : Bool := true
  conductorCoprimeIdealProductClosurePaid : Bool := true
  normalizedIdealGeneratorMultiplicativePaid : Bool := true
  groessencharacterIntegralIdealMonoidReady : Bool := true
  fractionalIdealExtensionPaid : Bool := false
  analyticHeckeLSeriesPaid : Bool := false
  ellipticHeckeEulerProductAgreementPaid : Bool := false

/-- The integral conductor-coprime ideal character is now multiplicative. -/
def canonicalBoundary : HeckeMultiplicativityBoundary := {}

end Integration.EisensteinJZeroHeckeMultiplicativityExact
