import Integration.EisensteinQuadraticAlgebraExact
import Integration.EisensteinSixUnitOrbitExact

/-!
# Same-carrier Hecke conductor for the j=0 Eisenstein curve

External CM literature for `E : y^2 = x^3 + 1` describes the associated
Hecke character over `Q(sqrt(-3))` by normalizing a principal prime-ideal
generator modulo `2*sqrt(-3)`: among the six roots of unity there is a unique
unit congruent to the generator modulo this conductor, and the character value
is the correspondingly normalized generator.

External provenance for that statement remains EXTERNAL. In particular this
file does not present the literature statement as a DASHI theorem. What this
file owns is the exact same-carrier realization of that modulus inside the
repository's already-declared

    EisensteinQA = QuadraticAlgebra Int (-1) (-1),

where `sqrt(-3)=1+2*omega`. Thus

    f = 2*sqrt(-3) = 2+4*omega,
    N(f)=12.

Since the quadratic-field discriminant has absolute value 3, the familiar
conductor-norm product is `12*3=36`, matching the externally recorded rational
curve conductor. This numerical match is a consistency bridge, not a proof of
the external conductor theorem.

The file also gives the exact proof-relevant seam needed for globalization:
`HeckeUnitNormalizable z` means there is a UNIQUE one of the repository's six
Eisenstein units congruent to `z` modulo the literal conductor element.
Nothing here assumes every ideal generator has that property; proving it on
the required coprime principal ideals is the next global theorem.

Attribution:
* the conductor-normalization statement is externally sourced (Tu--Yang /
  standard CM-Hecke literature), not repo-owned;
* Mathlib owns generic quadratic-algebra/divisibility infrastructure;
* DASHI/Lean owns only this carrier realization and typed normalization seam.
-/

namespace Integration.EisensteinJZeroHeckeConductorExact

open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinSixUnitsExact
open Dashi.EisensteinSixUnitOrbitExact

/-- The literal Eisenstein integer corresponding to `sqrt(-3)=1+2*omega`. -/
def sqrtMinusThreeEisenstein : EisensteinQA :=
  1 + 2 * (QuadraticAlgebra.omega : EisensteinQA)

/-- Coordinate form of the square-root-of-minus-three element. -/
theorem sqrtMinusThreeEisenstein_coordinates :
    sqrtMinusThreeEisenstein = asQuadraticAlgebra 1 2 := by
  ext <;> norm_num [sqrtMinusThreeEisenstein, asQuadraticAlgebra]

/-- Literal quadratic identity `(1+2*omega)^2=-3`. -/
theorem sqrtMinusThreeEisenstein_sq :
    sqrtMinusThreeEisenstein ^ 2 = (-3 : EisensteinQA) := by
  unfold sqrtMinusThreeEisenstein
  have hω := omega_square_relation
  rw [show (QuadraticAlgebra.omega : EisensteinQA) ^ 2 =
      -(1 : EisensteinQA) - QuadraticAlgebra.omega from hω]
  ring

/-- The externally specified CM normalization modulus, realized on the exact
repo carrier. -/
def heckeConductorElement : EisensteinQA :=
  2 * sqrtMinusThreeEisenstein

/-- Coordinate form `2+4*omega`. -/
theorem heckeConductorElement_coordinates :
    heckeConductorElement = asQuadraticAlgebra 2 4 := by
  rw [heckeConductorElement, sqrtMinusThreeEisenstein_coordinates]
  ext <;> norm_num [asQuadraticAlgebra]

/-- The literal Eisenstein norm of the conductor generator is twelve. -/
theorem heckeConductorElement_norm :
    QuadraticAlgebra.norm heckeConductorElement = 12 := by
  rw [heckeConductorElement_coordinates, norm_asQuadraticAlgebra]
  norm_num [eisensteinNorm]

/-- Consistency bridge to the externally recorded rational conductor 36:
`Norm(2*sqrt(-3))*|disc Q(sqrt(-3))| = 12*3 = 36`.
The field-discriminant value `3` is intentionally explicit rather than hidden
inside an unsourced conductor theorem. -/
theorem conductorNorm_times_fieldDiscriminant : 12 * 3 = 36 := by
  norm_num

------------------------------------------------------------------------
-- Exact typed normalization seam.
------------------------------------------------------------------------

/-- Congruence modulo the literal conductor generator. -/
def CongruentModHeckeConductor (z w : EisensteinQA) : Prop :=
  heckeConductorElement ∣ z - w

/-- A literal Eisenstein element is Hecke-unit-normalizable exactly when there
is a UNIQUE unit among the repo's classified six units congruent to it modulo
`2*sqrt(-3)`.

This is the formal predicate required by the externally sourced CM
normalization rule; existence for all generators prime to the conductor is not
manufactured here. -/
def HeckeUnitNormalizable (z : EisensteinQA) : Prop :=
  ∃! u : EisensteinUnitCode,
    CongruentModHeckeConductor z u.1

/-- Choose the unique normalizing unit from a proof of normalizability. -/
noncomputable def normalizedHeckeUnit
    (z : EisensteinQA) (h : HeckeUnitNormalizable z) : EisensteinUnitCode :=
  Classical.choose h

/-- The chosen unit satisfies the required conductor congruence. -/
theorem normalizedHeckeUnit_spec
    (z : EisensteinQA) (h : HeckeUnitNormalizable z) :
    CongruentModHeckeConductor z (normalizedHeckeUnit z h).1 :=
  (Classical.choose_spec h).1

/-- Any listed unit satisfying the same congruence is the chosen unit. -/
theorem normalizedHeckeUnit_unique
    (z : EisensteinQA) (h : HeckeUnitNormalizable z)
    (u : EisensteinUnitCode)
    (hu : CongruentModHeckeConductor z u.1) :
    u = normalizedHeckeUnit z h := by
  exact ((Classical.choose_spec h).2 u hu).symm

/-- The selected listed Eisenstein integer, bundled as an actual unit of the
ring.  This is the correct carrier on which inversion is defined. -/
noncomputable def normalizedHeckeUnitAsUnit
    (z : EisensteinQA) (h : HeckeUnitNormalizable z) : EisensteinQAˣ :=
  (all_listed_units_are_units
    (normalizedHeckeUnit z h).1 (normalizedHeckeUnit z h).2).unit

@[simp]
theorem normalizedHeckeUnitAsUnit_val
    (z : EisensteinQA) (h : HeckeUnitNormalizable z) :
    (normalizedHeckeUnitAsUnit z h : EisensteinQA) =
      (normalizedHeckeUnit z h).1 := by
  exact IsUnit.unit_spec _

/-- Multiplying by the inverse selected unit gives the normalized generator.
The inverse is taken in `EisensteinQAˣ`, not via an accidental ring-level
inverse.  This is intentionally an element-level operation; descent to
principal ideals and proof of multiplicativity are separate global payments. -/
noncomputable def heckeNormalizedElement
    (z : EisensteinQA) (h : HeckeUnitNormalizable z) : EisensteinQA :=
  ((normalizedHeckeUnitAsUnit z h)⁻¹ : EisensteinQAˣ) * z

structure HeckeConductorBoundary where
  externalNormalizationRuleRecordedAsExternal : Bool := true
  literalSqrtMinusThreeCarrierPaid : Bool := true
  literalConductorElementPaid : Bool := true
  conductorElementNormTwelvePaid : Bool := true
  conductorNormTimesFieldDiscriminantThirtySixPaid : Bool := true
  uniqueSixUnitNormalizationPredicateTyped : Bool := true
  normalizationChoiceInterfacePaid : Bool := true
  everyCoprimePrincipalGeneratorNormalizablePaid : Bool := false
  normalizationIndependentOfGeneratorPaid : Bool := false
  normalizedIdealCharacterMultiplicativePaid : Bool := false
  groessencharacterPaid : Bool := false

/-- Exact boundary after realizing the externally specified conductor on the
repo carrier. -/
def canonicalBoundary : HeckeConductorBoundary := {}

end Integration.EisensteinJZeroHeckeConductorExact
