import Synthesis.MillenniumBSDActualE2H1SameObject
import Synthesis.MillenniumBSDQuadraticKummerPair

/-!
# BA4: isolate the sole remaining H¹ representation theorem

All arithmetic in the quadratic Kummer comparison is now paid.  The scalar
square-class map is a bijection, and its two-coordinate product identifies the
literal descent carrier with a pair of continuous quadratic characters.

Therefore the remaining global BA4 producer is *only* the low-degree
continuous-cohomology representation theorem for the trivial two-torsion
module:

  H¹_cont(G_Q,(C₂)^2_triv)
    ≃ Hom_cont(G_Q,C₂) × Hom_cont(G_Q,C₂).

Supplying that representation theorem compiles immediately to the existing
`RationalQuadraticContinuousKummerProducer`; no Hilbert 90, square-class
descent, or elliptic two-torsion geometry remains in this seam.
-/

namespace Synthesis.Millennium.BSD

/-- Exact remaining cohomological producer after scalar Kummer has been paid. -/
def TrivialE2H1QuadraticCharacterPairProducer : Prop :=
  Nonempty
    ((continuousCohomology 1 cmTwoTorsionRepresentation) ≃
      (RationalQuadraticCharacter × RationalQuadraticCharacter))

/-- The only missing H¹ representation theorem compiles with the paid pair
Kummer equivalence to the square-class producer expected by the existing BA4
lane. -/
noncomputable theorem rationalQuadraticContinuousKummerProducer_of_characterPair
    (h : TrivialE2H1QuadraticCharacterPairProducer) :
    RationalQuadraticContinuousKummerProducer := by
  rcases h with ⟨e⟩
  exact ⟨e.trans quadraticCharacterPairEquivRatSquareClasses⟩

/-- Consequently the actual geometric `E[2]` H¹ is identified with the
literal pair of rational square classes from exactly that one producer. -/
noncomputable def cmActualE2H1EquivRatSquareClasses_of_characterPair
    (h : TrivialE2H1QuadraticCharacterPairProducer) :
    (continuousCohomology 1 cmActualE2Representation) ≃
      (RatSquareClass × RatSquareClass) :=
  cmActualE2H1EquivRatSquareClasses
    (rationalQuadraticContinuousKummerProducer_of_characterPair h)

/-- Machine-readable statement of the narrowed BA4 boundary. -/
structure BA4KummerBoundaryStatus where
  scalarSquareClassDescentPaid : Bool
  scalarCharacterInjectivityPaid : Bool
  scalarCharacterSurjectivityPaid : Bool
  pairKummerEquivalencePaid : Bool
  trivialH1CharacterPairRepresentationPaid : Bool
  deriving DecidableEq, Repr

def ba4KummerBoundaryStatus : BA4KummerBoundaryStatus :=
  ⟨true, true, true, true, false⟩

theorem ba4_only_characterPair_representation_unpaid :
    ba4KummerBoundaryStatus =
      ⟨true, true, true, true, false⟩ := rfl

end Synthesis.Millennium.BSD
