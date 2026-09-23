import Synthesis.MillenniumBSDTrivialTwoTorsionH1Generic
import Synthesis.MillenniumBSDSquareClassGroups
import Mathlib.Tactic

/-!
# Local Kummer cohomology reduction

All representation-theoretic continuous H¹ work is now generic in the field.
For the explicit p-adic two-descent lane, the only remaining local arithmetic
owner is the scalar quadratic Kummer equivalence

  Q_p^*/Q_p^{*2} ≃ Hom_cont(G_{Q_p}, C₂).

Once this scalar equivalence is supplied, the pair-valued H¹ identification
used by E[2] is compiled automatically.
-/

namespace Synthesis.Millennium.BSD

/-- Absolute Galois group of Q_p. -/
abbrev PadicAbsoluteGalois (p : ℕ) [Fact p.Prime] :=
  Field.absoluteGaloisGroup ℚ_[p]

/-- Scalar continuous quadratic characters of G_{Q_p}. -/
abbrev PadicQuadraticCharacter (p : ℕ) [Fact p.Prime] :=
  GenericQuadraticCharacter (PadicAbsoluteGalois p)

/-- Exact scalar local arithmetic theorem still required at a p-adic place. -/
def PadicQuadraticKummerProducer (p : ℕ) [Fact p.Prime] : Prop :=
  Nonempty
    (PadicSquareClass p ≃*
      PadicQuadraticCharacter p)

/-- A paid scalar local Kummer equivalence automatically gives the pair-valued
square-class/character equivalence used by full rational two-descent. -/
noncomputable def padicSquareClassPairMulEquivQuadraticCharacters
    (p : ℕ) [Fact p.Prime]
    (h : PadicQuadraticKummerProducer p) :
    (PadicSquareClass p × PadicSquareClass p) ≃*
      (PadicQuadraticCharacter p × PadicQuadraticCharacter p) := by
  rcases h with ⟨e⟩
  exact e.prodCongr e

/-- The representation-theoretic half is already paid for every field.
Thus scalar p-adic Kummer alone produces the full local H¹/square-class pair
identification. -/
noncomputable def padicTwoTorsionH1MulEquivSquareClassPair
    (p : ℕ) [Fact p.Prime]
    (h : PadicQuadraticKummerProducer p) :
    Multiplicative
      (ContinuousCohomology.continuousCohomology 1
        (genericTwoTorsionRepresentation
          (PadicAbsoluteGalois p))) ≃*
      (PadicSquareClass p × PadicSquareClass p) :=
  (absoluteGaloisTrivialTwoTorsionH1QuadraticPairMulEquiv ℚ_[p]).trans
    (padicSquareClassPairMulEquivQuadraticCharacters p h).symm

/-- Machine-readable local frontier: the continuous H¹ normalization and
pair decomposition are paid uniformly; scalar local Kummer and compatibility
with the explicit elliptic Kummer coordinates remain. -/
structure PadicKummerCohomologyBoundaryStatus where
  genericContinuousH1Paid : Bool
  quadraticCharacterPairSplitPaid : Bool
  explicitPadicSquareClassCarrierPaid : Bool
  explicitEllipticLocalKummerHomPaid : Bool
  scalarPadicKummerPaid : Bool
  explicitToCohomologicalCompatibilityPaid : Bool
  deriving DecidableEq, Repr

def padicKummerCohomologyBoundaryStatus :
    PadicKummerCohomologyBoundaryStatus :=
  ⟨true, true, true, true, false, false⟩

end Synthesis.Millennium.BSD
