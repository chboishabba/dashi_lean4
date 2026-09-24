import Synthesis.MillenniumBSDEtaToActualLTransfer
import Synthesis.MillenniumBSDUniversalRankWeld

/-!
# CM worked-case boundary versus universal BSD

The special curve E : y^2 = x^3 - x now has a sharply reduced analytic
same-object boundary.  J1 and J2 are internal to J0, the prime values and
bad-prime coefficient data are paid, and all coefficient/Mellin/L-series
transport below the remaining Jacobi inputs is already compiled.

This file packages exactly the remaining CM analytic inputs and keeps that
worked-case theorem separate from the universal BSD rank owner.
-/

namespace Synthesis.Millennium.BSD

/-- Exact source-level CM analytic inputs still required by the Jacobi route:
the formal triple product and the two surviving CM-theta reconstruction laws. -/
structure CMWorkedCaseAnalyticInputs : Prop where
  tripleProduct : JacobiTripleProductFormal
  jacobiMultiplicative : JacobiArithmeticMultiplicativity
  oddPrimePowerRecurrence : JacobiOddPrimePowerRecurrence

/-- Package the two arithmetic laws into the existing reconstruction record. -/
def CMWorkedCaseAnalyticInputs.toJacobiCMData
    (h : CMWorkedCaseAnalyticInputs) :
    JacobiCMReconstructionData where
  multiplicative := h.jacobiMultiplicative
  oddPrimePowerRecurrence := h.oddPrimePowerRecurrence

/-- The three CM worked-case inputs compile to coefficientwise equality of the
eta kernel and the actual literal elliptic L-series coefficients. -/
theorem cmEtaEllipticCoefficientAgreement_of_workedCaseInputs
    (h : CMWorkedCaseAnalyticInputs) :
    EtaEllipticAllCoefficientAgreement := by
  rcases jacobiEta32Products_of_tripleProduct h.tripleProduct with
    ⟨hOdd, hEven⟩
  exact etaElliptic_allCoefficientAgreement_of_jacobiCMData
    hOdd hEven h.toJacobiCMData

/-- End-to-end same-object continuation theorem for the CM curve from the
three remaining analytic inputs. -/
theorem cmCompletedEllipticLContinuation_agrees_initial_of_workedCaseInputs
    (h : CMWorkedCaseAnalyticInputs)
    {s : ℂ} (hs : (5 : ℝ) / 2 < s.re) :
    cmCompletedEllipticLContinuation s =
      cmCompletedEllipticLInitial s :=
  cmCompletedEllipticLContinuation_agrees_initial_of_tripleProductOnlyCMData
    h.tripleProduct h.toJacobiCMData hs

/-- The functional equation is already paid independently of those remaining
same-object coefficient inputs. -/
theorem cmCompletedEllipticLContinuation_functionalEquation_paid
    (s : ℂ) :
    cmCompletedEllipticLContinuation (2 - s) =
      cmCompletedEllipticLContinuation s :=
  cmCompletedEllipticLContinuation_functional_equation s

/-- CM worked-case rank equality remains a one-curve statement even after the
analytic continuation is completely attached to the literal curve. -/
def CMWorkedCaseRankTarget
    (b : BSDBoundRankObservers) : Prop :=
  CMBSDRankWeld b.toRankObservers

/-- Universal BSD still restricts to the CM worked-case target, not conversely
without an explicit universal coverage/generalisation theorem. -/
theorem cmWorkedCaseRankTarget_of_universal
    (p : UniversalBSDRankProof) :
    CMWorkedCaseRankTarget p.bound :=
  cmBSDRankWeld_of_universal
    p.bound.toRankObservers p.rankWeld

/-- Machine-readable ledger separating the CM analytic worked case from the
Clay-facing universal rank theorem. -/
structure CMWorkedCaseMaxCutStatus where
  actualMathlibCurvePaid : Bool
  actualMathlibLSeriesPaid : Bool
  j1SpecializationPaid : Bool
  j2SpecializationPaid : Bool
  jacobiPrimeValuesPaid : Bool
  jacobiBadPrimePaid : Bool
  localToGlobalCoefficientCompilerPaid : Bool
  mellinToActualLCompilerPaid : Bool
  functionalEquationPaid : Bool
  j0TripleProductPaid : Bool
  jacobiMultiplicativityPaid : Bool
  jacobiPrimePowerRecurrencePaid : Bool
  cmRankWeldPaid : Bool
  universalCoveragePaid : Bool
  universalRankWeldPaid : Bool
  deriving DecidableEq, Repr

def cmWorkedCaseMaxCutStatus : CMWorkedCaseMaxCutStatus :=
  ⟨true, true, true, true, true, true, true, true, true,
    false, false, false, false, false, false⟩

end Synthesis.Millennium.BSD
