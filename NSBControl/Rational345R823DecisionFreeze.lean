import NSBControl.Rational345R823RealR749R760
import NSBControl.Rational345R830PhysicalPacketSegment

/-!
# R823 route-selection freeze

The literal real R694/R700 -> R748/R749 -> R760 same-object chain now feeds the
existing R823 semantic transport and R830/R831 negative-integral compiler.
Consequently the universal reserve shortcut has an explicit source-level
counterexample on the selected radius-four physical trajectory.

This owner deliberately separates mathematical/source status from kernel/CI
status.  The latter remains false until an exact-head Lean run is observed.
Nothing here promotes the result to the positive B proof; after certification
the surviving programme is B1 -> {B2,B3,B4} -> B7 -> B-continuation.
-/

namespace NSBControl
namespace Rational345R823DecisionFreeze

open Rational345R823RealR749R760

/-- Concrete source-level counterexample to the universal R823 integrated
reserve inequality, obtained from the literal real R760 carrier. -/
theorem r823UniversalReserveCounterexample :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve :=
  literalR760DecisionContradiction


/-- Original-multiplicity R760/R822 same-object source, not a selected
    reserve/demand pair chosen after seeing a negative integral. -/
noncomputable def literalPhysicalReserveSource :
    Rational345R831ReserveDecision.R823Cutoff4TouchedCarrierWeldData :=
  Rational345R823LiteralR760CellMaxCut.touchedCarrierWeld_of_literalR760Cell
    literalR760CellCarrier

/--
Stronger source-exact R823 endpoint: there is a nonzero real-time interval
of the actual radius-four Galerkin trajectory through the rational 3-4-5
seed, with reality, transversality and zero mean, on which the integrals
of the LITERAL R823 reserve and demand definitions violate reserve >= demand.

Unlike the historical existential summary, neither reserve nor demand is
an untracked real number: both are explicitly obtained from R760's original
signed physical cells and the R823 semantic provenance definitions.
-/
theorem literalPhysicalReserveIntegralCounterexample :
    ∃ (u : ℝ → Rational345RealRadius4.State) (T : ℝ),
      0 < T ∧
      u 0 = Rational345RealInitialState.u₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        Rational345R831ReserveDecision.IsR823PhysicalState (u t)) ∧
      ¬ ((∫ t in (0 : ℝ)..T,
            Rational345R823RealSemanticProvenance.r823DemandRate
              literalPhysicalReserveSource (u t)) ≤
          (∫ t in (0 : ℝ)..T,
            Rational345R823RealSemanticProvenance.r823ReserveRate
              literalPhysicalReserveSource (u t))) := by
  open Rational345R831ReserveDecision in
    obtain ⟨u, T, hT, hu0, huContinuous, hReality, hTransverse,
      hZero, hPointwiseNeg, hIntegratedNeg⟩ :=
        Rational345R830PhysicalPacketSegment.r830_physical_packet_negative_segment
  have hPhysical :
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        Rational345R831ReserveDecision.IsR823PhysicalState (u t) := by
    intro t ht
    exact ⟨hReality t ht, hTransverse t ht, hZero t ht⟩
  let semantic :=
    Rational345R823RealSemanticProvenance.realSemanticWeld_of_literalTouchedCarrier
      literalPhysicalReserveSource
  let pointwise :=
    Rational345R831ReserveDecision.physicalPointwiseWeld_of_terminalSemantic
      semantic
  let integrated :=
    Rational345R831ReserveDecision.integratedWeldOfPhysicalSegment
      pointwise u T (le_of_lt hT) huContinuous hPhysical
  have hNegative :
      Rational345R831ReserveDecision.selectedPayment u T < 0 := by
    simpa [Rational345R831ReserveDecision.selectedPayment]
      using hIntegratedNeg
  have hContradiction :
      ¬ integrated.integratedDemand ≤ integrated.integratedReserve :=
    Rational345R831ReserveDecision.welded_negative_payment_refutes_reserve
      integrated hNegative
  refine ⟨u, T, hT, hu0, hPhysical, ?_⟩
  change ¬ ((∫ t in (0 : ℝ)..T,
      Rational345R823RealSemanticProvenance.r823DemandRate
        literalPhysicalReserveSource (u t)) ≤
    (∫ t in (0 : ℝ)..T,
      Rational345R823RealSemanticProvenance.r823ReserveRate
        literalPhysicalReserveSource (u t))) at hContradiction
  exact hContradiction

/-- The source theorem chain reaches the route-selection contradiction. -/
def r823DecisionSourceClosed : Bool := true

/-- Exact-head kernel certification is intentionally tracked independently. -/
def r823DecisionKernelCertified : Bool := false

/-- R823 is an auxiliary route-selection shortcut, not the positive B theorem. -/
def r823DecisionIsNotBContinuation : Bool := true

end Rational345R823DecisionFreeze
end NSBControl
