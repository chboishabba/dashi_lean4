import NSBControl.Rational345R831ReserveDecision
import NSBControl.Rational345R830PhysicalSegmentStrong

/-!
# R831 physical-domain reserve weld

Agda R853/R823 only asserts its pointwise identities on a live physical packet.
The earlier Lean mirror asked for those identities on every ambient radius-four
state, which is stronger than the decision experiment needs.

R830 now supplies a nonzero trajectory segment satisfying Fourier reality and
transversality at every time.  Therefore the exact R831 semantic leaf can be
cut to the physical state domain traversed by that segment.
-/

open Set

namespace NSBControl
namespace Rational345R831ReserveDecision

open Rational345RealRadius4
open Rational345Round71RealityField
open Rational345R830PhysicalSegmentStrong

/-- The two linear physical constraints carried by the R830 trajectory. -/
def IsR823PhysicalState (x : State) : Prop :=
  realityTransform x = x ∧
    ∀ k : Mode, bilinearDot (kComplex k) (x k) = 0

/-- Exact R823 pointwise reserve/demand identity, required only on physical
states.  Continuity remains global because it is a cheap finite-polynomial
property and is what the interval-integral compiler consumes. -/
structure R823PhysicalPointwiseWeld where
  reserveRate : State → ℝ
  demandRate : State → ℝ
  selectedRate_eq_reserve_sub_demand :
    ∀ x, IsR823PhysicalState x →
      selectedRate x = reserveRate x - demandRate x
  reserveRate_continuous : Continuous reserveRate
  demandRate_continuous : Continuous demandRate

/-- Integrate a pointwise R823 identity along one physical trajectory segment. -/
def integratedWeldOfPhysicalSegment
    (weld : R823PhysicalPointwiseWeld)
    (u : ℝ → State) (T : ℝ)
    (hT : 0 ≤ T)
    (hu : ContinuousOn u (Icc (0 : ℝ) T))
    (hphysical : ∀ t ∈ Icc (0 : ℝ) T, IsR823PhysicalState (u t)) :
    R823IntegratedWeld u T := by
  let reserve : ℝ := ∫ t in (0 : ℝ)..T, weld.reserveRate (u t)
  let demand : ℝ := ∫ t in (0 : ℝ)..T, weld.demandRate (u t)
  refine
    { integratedReserve := reserve
      integratedDemand := demand
      selectedPayment_eq_reserve_sub_demand := ?_ }

  have hreserveCont :
      ContinuousOn (fun t => weld.reserveRate (u t)) (Icc (0 : ℝ) T) :=
    weld.reserveRate_continuous.continuousOn.comp hu (fun _ ht => ht)
  have hdemandCont :
      ContinuousOn (fun t => weld.demandRate (u t)) (Icc (0 : ℝ) T) :=
    weld.demandRate_continuous.continuousOn.comp hu (fun _ ht => ht)
  have hreserveInt := hreserveCont.intervalIntegrable
  have hdemandInt := hdemandCont.intervalIntegrable

  unfold selectedPayment
  change
    (∫ t in (0 : ℝ)..T, selectedRate (u t)) = reserve - demand
  calc
    (∫ t in (0 : ℝ)..T, selectedRate (u t))
        = ∫ t in (0 : ℝ)..T,
            (weld.reserveRate (u t) - weld.demandRate (u t)) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have htIcc : t ∈ Icc (0 : ℝ) T := by
            simpa [uIcc_of_le hT] using ht
          exact weld.selectedRate_eq_reserve_sub_demand
            (u t) (hphysical t htIcc)
    _ = reserve - demand := by
          dsimp [reserve, demand]
          exact intervalIntegral.integral_sub hreserveInt hdemandInt

/-- Max-cut terminal decision theorem: no ambient-state R853/R823 identity is
needed.  A reserve/demand identity on the actual physical state domain already
turns the R830 physical negative segment into a counterexample to the reserve
inequality. -/
theorem r830_physical_segment_refutes_r823_reserve
    (weld : R823PhysicalPointwiseWeld) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve := by
  obtain ⟨u, T, hT, hu0, hu, hReality, hTransverse, hneg, hIntegral⟩ :=
    r830_physical_negative_segment_continuous

  have hphysical :
      ∀ t ∈ Icc (0 : ℝ) T, IsR823PhysicalState (u t) := by
    intro t ht
    exact ⟨hReality t ht, hTransverse t ht⟩

  let integrated :=
    integratedWeldOfPhysicalSegment weld u T (le_of_lt hT) hu hphysical

  refine ⟨integrated.integratedReserve, integrated.integratedDemand, ?_⟩
  apply welded_negative_payment_refutes_reserve integrated
  simpa [selectedPayment] using hIntegral

/-- The old all-ambient-state weld is stronger than necessary for R831. -/
def r831DecisionReducedToPhysicalPointwiseWeld : Bool := true

/-- Exact remaining decision leaf: construct the R823 reserve/demand rates on
the real physical state carrier and prove their pointwise identity there. -/
def r823PhysicalPointwiseWeldClosed : Bool := false

end Rational345R831ReserveDecision
end NSBControl
