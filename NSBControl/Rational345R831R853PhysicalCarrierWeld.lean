import NSBControl.Rational345R831PhysicalWeld

/-!
# R831 physical-only Round853 carrier weld

The preferred decision route is Round853 -> R823, but the Agda theorem lives on
live physical packets.  The ambient Lean `R853RealCarrierWeld` asks for scalar
same-object identities on every radius-four state, which is stronger than R830
needs.

This owner cuts the interface to the exact state domain traversed by the R830
negative segment: Fourier reality, divergence freedom, and zero mean.  The
normal-form and reserve-minus-demand identities are required only there.  The
terminal integration compiler then reuses `R823PhysicalPointwiseWeld`.
-/

namespace NSBControl
namespace Rational345R831ReserveDecision

open Rational345RealRadius4

/-- Physical-domain version of the Round853 + R823 carrier weld. -/
structure R853PhysicalCarrierWeld where
  coherent : State → ℝ
  production : State → ℝ
  dissipation : State → ℝ
  completePhysicalRate : State → ℝ
  reserveRate : State → ℝ
  demandRate : State → ℝ

  coherent_sameObject :
    ∀ x, IsR823PhysicalState x → coherent x = globalCoherentWork x
  production_sameObject :
    ∀ x, IsR823PhysicalState x → production x = criticalProduction x
  dissipation_sameObject :
    ∀ x, IsR823PhysicalState x → dissipation x = criticalDissipation x

  r853DecisionNormalForm :
    ∀ x, IsR823PhysicalState x →
      completePhysicalRate x =
        6 * (12 * coherent x - production x + dissipation x)

  r823ReserveMinusDemand :
    ∀ x, IsR823PhysicalState x →
      completePhysicalRate x = reserveRate x - demandRate x

  reserveRate_continuous : Continuous reserveRate
  demandRate_continuous : Continuous demandRate

/-- On the physical packet domain, Round853 identifies the actual complete
packet rate with the public Lean selected rate. -/
theorem r853_selectedRate_sameObject_physical
    (weld : R853PhysicalCarrierWeld)
    (x : State) (hx : IsR823PhysicalState x) :
    selectedRate x = weld.completePhysicalRate x := by
  rw [selectedRate_public_definition]
  rw [← weld.coherent_sameObject x hx,
      ← weld.production_sameObject x hx,
      ← weld.dissipation_sameObject x hx]
  exact (weld.r853DecisionNormalForm x hx).symm

/-- Physical Round853 + R823 data constructs exactly the pointwise weld needed
along the R830 packet, with no ambient-state strengthening. -/
def r823PhysicalPointwiseWeld_of_r853Physical
    (weld : R853PhysicalCarrierWeld) : R823PhysicalPointwiseWeld where
  reserveRate := weld.reserveRate
  demandRate := weld.demandRate
  selectedRate_eq_reserve_sub_demand := by
    intro x hx
    exact (r853_selectedRate_sameObject_physical weld x hx).trans
      (weld.r823ReserveMinusDemand x hx)
  reserveRate_continuous := weld.reserveRate_continuous
  demandRate_continuous := weld.demandRate_continuous

/-- Preferred terminal physical max-cut: the actual R853/R823 carrier theorem
on live physical states is sufficient for the negative R830 packet to refute
the reserve inequality. -/
theorem r830_refutes_r823_reserve_of_r853Physical
    (weld : R853PhysicalCarrierWeld) :
    ∃ reserve demand : ℝ, ¬ demand ≤ reserve :=
  r830_physical_segment_refutes_r823_reserve
    (r823PhysicalPointwiseWeld_of_r853Physical weld)

/-- The ambient-state Round853 assumption has been eliminated. -/
def r831R853ReducedToPhysicalCarrier : Bool := true

/-- Honest final decision-lane leaf: identify the actual Agda R853/R823 live
packet scalars with the real Lean radius-four operators on physical states. -/
def r853PhysicalTrajectoryCarrierWeldClosed : Bool := false

end Rational345R831ReserveDecision
end NSBControl
