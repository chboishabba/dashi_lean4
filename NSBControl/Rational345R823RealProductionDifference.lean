import Mathlib.Tactic
import NSBControl.Rational345R823RealProductionIncidence
import NSBControl.Rational345Round71NonlinearConservation
import NSBControl.Rational345R831PhysicalWeld

/-!
# Real R748 paired two-difference production carrier

This is the real-radius-four port of the R748 production side used by R749.
The carrier is the complete finite physical triad cube with inactive incidences
zero-masked.  The exact local three-leg paired-power cancellation is proved
from the already-ported real energy cell, Fourier reality, and transversality.
No estimate is introduced.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345R823RealProductionDifference

open Rational345RealRadius4
open Rational345Round71PhysicalCarrier
open Rational345Round71RealityField
open Rational345Round71NonlinearConservation
open Rational345R823RealProductionIncidence
open Rational345R831ReserveDecision

classical

/-- Storage order is `(output, first input, second input)`. -/
abbrev R760Incidence := Mode × (Mode × Mode)

def incK (β : R760Incidence) : Mode := β.1
def incP (β : R760Incidence) : Mode := β.2.1
def incQ (β : R760Incidence) : Mode := β.2.2

def physicalTriadActive (β : R760Incidence) : Prop :=
  nonzeroMode (incP β) ∧ nonzeroMode (incQ β) ∧
    nonzeroMode (incK β) ∧ Resonates (incP β) (incQ β) (incK β)

instance (β : R760Incidence) : Decidable (physicalTriadActive β) := inferInstance

/-- Physical p/q swap. -/
def swapIncidence (β : R760Incidence) : R760Incidence :=
  (incK β, (incQ β, incP β))

/-- The two nontrivial energy legs used in R748. -/
def pEnergyLeg (β : R760Incidence) : R760Incidence :=
  (incP β, (incK β, negateMode (incQ β)))

def qEnergyLeg (β : R760Incidence) : R760Incidence :=
  (incQ β, (incK β, negateMode (incP β)))

@[simp] theorem swapIncidence_involutive (β : R760Incidence) :
    swapIncidence (swapIncidence β) = β := by
  rcases β with ⟨k, p, q⟩
  rfl

@[simp] theorem pEnergyLeg_involutive (β : R760Incidence) :
    pEnergyLeg (pEnergyLeg β) = β := by
  rcases β with ⟨k, p, q⟩
  simp [pEnergyLeg, incK, incP, incQ]

@[simp] theorem qEnergyLeg_involutive (β : R760Incidence) :
    qEnergyLeg (qEnergyLeg β) = β := by
  rcases β with ⟨k, p, q⟩
  simp [qEnergyLeg, incK, incP, incQ]

def swapEquiv : R760Incidence ≃ R760Incidence where
  toFun := swapIncidence
  invFun := swapIncidence
  left_inv := swapIncidence_involutive
  right_inv := swapIncidence_involutive

def pEnergyLegEquiv : R760Incidence ≃ R760Incidence where
  toFun := pEnergyLeg
  invFun := pEnergyLeg
  left_inv := pEnergyLeg_involutive
  right_inv := pEnergyLeg_involutive

def qEnergyLegEquiv : R760Incidence ≃ R760Incidence where
  toFun := qEnergyLeg
  invFun := qEnergyLeg
  left_inv := qEnergyLeg_involutive
  right_inv := qEnergyLeg_involutive

theorem resonates_swap_iff (p q k : Mode) :
    Resonates q p k ↔ Resonates p q k := by
  constructor <;> intro h j
  · have hj := h j
    omega
  · have hj := h j
    omega

theorem resonates_pEnergyLeg_iff (β : R760Incidence) :
    Resonates (incP (pEnergyLeg β)) (incQ (pEnergyLeg β))
        (incK (pEnergyLeg β)) ↔
      Resonates (incP β) (incQ β) (incK β) := by
  rcases β with ⟨k, p, q⟩
  simp only [pEnergyLeg, incK, incP, incQ, kInt_negate]
  constructor <;> intro h j
  · have hj := h j
    omega
  · have hj := h j
    omega

theorem resonates_qEnergyLeg_iff (β : R760Incidence) :
    Resonates (incP (qEnergyLeg β)) (incQ (qEnergyLeg β))
        (incK (qEnergyLeg β)) ↔
      Resonates (incP β) (incQ β) (incK β) := by
  rcases β with ⟨k, p, q⟩
  simp only [qEnergyLeg, incK, incP, incQ, kInt_negate]
  constructor <;> intro h j
  · have hj := h j
    omega
  · have hj := h j
    omega

@[simp] theorem physicalTriadActive_swap_iff (β : R760Incidence) :
    physicalTriadActive (swapIncidence β) ↔ physicalTriadActive β := by
  rcases β with ⟨k, p, q⟩
  simp only [physicalTriadActive, swapIncidence, incK, incP, incQ]
  rw [resonates_swap_iff]
  aesop

@[simp] theorem physicalTriadActive_pEnergyLeg_iff (β : R760Incidence) :
    physicalTriadActive (pEnergyLeg β) ↔ physicalTriadActive β := by
  rcases β with ⟨k, p, q⟩
  simp only [physicalTriadActive, pEnergyLeg, incK, incP, incQ]
  have hq : nonzeroMode (negateMode q) ↔ nonzeroMode q := by
    simpa [nonzeroMode] using not_congr (isZeroMode_negate_iff q)
  rw [hq]
  have hr := resonates_pEnergyLeg_iff (k, (p, q))
  simp only [pEnergyLeg, incK, incP, incQ] at hr
  rw [hr]
  aesop

@[simp] theorem physicalTriadActive_qEnergyLeg_iff (β : R760Incidence) :
    physicalTriadActive (qEnergyLeg β) ↔ physicalTriadActive β := by
  rcases β with ⟨k, p, q⟩
  simp only [physicalTriadActive, qEnergyLeg, incK, incP, incQ]
  have hp : nonzeroMode (negateMode p) ↔ nonzeroMode p := by
    simpa [nonzeroMode] using not_congr (isZeroMode_negate_iff p)
  rw [hp]
  have hr := resonates_qEnergyLeg_iff (k, (p, q))
  simp only [qEnergyLeg, incK, incP, incQ] at hr
  rw [hr]
  aesop

/-- Pointwise Fourier reality extracted from the physical-state predicate. -/
theorem physical_reality
    (u : State) (hu : IsR823PhysicalState u) (k : Mode) :
    u (negateMode k) = vecConj (u k) := by
  have h := congrFun hu.1 (negateMode k)
  simpa [realityTransform] using h.symm

/-- The real R744 ordered power is exactly the real energy cell. -/
theorem orderedPower_eq_energyCell
    (u : State) (hdiv : ∀ m, bilinearDot (kComplex m) (u m) = 0)
    (p q k : Mode) :
    orderedPower u p q k = energyCell u p q k := by
  unfold orderedPower pairingRealLinear
  change
    (hermitianDot (u k) (projectedOrderedBilinear u u p q k)).re =
      energyCell u p q k
  exact projectedOrdered_power_eq_energyCell u hdiv p q k

/-- Full simultaneous mode negation leaves the real energy scalar unchanged on
Fourier-real states. -/
theorem energyCell_negate_all
    (u : State)
    (hreality : ∀ m, u (negateMode m) = vecConj (u m))
    (p q k : Mode) :
    energyCell u (negateMode p) (negateMode q) (negateMode k) =
      energyCell u p q k := by
  by_cases hk : isZeroMode k
  · have hkn : isZeroMode (negateMode k) := (isZeroMode_negate_iff k).2 hk
    simp [energyCell, hk, hkn]
  · have hkn : ¬ isZeroMode (negateMode k) := by simpa using hk
    by_cases hres : Resonates p q k
    · have hresn : Resonates (negateMode p) (negateMode q) (negateMode k) :=
        (resonates_negate_iff p q k).2 hres
      rw [energyCell, energyCell]
      simp only [hk, hkn, hres, hresn, if_false, if_true]
      rw [hreality p, hreality q, hreality k, kComplex_negate]
      simp [bilinearDot, hermitianDot, vecConj, map_sum]
      ring
    · have hresn : ¬ Resonates (negateMode p) (negateMode q) (negateMode k) := by
        exact fun h => hres ((resonates_negate_iff p q k).1 h)
      simp [energyCell, hk, hkn, hres, hresn]

/-- Ordered-pair real power at one physical triad incidence. -/
def orderedPairPower (u : State) (β : R760Incidence) : ℝ :=
  orderedPower u (incP β) (incQ β) (incK β) +
    orderedPower u (incQ β) (incP β) (incK β)

/-- Exact real counterpart of R98/R748 three-leg physical energy cancellation. -/
theorem threeLegOrderedPairPowerZero
    (u : State) (hu : IsR823PhysicalState u)
    (β : R760Incidence) (hβ : physicalTriadActive β) :
    orderedPairPower u β +
      orderedPairPower u (pEnergyLeg β) +
      orderedPairPower u (qEnergyLeg β) = 0 := by
  rcases β with ⟨k, p, q⟩
  rcases hβ with ⟨hp, hq, hk, hres⟩
  let hreality := physical_reality u hu
  let hdiv := hu.2.1
  simp only [orderedPairPower, pEnergyLeg, qEnergyLeg, incK, incP, incQ]
  simp_rw [orderedPower_eq_energyCell u hdiv]
  have hCE :
      energyCell u k (negateMode p) q =
        - energyCell u k (negateMode q) p := by
    simpa using
      (energyCell_pair_cancel u hreality hdiv k (negateMode q) p)
  have hBpair :
      energyCell u q (negateMode k) (negateMode p) =
        - energyCell u q p k :=
    energyCell_pair_cancel u hreality hdiv q p k
  have hDneg :
      energyCell u q (negateMode k) (negateMode p) =
        energyCell u (negateMode q) k p := by
    simpa using (energyCell_negate_all u hreality (negateMode q) k p)
  have hDB :
      energyCell u (negateMode q) k p = - energyCell u q p k :=
    hDneg.symm.trans hBpair
  have hApair :
      energyCell u p (negateMode k) (negateMode q) =
        - energyCell u p q k :=
    energyCell_pair_cancel u hreality hdiv p q k
  have hFneg :
      energyCell u p (negateMode k) (negateMode q) =
        energyCell u (negateMode p) k q := by
    simpa using (energyCell_negate_all u hreality (negateMode p) k q)
  have hFA :
      energyCell u (negateMode p) k q = - energyCell u p q k :=
    hFneg.symm.trans hApair
  rw [hCE, hDB, hFA]
  ring

/-- Zero-safe dyadic weight. -/
def selectedDyadicWeight (k : Mode) : ℝ :=
  if isZeroMode k then 0 else criticalWeight k

/-- Physical zero-masked R744 ordered incidence in the common R760 address. -/
def physicalProductionCell (u : State) (β : R760Incidence) : ℝ :=
  if physicalTriadActive β then
    criticalWeight (incK β) *
      orderedPower u (incP β) (incQ β) (incK β)
  else 0

/-- Swap-paired weighted production cell. -/
def pairedWeightedCell (u : State) (β : R760Incidence) : ℝ :=
  if physicalTriadActive β then
    selectedDyadicWeight (incK β) * orderedPairPower u β
  else 0

/-- Three-energy-leg paired production orbit. -/
def pairedProductionOrbitCell (u : State) (β : R760Incidence) : ℝ :=
  pairedWeightedCell u β +
    pairedWeightedCell u (pEnergyLeg β) +
    pairedWeightedCell u (qEnergyLeg β)

/-- Literal R748 two-difference local form. -/
def pairedTwoDifferenceCell (u : State) (β : R760Incidence) : ℝ :=
  if physicalTriadActive β then
    (selectedDyadicWeight (incK β) - selectedDyadicWeight (incQ β)) *
        orderedPairPower u β +
      (selectedDyadicWeight (incP β) - selectedDyadicWeight (incQ β)) *
        orderedPairPower u (pEnergyLeg β)
  else 0

/-- R748 pointwise rewrite using the exact three-leg cancellation. -/
theorem pairedProductionOrbit_is_twoDifference
    (u : State) (hu : IsR823PhysicalState u) (β : R760Incidence) :
    pairedProductionOrbitCell u β = pairedTwoDifferenceCell u β := by
  by_cases hβ : physicalTriadActive β
  · have hpβ : physicalTriadActive (pEnergyLeg β) :=
      (physicalTriadActive_pEnergyLeg_iff β).2 hβ
    have hqβ : physicalTriadActive (qEnergyLeg β) :=
      (physicalTriadActive_qEnergyLeg_iff β).2 hβ
    have hzero := threeLegOrderedPairPowerZero u hu β hβ
    rcases hβ with ⟨hp, hq, hk, hres⟩
    simp [pairedProductionOrbitCell, pairedWeightedCell,
      pairedTwoDifferenceCell, hβ, hpβ, hqβ,
      selectedDyadicWeight, pEnergyLeg, qEnergyLeg, incK, incP, incQ,
      hk, hp, hq] at hzero ⊢
    ring_nf at hzero ⊢
    linarith
  · have hpβ : ¬ physicalTriadActive (pEnergyLeg β) := by
      intro h
      exact hβ ((physicalTriadActive_pEnergyLeg_iff β).1 h)
    have hqβ : ¬ physicalTriadActive (qEnergyLeg β) := by
      intro h
      exact hβ ((physicalTriadActive_qEnergyLeg_iff β).1 h)
    simp [pairedProductionOrbitCell, pairedWeightedCell,
      pairedTwoDifferenceCell, hβ, hpβ, hqβ]

/-- Pairing one physical production cell with its p/q swap gives the weighted
ordered-pair cell. -/
theorem pairedWeightedCell_eq_cell_add_swap
    (u : State) (β : R760Incidence) :
    pairedWeightedCell u β =
      physicalProductionCell u β + physicalProductionCell u (swapIncidence β) := by
  by_cases hβ : physicalTriadActive β
  · have hs : physicalTriadActive (swapIncidence β) :=
      (physicalTriadActive_swap_iff β).2 hβ
    rcases hβ with ⟨hp, hq, hk, hres⟩
    simp [pairedWeightedCell, physicalProductionCell, orderedPairPower,
      selectedDyadicWeight, hβ, hs, hk, swapIncidence, incK, incP, incQ]
    ring
  · have hs : ¬ physicalTriadActive (swapIncidence β) := by
      intro h
      exact hβ ((physicalTriadActive_swap_iff β).1 h)
    simp [pairedWeightedCell, physicalProductionCell, hβ, hs]

/-- Common-address physical production fold equals the existing R744 physical
incidence total. -/
theorem physicalProductionCompleteFold_eq_existing (u : State) :
    (∑ β : R760Incidence, physicalProductionCell u β) =
      physicalWeightedProductionIncidenceTotal u := by
  simp only [R760Incidence, Fintype.sum_prod_type]
  unfold physicalProductionCell physicalTriadActive
    physicalWeightedProductionIncidenceTotal physicalWeightedProductionIncidence
  rfl

/-- Complete paired weighted fold is exactly critical production on a physical
zero-mean state. -/
theorem pairedWeightedCompleteFold_eq_criticalProduction
    (u : State) (hu : IsR823PhysicalState u) :
    (∑ β : R760Incidence, pairedWeightedCell u β) = criticalProduction u := by
  have hsplit :
      (∑ β : R760Incidence, pairedWeightedCell u β) =
        (∑ β : R760Incidence, physicalProductionCell u β) +
        (∑ β : R760Incidence, physicalProductionCell u (swapIncidence β)) := by
    simp_rw [pairedWeightedCell_eq_cell_add_swap]
    exact Finset.sum_add_distrib
  have hswap :
      (∑ β : R760Incidence, physicalProductionCell u (swapIncidence β)) =
        ∑ β : R760Incidence, physicalProductionCell u β :=
    Equiv.sum_comp swapEquiv (physicalProductionCell u)
  rw [hsplit, hswap, physicalProductionCompleteFold_eq_existing]
  rw [← weightedIncidence_eq_physicalWeightedIncidence u hu.2.2]
  rw [criticalProduction_eq_twice_weightedIncidence]
  ring

/-- Complete paired production orbit is three copies of critical production. -/
theorem pairedProductionOrbitCompleteFold_eq_threeProduction
    (u : State) (hu : IsR823PhysicalState u) :
    (∑ β : R760Incidence, pairedProductionOrbitCell u β) =
      3 * criticalProduction u := by
  unfold pairedProductionOrbitCell
  simp_rw [Finset.sum_add_distrib]
  have hp :
      (∑ β : R760Incidence, pairedWeightedCell u (pEnergyLeg β)) =
        ∑ β : R760Incidence, pairedWeightedCell u β :=
    Equiv.sum_comp pEnergyLegEquiv (pairedWeightedCell u)
  have hq :
      (∑ β : R760Incidence, pairedWeightedCell u (qEnergyLeg β)) =
        ∑ β : R760Incidence, pairedWeightedCell u β :=
    Equiv.sum_comp qEnergyLegEquiv (pairedWeightedCell u)
  rw [hp, hq, pairedWeightedCompleteFold_eq_criticalProduction u hu]
  ring

/-- Complete literal R748 two-difference fold. -/
def pairedTwoDifferenceCompleteFold (u : State) : ℝ :=
  ∑ β : R760Incidence, pairedTwoDifferenceCell u β

/-- D2 production theorem: complete two-difference fold is exactly 3P. -/
theorem pairedTwoDifferenceCompleteFold_eq_threeProduction
    (u : State) (hu : IsR823PhysicalState u) :
    pairedTwoDifferenceCompleteFold u = 3 * criticalProduction u := by
  unfold pairedTwoDifferenceCompleteFold
  calc
    (∑ β : R760Incidence, pairedTwoDifferenceCell u β) =
        ∑ β : R760Incidence, pairedProductionOrbitCell u β := by
      apply Fintype.sum_congr
      intro β
      exact (pairedProductionOrbit_is_twoDifference u hu β).symm
    _ = 3 * criticalProduction u :=
      pairedProductionOrbitCompleteFold_eq_threeProduction u hu

/-- Real R748 production side is represented without estimates. -/
def r823RealR748PairedTwoDifferenceClosed : Bool := true

end Rational345R823RealProductionDifference
end NSBControl
