import NSBControl.CyclicHelicalVectorTransform

namespace NSBControl
namespace SelfOrbitCommutatorCarrier

open CyclicHelicalVectorTransform

section

variable {V : Type*}

def pairWith
    (pairing : V → V → ℝ)
    (mixed value : Triad → V)
    (alpha beta : Triad) : ℝ :=
  pairing (mixed alpha) (value beta)

def spectatorRow
    (pair : Triad → Triad → ℝ)
    (beta : Triad)
    (items : List Triad) : ℝ :=
  (items.map (fun alpha => pair alpha beta)).sum

def outerRow
    (fibre : Mode → List Triad)
    (pair : Triad → Triad → ℝ)
    (beta : Triad) : ℝ :=
  spectatorRow pair beta (fibre beta.k)

def maskedOuterRow
    (mask : Triad → ℝ → ℝ)
    (fibre : Mode → List Triad)
    (pair : Triad → Triad → ℝ)
    (beta : Triad) : ℝ :=
  mask beta (outerRow fibre pair beta)

def orbitResidue
    (mask : Triad → ℝ → ℝ)
    (fibre : Mode → List Triad)
    (pair : Triad → Triad → ℝ)
    (beta : Triad) : ℝ :=
  maskedOuterRow mask fibre pair beta +
    maskedOuterRow mask fibre pair (pEnergyLeg beta) +
    maskedOuterRow mask fibre pair (qEnergyLeg beta)

def foldOrbit
    (mask : Triad → ℝ → ℝ)
    (fibre : Mode → List Triad)
    (pair : Triad → Triad → ℝ)
    (items : List Triad) : ℝ :=
  (items.map (orbitResidue mask fibre pair)).sum

theorem pair_transport
    (pairing : V → V → ℝ)
    (mixed selfNested commutatorCarrier : Triad → V)
    (hNested :
      ∀ beta, selfNested beta = commutatorCarrier beta)
    (alpha beta : Triad) :
    pairWith pairing mixed selfNested alpha beta =
      pairWith pairing mixed commutatorCarrier alpha beta := by
  simp [pairWith, hNested beta]

theorem spectatorRow_transport
    (pairing : V → V → ℝ)
    (mixed selfNested commutatorCarrier : Triad → V)
    (hNested :
      ∀ beta, selfNested beta = commutatorCarrier beta)
    (beta : Triad)
    (items : List Triad) :
    spectatorRow
        (pairWith pairing mixed selfNested) beta items =
      spectatorRow
        (pairWith pairing mixed commutatorCarrier) beta items := by
  simp [spectatorRow, pairWith, hNested beta]

theorem outerRow_transport
    (pairing : V → V → ℝ)
    (mixed selfNested commutatorCarrier : Triad → V)
    (fibre : Mode → List Triad)
    (hNested :
      ∀ beta, selfNested beta = commutatorCarrier beta)
    (beta : Triad) :
    outerRow fibre
        (pairWith pairing mixed selfNested) beta =
      outerRow fibre
        (pairWith pairing mixed commutatorCarrier) beta := by
  exact spectatorRow_transport
    pairing mixed selfNested commutatorCarrier
    hNested beta (fibre beta.k)

theorem maskedOuterRow_transport
    (pairing : V → V → ℝ)
    (mixed selfNested commutatorCarrier : Triad → V)
    (mask : Triad → ℝ → ℝ)
    (fibre : Mode → List Triad)
    (hNested :
      ∀ beta, selfNested beta = commutatorCarrier beta)
    (beta : Triad) :
    maskedOuterRow mask fibre
        (pairWith pairing mixed selfNested) beta =
      maskedOuterRow mask fibre
        (pairWith pairing mixed commutatorCarrier) beta := by
  unfold maskedOuterRow
  exact congrArg (mask beta)
    (outerRow_transport
      pairing mixed selfNested commutatorCarrier
      fibre hNested beta)

theorem orbitResidue_transport
    (pairing : V → V → ℝ)
    (mixed selfNested commutatorCarrier : Triad → V)
    (mask : Triad → ℝ → ℝ)
    (fibre : Mode → List Triad)
    (hNested :
      ∀ beta, selfNested beta = commutatorCarrier beta)
    (beta : Triad) :
    orbitResidue mask fibre
        (pairWith pairing mixed selfNested) beta =
      orbitResidue mask fibre
        (pairWith pairing mixed commutatorCarrier) beta := by
  unfold orbitResidue
  rw [
    maskedOuterRow_transport
      pairing mixed selfNested commutatorCarrier
      mask fibre hNested beta,
    maskedOuterRow_transport
      pairing mixed selfNested commutatorCarrier
      mask fibre hNested (pEnergyLeg beta),
    maskedOuterRow_transport
      pairing mixed selfNested commutatorCarrier
      mask fibre hNested (qEnergyLeg beta)
  ]

theorem completeSelfOrbit_transport
    (pairing : V → V → ℝ)
    (mixed selfNested commutatorCarrier : Triad → V)
    (mask : Triad → ℝ → ℝ)
    (fibre : Mode → List Triad)
    (items : List Triad)
    (hNested :
      ∀ beta, selfNested beta = commutatorCarrier beta) :
    foldOrbit mask fibre
        (pairWith pairing mixed selfNested) items =
      foldOrbit mask fibre
        (pairWith pairing mixed commutatorCarrier) items := by
  unfold foldOrbit
  apply List.sum_congr rfl
  intro beta hBeta
  exact orbitResidue_transport
    pairing mixed selfNested commutatorCarrier
    mask fibre hNested beta

end

end SelfOrbitCommutatorCarrier
end NSBControl
