import NSBControl.CyclicHelicalVectorTransform

namespace NSBControl
namespace SpectatorFibreLegTransport

open CyclicHelicalVectorTransform

section

variable
  (fibre : Mode → List Triad)
  (global : List Triad)

variable
  (fibreSound : ∀ {m τ}, τ ∈ fibre m → τ.k = m)
  (fibreComplete : ∀ {m τ}, τ ∈ global → τ.k = m → τ ∈ fibre m)
  (pLegClosed : ∀ {τ}, τ ∈ global → pEnergyLeg τ ∈ global)
  (qLegClosed : ∀ {τ}, τ ∈ global → qEnergyLeg τ ∈ global)

theorem pEnergyLeg_target_implies_matchingP
    {alpha beta : Triad}
    (h : pEnergyLeg alpha ∈ fibre beta.p) :
    alpha.p = beta.p := by
  have hk := fibreSound h
  simpa using hk

theorem qEnergyLeg_target_implies_matchingQ
    {alpha beta : Triad}
    (h : qEnergyLeg alpha ∈ fibre beta.q) :
    alpha.q = beta.q := by
  have hk := fibreSound h
  simpa using hk

theorem pEnergyLeg_target_from_matchingP
    {alpha beta : Triad}
    (hGlobal : alpha ∈ global)
    (hLabel : alpha.p = beta.p) :
    pEnergyLeg alpha ∈ fibre beta.p := by
  apply fibreComplete (pLegClosed hGlobal)
  simpa using hLabel

theorem qEnergyLeg_target_from_matchingQ
    {alpha beta : Triad}
    (hGlobal : alpha ∈ global)
    (hLabel : alpha.q = beta.q) :
    qEnergyLeg alpha ∈ fibre beta.q := by
  apply fibreComplete (qLegClosed hGlobal)
  simpa using hLabel

theorem pEnergyLeg_target_iff_matchingP
    {alpha beta : Triad}
    (hGlobal : alpha ∈ global) :
    pEnergyLeg alpha ∈ fibre beta.p ↔ alpha.p = beta.p := by
  constructor
  · exact pEnergyLeg_target_implies_matchingP fibre fibreSound
  · exact pEnergyLeg_target_from_matchingP
      fibre global fibreComplete pLegClosed hGlobal

theorem qEnergyLeg_target_iff_matchingQ
    {alpha beta : Triad}
    (hGlobal : alpha ∈ global) :
    qEnergyLeg alpha ∈ fibre beta.q ↔ alpha.q = beta.q := by
  constructor
  · exact qEnergyLeg_target_implies_matchingQ fibre fibreSound
  · exact qEnergyLeg_target_from_matchingQ
      fibre global fibreComplete qLegClosed hGlobal

end

end SpectatorFibreLegTransport
end NSBControl
