import NSBControl.Rational345BPClosed
import NSBControl.Rational345Round71TrajectoryPhysical

/-!
# R830 physical negative trajectory segment

R830 already supplies a local Galerkin trajectory that remains in the B_P
bootstrap ball and has strictly negative selected rate pointwise on the
residence-aware interval.  Round71 trajectory invariance supplies independent
positive radii for Fourier reality and divergence freedom.

Taking the positive minimum of those three time scales produces one actual
physical trajectory segment on which the selected rate is pointwise negative,
so its integral is strictly negative as well.
-/

open Set

namespace NSBControl
namespace Rational345R830PhysicalSegment

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345R830ResidenceInterval
open Rational345R830PointwiseNegative
open Rational345BPClosed
open Rational345Round71RealityField
open Rational345Round71TrajectoryPhysical
open Rational345R830DecisionCompiler

/-- Intersect the quantitative R830 interval with the two physical-invariant
radii, leaving slack by taking half of each invariant radius. -/
def physicalUsableTime (ε δ ρReality ρTransverse : ℝ) : ℝ :=
  min (residenceUsableTime ε δ)
    (min (ρReality / 2) (ρTransverse / 2))

theorem physicalUsableTime_pos
    {ε δ ρReality ρTransverse : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hR : 0 < ρReality) (hD : 0 < ρTransverse) :
    0 < physicalUsableTime ε δ ρReality ρTransverse := by
  rw [physicalUsableTime]
  exact lt_min (residenceUsableTime_pos hε hδ)
    (lt_min (by linarith) (by linarith))

theorem physicalUsableTime_le_residence
    (ε δ ρReality ρTransverse : ℝ) :
    physicalUsableTime ε δ ρReality ρTransverse ≤
      residenceUsableTime ε δ :=
  min_le_left _ _

theorem physicalUsableTime_lt_reality
    {ε δ ρReality ρTransverse : ℝ}
    (hR : 0 < ρReality) :
    physicalUsableTime ε δ ρReality ρTransverse < ρReality := by
  calc
    physicalUsableTime ε δ ρReality ρTransverse
        ≤ ρReality / 2 :=
          (min_le_right _ _).trans (min_le_left _ _)
    _ < ρReality := by linarith

theorem physicalUsableTime_lt_transverse
    {ε δ ρReality ρTransverse : ℝ}
    (hD : 0 < ρTransverse) :
    physicalUsableTime ε δ ρReality ρTransverse < ρTransverse := by
  calc
    physicalUsableTime ε δ ρReality ρTransverse
        ≤ ρTransverse / 2 :=
          (min_le_right _ _).trans (min_le_right _ _)
    _ < ρTransverse := by linarith

/-- Main physical R830 witness.  No R823 semantics are used here: this is only
the actual finite Galerkin trajectory, its two physical linear constraints,
and the already-certified selected-rate sign. -/
theorem r830_physical_negative_segment :
    ∃ (u : ℝ → State) (T : ℝ),
      0 < T ∧
      u 0 = u₀ ∧
      (∀ t ∈ Icc (0 : ℝ) T, realityTransform (u t) = u t) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        ∀ k : Mode, bilinearDot (kComplex k) (u t k) = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) T, selectedRate (u t) < 0) ∧
      (∫ t in (0 : ℝ)..T, selectedRate (u t)) < 0 := by
  obtain ⟨u, ε, δ, hε, hδ, hu0, hderiv, hres, hnegResidence⟩ :=
    r830_pointwise_negative_witness
  obtain ⟨ρR, hρR, hReality⟩ :=
    trajectory_reality_radius u hε hu0 hderiv
  obtain ⟨ρD, hρD, hTransverse⟩ :=
    trajectory_transverse_radius u hε hu0 hderiv

  let T := physicalUsableTime ε δ ρR ρD
  have hT : 0 < T := physicalUsableTime_pos hε hδ hρR hρD
  have hTres : T ≤ residenceUsableTime ε δ :=
    physicalUsableTime_le_residence ε δ ρR ρD
  have hTR : T < ρR := physicalUsableTime_lt_reality hρR
  have hTD : T < ρD := physicalUsableTime_lt_transverse hρD

  have hRealityT : ∀ t ∈ Icc (0 : ℝ) T,
      realityTransform (u t) = u t := by
    intro t ht
    apply hReality t
    rw [abs_of_nonneg ht.1]
    exact ht.2.trans_lt hTR

  have hTransverseT : ∀ t ∈ Icc (0 : ℝ) T,
      ∀ k : Mode, bilinearDot (kComplex k) (u t k) = 0 := by
    intro t ht
    apply hTransverse t
    rw [abs_of_nonneg ht.1]
    exact ht.2.trans_lt hTD

  have hnegT : ∀ t ∈ Icc (0 : ℝ) T,
      selectedRate (u t) < 0 := by
    intro t ht
    exact hnegResidence t ⟨ht.1, ht.2.trans hTres⟩

  have hcont : ContinuousOn (fun t => selectedRate (u t))
      (Icc (0 : ℝ) T) := by
    have hTpic : T < ε :=
      hTres.trans_lt (residenceUsableTime_lt_eps hε)
    have huCont : ContinuousOn u (Icc (0 : ℝ) T) := by
      intro t ht
      have htPic : t ∈ Ioo (-ε) ε := by
        constructor
        · linarith [ht.1]
        · exact ht.2.trans_lt hTpic
      exact (hderiv t htPic).continuousAt.continuousWithinAt
    exact selectedRate_continuous.continuousOn.comp huCont (fun _ ht => ht)

  have hIntegral :
      (∫ t in (0 : ℝ)..T, selectedRate (u t)) < 0 := by
    exact negative_integral_on_subinterval
      u selectedRate hT hTres hcont hnegResidence

  exact ⟨u, T, hT, hu0, hRealityT, hTransverseT, hnegT, hIntegral⟩

/-- Reality and divergence-free physicality no longer block the R823 decision
experiment. -/
def r830PhysicalLinearConstraintsClosed : Bool := true

end Rational345R830PhysicalSegment
end NSBControl
