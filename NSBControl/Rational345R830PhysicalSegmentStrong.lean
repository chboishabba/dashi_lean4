import NSBControl.Rational345R830PhysicalSegment

/-!
# R830 physical negative segment with continuity retained

`r830_physical_negative_segment` is intentionally a compact public witness and
drops the local Picard continuity proof after using it to establish the
negative integral.  R831's physical-domain pointwise-to-integrated weld needs
that continuity again, so this owner keeps it in the exported witness rather
than adding a new semantic assumption downstream.
-/

open Set

namespace NSBControl
namespace Rational345R830PhysicalSegmentStrong

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345R830ResidenceInterval
open Rational345R830PointwiseNegative
open Rational345BPClosed
open Rational345Round71RealityField
open Rational345Round71TrajectoryPhysical
open Rational345R830DecisionCompiler
open Rational345R830PhysicalSegment

/-- Same physical R830 segment, with state continuity retained for downstream
integration of any continuous pointwise observable. -/
theorem r830_physical_negative_segment_continuous :
    ∃ (u : ℝ → State) (T : ℝ),
      0 < T ∧
      u 0 = u₀ ∧
      ContinuousOn u (Icc (0 : ℝ) T) ∧
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
  have hTpic : T < ε :=
    hTres.trans_lt (residenceUsableTime_lt_eps hε)

  have huCont : ContinuousOn u (Icc (0 : ℝ) T) := by
    intro t ht
    have htPic : t ∈ Ioo (-ε) ε := by
      constructor
      · linarith [ht.1]
      · exact ht.2.trans_lt hTpic
    exact (hderiv t htPic).continuousAt.continuousWithinAt

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

  have hcontRate : ContinuousOn (fun t => selectedRate (u t))
      (Icc (0 : ℝ) T) :=
    selectedRate_continuous.continuousOn.comp huCont (fun _ ht => ht)

  have hIntegral :
      (∫ t in (0 : ℝ)..T, selectedRate (u t)) < 0 := by
    exact negative_integral_on_subinterval
      u selectedRate hT hTres hcontRate hnegResidence

  exact ⟨u, T, hT, hu0, huCont, hRealityT, hTransverseT, hnegT, hIntegral⟩

end Rational345R830PhysicalSegmentStrong
end NSBControl
