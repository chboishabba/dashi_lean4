import NSBControl.Rational345R830PhysicalSegmentStrong
import NSBControl.Rational345Round71ZeroMode

/-!
# R830 physical packet segment

The Agda live physical packet excludes k=0 in addition to reality and
transversality.  Shrink the already-negative physical R830 interval once more
to the local zero-mode radius.  Strict negativity survives restriction to any
positive subinterval.
-/

open Set

namespace NSBControl
namespace Rational345R830PhysicalPacketSegment

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345R830ResidenceInterval
open Rational345R830PointwiseNegative
open Rational345Round71RealityField
open Rational345Round71TrajectoryPhysical
open Rational345Round71ZeroMode
open Rational345R830DecisionCompiler
open Rational345R830PhysicalSegment

/-- A nonzero real Galerkin segment carrying all three structural properties
of the Round71 live packet: Fourier reality, divergence freedom, and zero mean. -/
theorem r830_physical_packet_negative_segment :
    ∃ (u : ℝ → State) (T : ℝ),
      0 < T ∧
      u 0 = u₀ ∧
      ContinuousOn u (Icc (0 : ℝ) T) ∧
      (∀ t ∈ Icc (0 : ℝ) T, realityTransform (u t) = u t) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        ∀ k : Mode, bilinearDot (kComplex k) (u t k) = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) T, u t zeroMode = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) T, selectedRate (u t) < 0) ∧
      (∫ t in (0 : ℝ)..T, selectedRate (u t)) < 0 := by
  obtain ⟨u, ε, δ, hε, hδ, hu0, hderiv, hres, hnegResidence⟩ :=
    r830_pointwise_negative_witness
  obtain ⟨ρR, hρR, hReality⟩ :=
    trajectory_reality_radius u hε hu0 hderiv
  obtain ⟨ρD, hρD, hTransverse⟩ :=
    trajectory_transverse_radius u hε hu0 hderiv
  obtain ⟨ρ0, hρ0, hZero⟩ :=
    trajectory_zeroMode_radius u hε hu0 hderiv

  let Tphys := physicalUsableTime ε δ ρR ρD
  let T := min Tphys (ρ0 / 2)

  have hTphys : 0 < Tphys := by
    exact physicalUsableTime_pos hε hδ hρR hρD
  have hT : 0 < T := by
    dsimp [T]
    exact lt_min hTphys (by linarith)
  have hTlePhys : T ≤ Tphys := min_le_left _ _
  have hTleZero : T ≤ ρ0 / 2 := min_le_right _ _
  have hTresPhys : Tphys ≤ residenceUsableTime ε δ :=
    physicalUsableTime_le_residence ε δ ρR ρD
  have hTres : T ≤ residenceUsableTime ε δ := hTlePhys.trans hTresPhys
  have hTR : T < ρR :=
    hTlePhys.trans_lt (physicalUsableTime_lt_reality hρR)
  have hTD : T < ρD :=
    hTlePhys.trans_lt (physicalUsableTime_lt_transverse hρD)
  have hT0 : T < ρ0 := by
    calc
      T ≤ ρ0 / 2 := hTleZero
      _ < ρ0 := by linarith
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

  have hZeroT : ∀ t ∈ Icc (0 : ℝ) T, u t zeroMode = 0 := by
    intro t ht
    apply hZero t
    rw [abs_of_nonneg ht.1]
    exact ht.2.trans_lt hT0

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

  exact ⟨u, T, hT, hu0, huCont, hRealityT, hTransverseT,
    hZeroT, hnegT, hIntegral⟩

end Rational345R830PhysicalPacketSegment
end NSBControl
