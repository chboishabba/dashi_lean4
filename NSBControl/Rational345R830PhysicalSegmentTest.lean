import NSBControl.Rational345R830PhysicalSegment

namespace NSBControl
namespace Rational345R830PhysicalSegmentTest

open Set
open Rational345RealRadius4
open Rational345RealInitialState
open Rational345Round71RealityField
open Rational345R830PhysicalSegment

example :
    ∃ (u : ℝ → State) (T : ℝ),
      0 < T ∧
      u 0 = u₀ ∧
      (∀ t ∈ Icc (0 : ℝ) T, realityTransform (u t) = u t) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        ∀ k : Mode, bilinearDot (kComplex k) (u t k) = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) T, selectedRate (u t) < 0) ∧
      (∫ t in (0 : ℝ)..T, selectedRate (u t)) < 0 := by
  exact r830_physical_negative_segment

end Rational345R830PhysicalSegmentTest
end NSBControl
