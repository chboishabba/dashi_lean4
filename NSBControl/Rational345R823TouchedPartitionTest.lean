import NSBControl.Rational345R823TouchedPartition

namespace NSBControl
namespace Rational345R823TouchedPartitionTest

open Rational345R823TouchedPartition

example
    {α : Type*} [Fintype α]
    (cell : α → ℝ) :
    ccTouchedFold4 cell = completeFold cell := by
  exact ccTouchedFold4_eq_completeFold cell

example
    {α : Type*} [Fintype α]
    (cell : α → ℝ) :
    fullySeparatedFold4 cell = 0 := by
  exact fullySeparatedFold4_eq_zero cell

end Rational345R823TouchedPartitionTest
end NSBControl
