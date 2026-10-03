import NSBControl.Rational345R830ResidenceInterval

namespace NSBControl
namespace Rational345R830ResidenceIntervalTest

open Rational345R830LocalInterval
open Rational345R830ResidenceInterval

example {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    0 < residenceUsableTime ε δ := by
  exact residenceUsableTime_pos hε hδ

example {ε δ : ℝ} (hδ : 0 < δ) :
    residenceUsableTime ε δ < δ := by
  exact residenceUsableTime_lt_residence hδ

end Rational345R830ResidenceIntervalTest
end NSBControl
