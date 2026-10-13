import Synthesis.JacobsonCalibratedVacuum

namespace Synthesis.JacobsonCalibratedVacuumRegression

open Synthesis.JacobsonCalibratedVacuum

example : planckConstantSI = 6.62607015e-34 := rfl
example : newtonConstantCODATA2022 = 6.67430e-11 := rfl
example : newtonConstantStdUncertaintyCODATA2022 = 0.00015e-11 := rfl
example (x : ℝ) : calibratedVacuumData.ricci x = zeroTensor := rfl
example (x : ℝ) : calibratedVacuumData.stress x = zeroTensor := rfl
example : authorityInstantiationClosedForVacuumBenchmark = true := rfl
example : calibrationReceiptOwned = true := rfl

end Synthesis.JacobsonCalibratedVacuumRegression
