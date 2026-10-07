import Integration.E6MinusculeWeightModule

namespace Integration.E6MinusculeWeightModuleRegression

open Integration.E6MinusculeWeightModule
open Integration.E6Minuscule27SchlafliRecognition

example : Module.finrank ℝ MinusculeModule = 27 := minuscule_module_finrank
example : Function.Injective coordinateWeightLine := coordinateWeightLine_injective
example (w : Omega5Weight) : weightVector w ≠ 0 := weightVector_ne_zero w
example : canonicalBoundary.canonicalCoordinateModuleTyped = true := rfl
example : canonicalBoundary.exactDimension27Paid = true := rfl
example : canonicalBoundary.distinctWeightLinesPaid = true := rfl
example : canonicalBoundary.simpleReflectionLinearActionPaid = true := rfl
example : canonicalBoundary.lineIntertwiningPaid = true := rfl
example : canonicalBoundary.albertProductPaidHere = false := rfl
example : canonicalBoundary.e6JordanAutomorphismCompatibilityPaidHere = false := rfl

end Integration.E6MinusculeWeightModuleRegression
