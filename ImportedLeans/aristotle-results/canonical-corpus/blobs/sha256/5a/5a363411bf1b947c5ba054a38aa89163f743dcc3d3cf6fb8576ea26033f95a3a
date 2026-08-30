/-!
# Lean mirror of `DASHI/Core/ComparisonLawCore.agda`

This is the generic governed-comparison interface.  It contains no theorem
asserting that a comparison law holds: the law and residual are data supplied
by a concrete instance, and `comparisonNeverMeansTruth` remains an explicit
boundary flag.
-/

namespace AgdaMirror.ComparisonLawCore

/-- Two structured carriers projected into a common comparison surface. -/
structure ComparisonLawCore where
  LeftCarrier : Type
  RightCarrier : Type
  Surface : Type
  leftProject : LeftCarrier → Surface
  rightProject : RightCarrier → Surface
  Residual : Surface → Surface → Type
  ComparisonLaw : Surface → Surface → Type
  comparisonNeverMeansTruth : Bool

/-- The public left projection. -/
def ProjectedLeft (core : ComparisonLawCore) : core.LeftCarrier → core.Surface :=
  core.leftProject

/-- The public right projection. -/
def ProjectedRight (core : ComparisonLawCore) : core.RightCarrier → core.Surface :=
  core.rightProject

/-- The typed obstruction between two projected surface values. -/
def ComparisonResidual (core : ComparisonLawCore) :
    core.Surface → core.Surface → Type :=
  core.Residual

end AgdaMirror.ComparisonLawCore
