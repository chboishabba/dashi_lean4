import Mathlib
import Integration.OggSSPP2BalancedTernaryPuncturedPlane
import Integration.OggSSPP2Gamma0FourMarkedSubgroupSchemeSource

/-!
# p=2 Gamma_0(4): unique raw supersingular cyclic subgroup vs ten-state residual

External source context:
Bertolini--Darmon--Prasanna, with appendix by Brian Conrad,
"p-adic L-functions and the coniveau filtration on Chow groups",
J. Reine Angew. Math. 731 (2017), 21--86,
DOI 10.1515/crelle-2014-0150.

The source states that a supersingular elliptic curve over an algebraic closure
of F_p has a unique Drinfeld cyclic subgroup of order p^r, namely ker(F^r).
Thus at p=2, r=2, the raw cyclic rank-4 subgroup is unique.

Therefore the ten-state p=2 residual target is not a set of ten raw cyclic
order-4 subgroup choices on one fixed supersingular elliptic curve.
-/

namespace Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation

open Integration.OggSSPP2BalancedTernaryPuncturedPlane

def rawCyclicSubgroupCount : Nat := 1
def residualTargetCount : Nat := Fintype.card DuplicatedCentreNineSheet

theorem raw_cyclic_subgroup_count_is_one :
    rawCyclicSubgroupCount = 1 := by rfl

theorem residual_target_count_is_ten :
    residualTargetCount = 10 := by decide

theorem one_does_not_equal_ten :
    rawCyclicSubgroupCount ≠ residualTargetCount := by decide

inductive SupersingularRawGamma0FourSubgroup
  | kerFrobeniusSquared
  deriving DecidableEq, Repr, Fintype

theorem raw_subgroup_type_has_one_state :
    Fintype.card SupersingularRawGamma0FourSubgroup = 1 := by decide

theorem every_raw_subgroup_is_frobenius_squared_kernel
    (s : SupersingularRawGamma0FourSubgroup) :
    s = .kerFrobeniusSquared := by
  cases s
  rfl

inductive RequiredExtraArithmeticDatum
  | deformationMarking
  | inertiaOrAutomorphismMarking
  | stackyOrLocalModelBranch
  | otherArithmeticResidual
  deriving DecidableEq, Repr

structure MarkingOverUniqueGamma0FourSubgroup where
  MarkedState : Type
  rawSubgroup :
    MarkedState → SupersingularRawGamma0FourSubgroup
  everyStateLiesOverKerFrobeniusSquared :
    ∀ s, rawSubgroup s = .kerFrobeniusSquared
  residualDatum :
    MarkedState → RequiredExtraArithmeticDatum
  provenanceFromArithmeticModuli : Prop

inductive ClaimOrigin
  | externalSourceContext
  | repositoryCrossModuleInference
  | openArithmeticRecognition
  deriving DecidableEq, Repr

structure Boundary where
  sourceBackedUniqueDrinfeldCyclicSubgroupUsed : Bool
  p2r2SpecializationIsKerFrobeniusSquared : Bool
  rawSubgroupChoiceCountIsOne : Bool
  residualTargetCountIsTen : Bool
  tenResidualStatesIdentifiedWithRawSubgroupChoices : Bool
  extraArithmeticMarkingRequired : Bool
  actualExtraArithmeticMarkingConstructed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sourceBackedUniqueDrinfeldCyclicSubgroupUsed := true
  p2r2SpecializationIsKerFrobeniusSquared := true
  rawSubgroupChoiceCountIsOne := true
  residualTargetCountIsTen := true
  tenResidualStatesIdentifiedWithRawSubgroupChoices := false
  extraArithmeticMarkingRequired := true
  actualExtraArithmeticMarkingConstructed := false

end Integration.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparation
