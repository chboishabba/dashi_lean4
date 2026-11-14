import Mathlib
import YangMills.OSVacuumContinuousExcitation

namespace RequestProject.YangMills

example
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : OSVacuumStronglyContinuousSemigroup H) (t : ℝ≥0) :
    vacuumOrthogonalSubmodule S.vacuum →L[ℝ]
      vacuumOrthogonalSubmodule S.vacuum :=
  S.excitationTransfer t

example
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : OSVacuumStronglyContinuousSemigroup H) :
    OSStronglyContinuousSemigroup (vacuumOrthogonalSubmodule S.vacuum) :=
  S.toExcitationStronglyContinuousSemigroup

example
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : OSVacuumStronglyContinuousSemigroup H) :
    OSSymmetricPositiveStronglyContinuousSemigroup
      (vacuumOrthogonalSubmodule S.vacuum) :=
  S.toExcitationSymmetricPositiveStronglyContinuousSemigroup

end RequestProject.YangMills
