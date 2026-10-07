import Mathlib
import YangMills.OSVacuumContinuousExcitation

namespace RequestProject.YangMills

example
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : OSVacuumStronglyContinuousSemigroup H) (t : ℝ≥0) :
    S.excitationTransfer t =
      S.toOSSymmetricPositiveStronglyContinuousSemigroup
        .toOSStronglyContinuousSemigroup.transfer t
        |>.domRestrict (vacuumOrthogonalSubmodule S.vacuum)
        |>.codRestrict (vacuumOrthogonalSubmodule S.vacuum)
          (fun x => S.transfer_preserves_excitation t x.property) := by
  rfl

example
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : OSVacuumStronglyContinuousSemigroup H) :
    OSStronglyContinuousSemigroup (vacuumOrthogonalSubmodule S.vacuum) :=
  S.toExcitationStronglyContinuousSemigroup

end RequestProject.YangMills
