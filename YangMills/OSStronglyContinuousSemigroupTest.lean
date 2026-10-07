import Mathlib
import YangMills.OSStronglyContinuousSemigroup

namespace RequestProject.YangMills

example
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (S : OSStronglyContinuousSemigroup H) (x : H) :
    Continuous (fun t : ℝ≥0 => S.transfer t x) :=
  S.stronglyContinuous x

example
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : ℕ → H →L[ℝ] H)
    (S : OSStronglyContinuousSemigroupExtension T)
    (n : ℕ) :
    S.toOSStronglyContinuousSemigroup.transfer (n : ℝ≥0) = T n :=
  S.discreteAgreement n

example
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : OSSymmetricPositiveStronglyContinuousSemigroup H)
    (t : ℝ≥0) :
    (S.toOSStronglyContinuousSemigroup.transfer t).IsPositive :=
  S.transfer_isPositive t

example
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : OSSymmetricPositiveStronglyContinuousSemigroup H)
    (t : ℝ≥0) :
    IsSelfAdjoint (S.toOSStronglyContinuousSemigroup.transfer t) :=
  S.transfer_isSelfAdjoint t

end RequestProject.YangMills
