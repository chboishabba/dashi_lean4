import Mathlib
import YangMills.CMP116WilsonPointwiseLocalization

open MeasureTheory

namespace RequestProject.YangMills

example
    {Cluster : Type*} [DecidableEq Cluster]
    (clusters : Finset Cluster)
    (weight shellCharge : Cluster → ℝ)
    (shell : ℝ)
    (hpoint : ∀ c ∈ clusters, |weight c| ≤ shellCharge c)
    (hshell : (∑ c ∈ clusters, shellCharge c) ≤ shell) :
    (∑ c ∈ clusters, |weight c|) ≤ shell :=
  finite_abs_weight_sum_le_shell_of_pointwise_localization
    clusters weight shellCharge shell hpoint hshell

end RequestProject.YangMills
