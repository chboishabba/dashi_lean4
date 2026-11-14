import Mathlib
import YangMills.CMP116WilsonMarkedExpansionLocalization

namespace RequestProject.YangMills

example
    {Cluster : Type*} [DecidableEq Cluster]
    (clusters : Finset Cluster)
    (weight : Cluster → ℝ)
    (touchesLeft touchesRight : Cluster → Bool)
    (hzero : ∀ c ∈ clusters,
      ¬ (touchesLeft c = true ∧ touchesRight c = true) → weight c = 0) :
    (∑ c ∈ clusters, weight c) =
      ∑ c ∈ clusters.filter (fun c => touchesLeft c && touchesRight c), weight c :=
  full_cluster_sum_eq_connecting_filter clusters weight touchesLeft touchesRight hzero

end RequestProject.YangMills
