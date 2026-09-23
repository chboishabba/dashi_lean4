/-
# A witness that the B3+B4 hypotheses are jointly satisfiable

`selected_boundary_below_connecting_decay` is an inequality under a list of hypotheses,
so it is worth checking that those hypotheses can hold simultaneously with a *nonzero*
selected boundary and two genuinely distinct source marks.  This file instantiates the
theorem on the single-edge graph, with one localization domain carrying one surviving
term of nonzero value, and records the resulting concrete inequality.
-/
import RequestProject.YangMills.Cluster.SelectedBoundary

open Finset

namespace RequestProject.YangMills.Cluster

open SimpleGraph

/-- The single edge `0 ~ 1`. -/
abbrev edgeGraph : SimpleGraph (Fin 2) := ⊤

/-- The connecting walk between the two source marks. -/
def edgeWalk : edgeGraph.Walk 0 1 := Walk.cons (by decide) Walk.nil

theorem edgeWalk_length : edgeWalk.length = 1 := rfl

theorem edgeWalk_support : edgeWalk.support.toFinset = (Finset.univ : Finset (Fin 2)) := by
  decide

/-- The hypotheses of `selected_boundary_below_connecting_decay` are satisfiable with a
nonzero selected boundary: the single-edge graph with one domain and one term of value
`1/4` gives a genuine instance of the bound. -/
theorem witness_selected_boundary :
    |(1 / 4 : ℝ)| ≤ (1 * clusterSeries 1 (1 / 2)) * (1 / 2 : ℝ) ^ edgeGraph.dist 0 1 := by
  have hdeg : ∀ x : Fin 2, edgeGraph.degree x ≤ 1 := by decide
  have key := selected_boundary_below_connecting_decay (ι := Unit) edgeGraph 1 le_rfl hdeg
    0 1 (1 / 2) 1 zero_le_one (by norm_num) (by norm_num) (by norm_num)
    {(Finset.univ : Finset (Fin 2))} (fun _ => (Finset.univ : Finset Unit))
    (fun _ => edgeWalk) (fun _ => 1) (fun _ => 1 / 4) (fun _ => 1 / 4)
    (fun _ => zero_le_one)
    (fun _ _ => ⟨(), Finset.mem_univ ()⟩)
    (fun Y hY _ _ => by
      rw [Finset.mem_singleton] at hY
      rw [hY]; exact edgeWalk_support)
    (fun _ _ _ _ => by rw [edgeWalk_length]; norm_num)
    (fun _ _ => by norm_num)
    (fun _ _ => by norm_num)
  simpa using key

end RequestProject.YangMills.Cluster
