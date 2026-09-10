import Integration.Kernel.LineageEdge

/-!
# Weld: amplification lineage → evidence dependence, executably

`Integration.Kernel.LineageEdge` proves that a non-generative edge adds no
provenance root, but its only fixture is a three-node star.  The consumer that
the corpus actually wants is a *counting* one: given a pile of reports,
citations and derived observations, how many independent acquisitions are
really there?

This file supplies an executable instance of that question.  Twenty observation
nodes are wired into a lineage in which node `i` is amplified from node `i - 3`;
the three nodes `0, 1, 2` are the acquisitions and the remaining seventeen are
descendants.

## What is proved

* `observationLineage` — a genuine `Lineage`, i.e. its propagation obligation
  `amplification_preserves_roots` is discharged, not postulated.
* **`amplified_from_rootNode`** — every node is `AmplifiedFrom` its own root
  node, by induction along the chain (not by fixture enumeration).
* **`twenty_observations_are_three_sources`** — the headline count: twenty
  observations, seventeen of them with a parent, and a root support of
  cardinality three.
* **`same_class_are_not_independent`** — two observations of the same class are
  never independent replication, however far apart in the chain; and
  `different_class_are_independent` — across classes they are.
* `count_is_not_support` — the count coordinate does not determine the root
  support, restated on this instance.

**Claim boundary.**  Nodes and roots are elements of `Fin 20` and `Fin 3`; the
edge typing is stipulated here.  Nothing is claimed about any real report,
citation, dataset or observation.
-/

namespace Integration.Kernel.Welds.AmplifiedObservationCount

open Integration.Kernel.EvidenceDependence Integration.Kernel.LineageEdge
open Integration.Kernel.LineageEdge.EdgeKind

/-! ## §1 Twenty observations over three acquisitions -/

/-- The observation nodes. -/
abbrev Obs := Fin 20

/-- The acquisition roots. -/
abbrev Root := Fin 3

/-- Which acquisition an observation descends from. -/
def rootOf (i : Obs) : Root := ⟨i.val % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The node that is the acquisition of `i`'s class. -/
def rootNode (i : Obs) : Obs := ⟨i.val % 3, by omega⟩

/-- The lineage: `i` is amplified from `i - 3`, and nothing else is an edge. -/
def observationLineage : Lineage Obs Root where
  kind x y := if x.val + 3 = y.val then some amplifiedBy else none
  rootsOf i := {rootOf i}
  amplification_preserves_roots := by
    intro x y k hk _
    by_cases h : x.val + 3 = y.val
    · have : rootOf y = rootOf x := by
        apply Fin.ext
        simp only [rootOf]
        omega
      rw [this]
    · simp [h] at hk

/-- The provenance the lineage induces. -/
abbrev prov : Provenance Obs Root := observationLineage.provenance

@[simp] theorem prov_rootsOf (i : Obs) : prov.rootsOf i = {rootOf i} := rfl

/-! ## §2 Every observation is amplified from its acquisition -/

theorem kind_step {x y : Obs} (h : x.val + 3 = y.val) :
    observationLineage.kind x y = some amplifiedBy := by
  simp [observationLineage, h]

/-- **Every node descends from its own root node by amplification alone.** -/
theorem amplified_from_rootNode : ∀ (n : ℕ) (i : Obs), i.val = n →
    AmplifiedFrom observationLineage (rootNode i) i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi
    by_cases h3 : n < 3
    · have hri : rootNode i = i := by
        apply Fin.ext
        simp only [rootNode, hi]
        omega
      rw [hri]
      exact .refl i
    · have hb : n - 3 < 20 := by omega
      have hlt : n - 3 < n := by omega
      have hroot : rootNode (⟨n - 3, hb⟩ : Obs) = rootNode i := by
        apply Fin.ext
        simp only [rootNode, hi]
        omega
      have hprev := ih (n - 3) hlt ⟨n - 3, hb⟩ rfl
      rw [hroot] at hprev
      exact .step hprev amplifiedBy (kind_step (by simp only []; omega)) rfl

/-- The chain form, stated for a node directly. -/
theorem amplified_from_root (i : Obs) :
    AmplifiedFrom observationLineage (rootNode i) i :=
  amplified_from_rootNode i.val i rfl

/-! ## §3 The count -/

/-- The three acquisitions. -/
def acquisitions : List Obs := [0, 1, 2]

/-- The seventeen amplified descendants. -/
def descendants : List Obs := (List.finRange 20).filter (fun i => decide (3 ≤ i.val))

theorem descendants_length : descendants.length = 17 := by decide

theorem acquisitions_length : acquisitions.length = 3 := rfl

/-- **Twenty observations, three sources.**  The visible pile has twenty
entries and seventeen of them are amplified descendants; the provenance support
of the whole pile has cardinality three. -/
theorem twenty_observations_are_three_sources :
    (List.finRange 20).length = 20 ∧
      descendants.length = 17 ∧
        (rootSupport prov (List.finRange 20)).card = 3 := by
  refine ⟨by decide, descendants_length, by decide⟩

/-! ## §4 What the count is allowed to license -/

/-- **Same-class observations are never independent replication.** -/
theorem same_class_are_not_independent {i j : Obs} (h : rootOf i = rootOf j) :
    ¬ Independent prov i j := by
  refine shared_root_blocks_independent_replication ⟨rootOf i, ?_, ?_⟩
  · simp
  · simp [h]

/-- Across classes, independence does hold. -/
theorem different_class_are_independent {i j : Obs} (h : rootOf i ≠ rootOf j) :
    Independent prov i j := by
  show Disjoint ({rootOf i} : Finset Root) {rootOf j}
  exact Finset.disjoint_singleton.2 h

/-- Two long-chain descendants of the same acquisition — nodes `3` and `18`,
fifteen steps apart — are still not independent evidence. -/
theorem far_apart_but_dependent : ¬ Independent prov 3 18 :=
  same_class_are_not_independent (by decide)

/-- **The visible count does not determine the support.**  Three observations
drawn from one class and three drawn from three classes have the same length
and different root support. -/
theorem count_is_not_support :
    ([0, 3, 6] : List Obs).length = ([0, 1, 2] : List Obs).length ∧
      (rootSupport prov [0, 3, 6]).card ≠ (rootSupport prov [0, 1, 2]).card := by
  refine ⟨rfl, by decide⟩

end Integration.Kernel.Welds.AmplifiedObservationCount
