import Integration.Kernel.EvidenceDependence

/-!
# Lineage geometry: amplification is not generation

`Integration.Kernel.EvidenceDependence` treats provenance as a set of roots and
asks whether two units share one.  That is the simplest question one can ask
about lineage.  Several lanes of this corpus need a sharper one: *how* the
influence travelled.  A downstream node may have been generated from an
upstream one, or merely transformed, selected, funded, amplified, verified or
reported.  Those edges do very different things to the evidence, and a plain
"depends on" graph erases the difference.

This file types the edges and proves the consequence that matters:
**a non-generative edge introduces no new provenance root**, so a chain of
amplification, however long, never manufactures independent replication.

## What is proved

* `EdgeKind`, and the stipulated classifier `Generative` (only `generatedFrom`
  counts; the rest are downstream operations).  As everywhere in this kernel
  this is a classification of labels, not an inspection of anything real.
* `Lineage` bundles the edge typing with the roots and carries the propagation
  law **as a proof obligation**, not a Boolean: any instance must supply
  `amplification_preserves_roots`.  `starLineage` discharges it, so the
  structure is inhabited and the theorems below are not vacuous.
* **`roots_constant_along_amplification`** — along any chain of non-generative
  edges the root set is unchanged.
* **`amplified_copies_are_not_independent_replication`** — the payoff, welded to
  `Integration.Kernel.EvidenceDependence`: two nodes amplified from a common
  rooted source are provably *not* independent.  Twenty visible downstream
  observations of one acquisition are not twenty replications.
* **`edge_kind_does_not_descend_through_roots`** — and the converse warning: the
  root sets do not recover the edge semantics, so a `depends-on` DAG is a
  quotient of the typed lineage (`not_descendsThrough_of_collision` again).
* `downstream_count_is_not_source_count` — the count fixture in the typed
  language: three amplified nodes, one root.

**Claim boundary.**  Nodes, roots and the edge typing are arbitrary data; the
`Generative` classifier is stipulated in this file.  Nothing is claimed about
any actual citation, funding relationship, dataset or publication.
-/

namespace Integration.Kernel.LineageEdge

open Integration.Kernel.Quotient Integration.Kernel.EvidenceDependence

universe u v

/-! ## §1 Typed lineage edges -/

/-- How influence travelled along an edge. -/
inductive EdgeKind : Type
  | generatedFrom
  | transformedBy
  | selectedBy
  | fundedBy
  | amplifiedBy
  | verifiedBy
  | reportedBy
  deriving DecidableEq, Repr

open EdgeKind

/-- Which edges introduce new provenance.  Stipulated: only generation does;
transformation, selection, funding, amplification, verification and reporting
are operations on something already there. -/
def Generative : EdgeKind → Bool
  | generatedFrom => true
  | _ => false

theorem generative_iff (k : EdgeKind) : Generative k = true ↔ k = generatedFrom := by
  cases k <;> simp [Generative]

theorem amplification_is_not_generative : Generative amplifiedBy = false := rfl

theorem funding_is_not_generative : Generative fundedBy = false := rfl

theorem reporting_is_not_generative : Generative reportedBy = false := rfl

/-! ## §2 A lineage, with the propagation law as an obligation -/

variable {N : Type u} {R : Type v}

/-- A typed lineage: which edges exist and of what kind, what roots each node
rests on, and the law that a non-generative edge adds no root.  The law is a
`Prop` field: an instance has to prove it. -/
structure Lineage (N : Type u) (R : Type v) where
  /-- The kind of the edge from one node to another, if there is one. -/
  kind : N → N → Option EdgeKind
  /-- The provenance roots of a node. -/
  rootsOf : N → Finset R
  /-- A non-generative edge introduces no new root. -/
  amplification_preserves_roots :
    ∀ x y k, kind x y = some k → Generative k = false → rootsOf y = rootsOf x

/-- The provenance assignment a lineage induces, for use with
`Integration.Kernel.EvidenceDependence`. -/
def Lineage.provenance (L : Lineage N R) : Provenance N R := ⟨L.rootsOf⟩

/-- `y` is reachable from `x` by non-generative edges only. -/
inductive AmplifiedFrom (L : Lineage N R) : N → N → Prop
  | refl (x : N) : AmplifiedFrom L x x
  | step {x y z : N} (h : AmplifiedFrom L x y) (k : EdgeKind)
      (hk : L.kind y z = some k) (hgen : Generative k = false) : AmplifiedFrom L x z

/-- **Amplification adds no root.**  However long the chain of non-generative
edges, the provenance closure is exactly the source's. -/
theorem roots_constant_along_amplification {L : Lineage N R} {x y : N}
    (h : AmplifiedFrom L x y) : L.rootsOf y = L.rootsOf x := by
  induction h with
  | refl => rfl
  | step _ k hk hgen ih => rw [L.amplification_preserves_roots _ _ k hk hgen, ih]

/-- **Amplified copies are not independent replication.**  Two nodes amplified
from a common rooted source share every root, so they fail the independence test
of `Integration.Kernel.EvidenceDependence`. -/
theorem amplified_copies_are_not_independent_replication [DecidableEq R] {L : Lineage N R}
    {x y z : N} (hy : AmplifiedFrom L x y) (hz : AmplifiedFrom L x z)
    (hne : (L.rootsOf x).Nonempty) : ¬ Independent L.provenance y z := by
  obtain ⟨r, hr⟩ := hne
  refine shared_root_blocks_independent_replication ⟨r, ?_, ?_⟩
  · show r ∈ L.rootsOf y
    rw [roots_constant_along_amplification hy]; exact hr
  · show r ∈ L.rootsOf z
    rw [roots_constant_along_amplification hz]; exact hr

/-! ## §3 Two lineages the root sets cannot tell apart -/

/-- Three nodes, all amplified from one root. -/
def starLineage : Lineage (Fin 3) ℕ where
  kind _ _ := some amplifiedBy
  rootsOf _ := {0}
  amplification_preserves_roots _ _ _ _ _ := rfl

/-- The same root sets, but every edge is a generation. -/
def generativeLineage : Lineage (Fin 3) ℕ where
  kind _ _ := some generatedFrom
  rootsOf _ := {0}
  amplification_preserves_roots _ _ _ _ _ := rfl

theorem star_roots_eq_generative_roots :
    starLineage.rootsOf = generativeLineage.rootsOf := rfl

theorem star_kinds_differ : starLineage.kind ≠ generativeLineage.kind := by
  intro h
  have := congrFun (congrFun h 0) 1
  exact absurd this (by decide)

/-- **The `depends-on` graph is a quotient of the typed lineage.**  Two lineages
with identical root sets differ in every edge kind, so no function of the roots
recovers how the influence travelled. -/
theorem edge_kind_does_not_descend_through_roots :
    ¬ DescendsThrough (fun L : Lineage (Fin 3) ℕ => L.kind)
        (fun L : Lineage (Fin 3) ℕ => L.rootsOf) :=
  not_descendsThrough_of_collision star_roots_eq_generative_roots star_kinds_differ

/-- Every node of the star is amplified from node `0`. -/
theorem star_all_amplified (i : Fin 3) : AmplifiedFrom starLineage 0 i :=
  .step (.refl 0) amplifiedBy rfl rfl

/-- **Three downstream nodes, one root.**  Neither of the two visible nodes is
an independent replication of the other. -/
theorem downstream_count_is_not_source_count :
    (rootSupport starLineage.provenance [0, 1, 2]).card = 1 ∧
      ¬ Independent starLineage.provenance 1 2 := by
  refine ⟨by decide, ?_⟩
  exact amplified_copies_are_not_independent_replication (star_all_amplified 1)
    (star_all_amplified 2) ⟨0, by decide⟩

end Integration.Kernel.LineageEdge
