import Integration.StructureMorphism

/-!
# Descent of the law is independent of preservation of locality

`Agda/DASHI/Core/ThresholdKernelRenormalisation.agda` carries three separate
certificates for one coarse-graining: `CommutesExactly` (the coarse law
reproduces the fine one), `LocalityPreserving` (fine edges survive), and
`LocalityDestroyed` (some fine edge does not).  Its declaration
`localityPreservationIsNotKernelCommutation` has type
`LocalityPreserving Gf Gc Q → LocalityPreserving Gf Gc Q` and is the identity
function, so the Agda file **names** the separation but does not prove it.

This file proves it, against the Lean owners: commutation is
`Integration.StructureMorphism.Exact`, and locality preservation is a separate
predicate on the node map.  Neither implies the other.

Contents.

* `Renormalisation` — a fine and a coarse carrier, an edge relation and a law on
  each, and the two components of a coarse-graining (a node map and a state
  map);
* `CommutesExactly`, `commutesExactly_iff_exact` — commutation *is* the owner's
  exact square, so all of its transport theory applies
  (`trajectories_descend`);
* `LocalityPreserving`, `LocalityDestroyed`, `not_both`,
  `destroyed_iff_not_preserving`;
* `pooling` — a genuine pooling coarse-graining: the law descends **exactly**
  while locality is **destroyed**;
* `forgetful` — a coarse-graining that **preserves locality** while the law
  provably does **not** descend, in the strong sense that *no* coarse law at all
  reproduces it;
* `descent_and_locality_independent` — the packaged independence.

The carriers are two-element and one-element types with Boolean states.  No
claim is made about any physical renormalisation group, about brains, or about
coarse-graining of any actual system.
-/

namespace Integration.KernelRenormalisation

open Integration.StructureMorphism

/-! ## The data -/

/-- A fine and a coarse system, each with an edge relation and a law on
Boolean states, together with a coarse-graining of nodes and of states. -/
structure Renormalisation (Xf Xc : Type) where
  /-- Adjacency on the fine carrier. -/
  fineEdge : Xf → Xf → Prop
  /-- Adjacency on the coarse carrier. -/
  coarseEdge : Xc → Xc → Prop
  /-- The fine law. -/
  fineLaw : (Xf → Bool) → (Xf → Bool)
  /-- The coarse law. -/
  coarseLaw : (Xc → Bool) → (Xc → Bool)
  /-- The coarse-graining of nodes. -/
  node : Xf → Xc
  /-- The coarse-graining of states. -/
  state : (Xf → Bool) → (Xc → Bool)

variable {Xf Xc : Type}

/-- The law descends exactly. -/
def CommutesExactly (R : Renormalisation Xf Xc) : Prop :=
  ∀ s, R.state (R.fineLaw s) = R.coarseLaw (R.state s)

/-- Commutation is the owner's exact square, not a new notion. -/
theorem commutesExactly_iff_exact (R : Renormalisation Xf Xc) :
    CommutesExactly R ↔ Exact R.state R.fineLaw R.coarseLaw := Iff.rfl

/-- Consequently finite trajectories descend. -/
theorem trajectories_descend {R : Renormalisation Xf Xc} (h : CommutesExactly R) (n : ℕ)
    (s : Xf → Bool) : R.state (R.fineLaw^[n] s) = R.coarseLaw^[n] (R.state s) :=
  exact_iterate h n s

/-- The strongest form of failure: no coarse law at all closes the square. -/
def NoCoarseLaw (R : Renormalisation Xf Xc) : Prop :=
  ¬ ∃ F : (Xc → Bool) → (Xc → Bool), ∀ s, R.state (R.fineLaw s) = F (R.state s)

/-- Every fine edge has a coarse image. -/
def LocalityPreserving (R : Renormalisation Xf Xc) : Prop :=
  ∀ x y, R.fineEdge x y → R.coarseEdge (R.node x) (R.node y)

/-- Some fine edge has no coarse image. -/
def LocalityDestroyed (R : Renormalisation Xf Xc) : Prop :=
  ∃ x y, R.fineEdge x y ∧ ¬ R.coarseEdge (R.node x) (R.node y)

theorem not_both (R : Renormalisation Xf Xc) :
    ¬ (LocalityPreserving R ∧ LocalityDestroyed R) := by
  rintro ⟨hp, x, y, hxy, hnot⟩
  exact hnot (hp x y hxy)

theorem destroyed_iff_not_preserving (R : Renormalisation Xf Xc) :
    LocalityDestroyed R ↔ ¬ LocalityPreserving R := by
  constructor
  · intro h hp; exact not_both R ⟨hp, h⟩
  · intro h
    by_contra hcon
    apply h
    intro x y hxy
    by_contra hne
    exact hcon ⟨x, y, hxy, hne⟩

/-! ## Descent without locality -/

/-- Pooling two adjacent fine nodes into a single coarse node.  The fine law
exchanges the two nodes; the coarse state is their disjunction, which the
exchange does not move. -/
def pooling : Renormalisation Bool Unit where
  fineEdge := fun x y => x ≠ y
  coarseEdge := fun x y => x ≠ y
  fineLaw := fun s x => s (!x)
  coarseLaw := id
  node := fun _ => ()
  state := fun s _ => s false || s true

/-- **The law descends exactly through the pooling.** -/
theorem pooling_commutes : CommutesExactly pooling := by
  intro s
  funext _
  show (s (!false) || s (!true)) = (s false || s true)
  exact Bool.or_comm (s true) (s false)

/-- **And it destroys locality**: the two adjacent fine nodes are pooled into a
single coarse node, which is not adjacent to itself. -/
theorem pooling_destroys_locality : LocalityDestroyed pooling :=
  ⟨false, true, Bool.false_ne_true, fun h => h rfl⟩

/-! ## Locality without descent -/

/-- The identity coarse-graining of nodes, with a state map that keeps only the
first node.  The fine law exchanges the two nodes, so the retained coordinate is
replaced by the discarded one. -/
def forgetful : Renormalisation Bool Bool where
  fineEdge := fun x y => x ≠ y
  coarseEdge := fun x y => x ≠ y
  fineLaw := fun s x => s (!x)
  coarseLaw := id
  node := id
  state := fun s _ => s false

/-- **Locality is preserved**: the node map is the identity. -/
theorem forgetful_preserves_locality : LocalityPreserving forgetful := fun _ _ h => h

/-- **But no coarse law reproduces the fine one.**  Two fine states with the
same retained coordinate are sent by the fine law to states with different
retained coordinates. -/
theorem forgetful_no_coarse_law : NoCoarseLaw forgetful := by
  rintro ⟨F, hF⟩
  have h1 : (fun _ : Bool => true) = F (fun _ : Bool => false) := hF (fun b => b)
  have h2 : (fun _ : Bool => false) = F (fun _ : Bool => false) := hF (fun _ => false)
  exact absurd (congrFun (h1.trans h2.symm) false) (by decide)

theorem forgetful_not_commutes : ¬ CommutesExactly forgetful := fun h =>
  forgetful_no_coarse_law ⟨forgetful.coarseLaw, h⟩

/-! ## The independence -/

/-- **The separation the Agda module names but does not prove.**  Exact descent
of the law and preservation of locality are logically independent: pooling gives
the first without the second, and the forgetful coarse-graining gives the second
without the first — indeed without *any* coarse law. -/
theorem descent_and_locality_independent :
    (CommutesExactly pooling ∧ LocalityDestroyed pooling) ∧
      (LocalityPreserving forgetful ∧ NoCoarseLaw forgetful) :=
  ⟨⟨pooling_commutes, pooling_destroys_locality⟩,
    ⟨forgetful_preserves_locality, forgetful_no_coarse_law⟩⟩

end Integration.KernelRenormalisation
