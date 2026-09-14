import Integration.Kernel.Quotient

/-!
# Evidence dependence: shared provenance roots block independent replication

`Agda/DASHI/Biology/DrosophilaSameTrialProvenanceDependenceExact.agda` (in the
6 September tranche archive shipped with this project) sets up the architecture
this file owns: evidence units carrying upstream roots — dataset, animal,
trial, acquisition, registration, preprocessing, predictor, observer protocol —
and the principle that two observations sharing a root are not an independent
replication of one another.  It also separates *aggregation within a dependence
class* from *aggregation across independent classes*.

**What that Agda module actually contains, and what it does not.**  Its
`ProvenanceGraph` is a record interface whose `sharedRoot` and `sharedRootSound`
fields are `Set`-valued *parameters*, and its
`EvidenceDependenceAssessment` stores the independence rules as `Bool` fields
with `≡ true`/`≡ false` obligations supplied by whoever builds the record.  So
nothing there is a derived graph theorem, and nothing is transported here.  This
file is the Lean-side construction: roots are a `Finset`, sharing and
independence are *defined* from them, and the rules the Agda record stipulates
are proved.

## What is proved

* `independent_iff_disjoint_roots`, `sharesRoot_iff_exists_common_root` — the
  two notions are complementary and are decided by the root sets
  (`not_independent_iff_sharesRoot`).
* **`shared_root_blocks_independent_replication`** — the rule the Agda record
  carries as a `Bool` field, here a theorem.
* `not_independent_self` — an evidence unit with any root at all is not
  independent of itself, so "two readings of the same trial" never certifies
  replication.
* **`sharesRoot_not_transitive`** — sharing a root is *not* an equivalence
  relation, so "dependence class" cannot simply be its quotient; a class map
  has to be given, which is what §3 does.
* **`independent_of_different_class`** — the exact discipline that licenses the
  two-stage aggregation: if the class map separates only independent units
  (`ClassSeparates`), then units in different classes are provably independent,
  so across-class aggregation is aggregation of independent evidence.
* **`count_does_not_determine_root_support`** — the headline non-descent, an
  instance of `Integration.Kernel.Quotient.not_descendsThrough_of_collision`:
  how many evidence units you hold is not a function computing how many
  independent roots they rest on.  `amplification_is_not_generation` is the
  explicit fixture: three units, one root.
* `card_roots_union_of_independent` / `card_roots_union_lt_of_shared` — the
  arithmetic behind that: independent units add their roots, dependent ones do
  not.

**Claim boundary.**  Everything is a statement about a function
`rootsOf : E → Finset R` for arbitrary `E` and `R`.  "Evidence", "root" and
"replication" are names for the arguments; nothing is claimed about any
experiment, dataset or organism.
-/

namespace Integration.Kernel.EvidenceDependence

open Integration.Kernel.Quotient

universe u v w

variable {E : Type u} {R : Type v}

/-! ## §1 Provenance roots, sharing and independence -/

/-- A provenance assignment: each evidence unit rests on a finite set of
upstream roots. -/
structure Provenance (E : Type u) (R : Type v) where
  /-- The upstream roots an evidence unit rests on. -/
  rootsOf : E → Finset R

variable (P : Provenance E R)

/-- Two evidence units share a root. -/
def SharesRoot (x y : E) : Prop := ∃ r, r ∈ P.rootsOf x ∧ r ∈ P.rootsOf y

/-- Two evidence units are independent: their provenance closures are disjoint.
This is the *definition* of independence used here; it is not a stipulated
Boolean field. -/
def Independent (x y : E) : Prop := Disjoint (P.rootsOf x) (P.rootsOf y)

variable {P}

theorem independent_iff_disjoint_roots {x y : E} :
    Independent P x y ↔ Disjoint (P.rootsOf x) (P.rootsOf y) := Iff.rfl

theorem sharesRoot_iff_exists_common_root {x y : E} :
    SharesRoot P x y ↔ ∃ r, r ∈ P.rootsOf x ∧ r ∈ P.rootsOf y := Iff.rfl

/-- Sharing a root and being independent are exact complements. -/
theorem not_independent_iff_sharesRoot {x y : E} :
    ¬ Independent P x y ↔ SharesRoot P x y := by
  rw [independent_iff_disjoint_roots, Finset.not_disjoint_iff]
  exact ⟨fun ⟨r, h₁, h₂⟩ => ⟨r, h₁, h₂⟩, fun ⟨r, h₁, h₂⟩ => ⟨r, h₁, h₂⟩⟩

/-- **A shared root blocks an inference of independent replication.**  In the
Agda owner this is a `Bool` field with an equality obligation; here it is a
consequence of the definitions. -/
theorem shared_root_blocks_independent_replication {x y : E} (h : SharesRoot P x y) :
    ¬ Independent P x y := not_independent_iff_sharesRoot.mpr h

theorem independent_symm {x y : E} (h : Independent P x y) : Independent P y x := h.symm

theorem sharesRoot_symm {x y : E} (h : SharesRoot P x y) : SharesRoot P y x := by
  obtain ⟨r, h₁, h₂⟩ := h
  exact ⟨r, h₂, h₁⟩

/-- A unit with any provenance at all is not independent of itself: repeating a
measurement of the same rooted artefact never certifies replication. -/
theorem not_independent_self {x : E} (h : (P.rootsOf x).Nonempty) :
    ¬ Independent P x x := by
  obtain ⟨r, hr⟩ := h
  exact not_independent_iff_sharesRoot.mpr ⟨r, hr, hr⟩

/-- Independence is inherited by units with fewer roots. -/
theorem independent_of_subset {x y x' y' : E}
    (hx : P.rootsOf x' ⊆ P.rootsOf x) (hy : P.rootsOf y' ⊆ P.rootsOf y)
    (h : Independent P x y) : Independent P x' y' :=
  Finset.disjoint_of_subset_left hx (Finset.disjoint_of_subset_right hy h)

/-- **Sharing a root is not transitive**, so the dependence classes of §3 are
not the quotient by this relation: two units can each share a root with a hub
and be independent of each other. -/
theorem sharesRoot_not_transitive :
    ∃ (E R : Type) (_ : DecidableEq R) (P : Provenance E R) (x y z : E),
      SharesRoot P x y ∧ SharesRoot P y z ∧ ¬ SharesRoot P x z := by
  classical
  refine ⟨Fin 3, ℕ, inferInstance,
    ⟨![{0}, {0, 1}, {1}]⟩, 0, 1, 2, ⟨0, by decide, by decide⟩, ⟨1, by decide, by decide⟩, ?_⟩
  rintro ⟨r, hr₀, hr₂⟩
  revert hr₀ hr₂
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, Finset.mem_singleton]
  rintro rfl h
  exact absurd h (by decide)

/-! ## §2 How much independent evidence is actually held -/

section Support

variable [DecidableEq R]

/-- The union of the provenance closures of a list of evidence units. -/
def rootSupport (P : Provenance E R) : List E → Finset R
  | [] => ∅
  | x :: xs => P.rootsOf x ∪ rootSupport P xs

@[simp] theorem rootSupport_nil : rootSupport P ([] : List E) = ∅ := rfl

@[simp] theorem rootSupport_cons (x : E) (xs : List E) :
    rootSupport P (x :: xs) = P.rootsOf x ∪ rootSupport P xs := rfl

theorem roots_subset_rootSupport {x : E} {xs : List E} (h : x ∈ xs) :
    P.rootsOf x ⊆ rootSupport P xs := by
  induction xs with
  | nil => cases h
  | cons a as ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · exact Finset.subset_union_left
      · exact (ih h').trans Finset.subset_union_right

/-- Independent units contribute disjointly: their root supports add. -/
theorem card_roots_union_of_independent {x y : E} (h : Independent P x y) :
    (P.rootsOf x ∪ P.rootsOf y).card = (P.rootsOf x).card + (P.rootsOf y).card :=
  Finset.card_union_of_disjoint h

/-- Dependent units do not: the union is strictly smaller than the sum, so
counting observations overstates the evidence. -/
theorem card_roots_union_lt_of_shared {x y : E} (h : SharesRoot P x y) :
    (P.rootsOf x ∪ P.rootsOf y).card < (P.rootsOf x).card + (P.rootsOf y).card := by
  have hlt : (P.rootsOf x ∩ P.rootsOf y).card ≠ 0 := by
    obtain ⟨r, h₁, h₂⟩ := h
    exact Finset.card_ne_zero_of_mem (Finset.mem_inter.mpr ⟨h₁, h₂⟩)
  have := Finset.card_union_add_card_inter (P.rootsOf x) (P.rootsOf y)
  omega

/-! ### Amplification is not generation -/

/-- Three evidence units resting on a single shared root. -/
def sharedRootFixture : Provenance (Fin 3) ℕ := ⟨fun _ => {0}⟩

/-- Three evidence units resting on three distinct roots. -/
def distinctRootFixture : Provenance (Fin 3) ℕ := ⟨fun i => {(i : ℕ)}⟩

/-- **Amplification is not generation.**  Three units with one root between them
have the same count as three units with three roots. -/
theorem amplification_is_not_generation :
    (rootSupport sharedRootFixture [0, 1, 2]).card = 1 ∧
      (rootSupport distinctRootFixture [0, 1, 2]).card = 3 := by
  constructor <;> decide

/-- **The number of evidence units does not determine the independent root
support.**  Stated as a non-descent through the kernel's collision obstruction:
no function of the observation count computes the size of the provenance
closure. -/
theorem count_does_not_determine_root_support :
    ¬ DescendsThrough
        (fun p : Provenance (Fin 3) ℕ × List (Fin 3) => (rootSupport p.1 p.2).card)
        (fun p : Provenance (Fin 3) ℕ × List (Fin 3) => p.2.length) :=
  not_descendsThrough_of_collision
    (x := (sharedRootFixture, [0, 1, 2])) (y := (distinctRootFixture, [0, 1, 2]))
    rfl (by decide)

end Support

/-! ## §3 Dependence classes and two-stage aggregation

Because `SharesRoot` is not transitive (`sharesRoot_not_transitive`), a
dependence class assignment is extra data.  The discipline that makes the
two-stage aggregation "within class, then across classes" sound is exactly
`ClassSeparates`: the class map must never separate two units that share a
root. -/

variable {K : Type w}

/-- A class map is *dependence-respecting* when any two units sharing a root
land in the same class. -/
def ClassSeparates (P : Provenance E R) (cls : E → K) : Prop :=
  ∀ x y, SharesRoot P x y → cls x = cls y

/-- **Across-class aggregation aggregates independent evidence.**  Under a
dependence-respecting class map, units in different classes are provably
independent — this is what licenses treating class aggregates as independent
summands. -/
theorem independent_of_different_class {cls : E → K} (h : ClassSeparates P cls)
    {x y : E} (hxy : cls x ≠ cls y) : Independent P x y := by
  by_contra hind
  exact hxy (h x y (not_independent_iff_sharesRoot.mp hind))

/-- Within a class nothing is claimed: the same hypothesis is consistent with
two units in one class being dependent *or* independent, which is why the
within-class aggregation rule has to be supplied separately. -/
theorem class_agreement_is_not_dependence :
    ∃ (P : Provenance (Fin 2) ℕ) (cls : Fin 2 → Unit),
      ClassSeparates P cls ∧ Independent P 0 1 := by
  refine ⟨⟨fun i => {(i : ℕ)}⟩, fun _ => (), fun _ _ _ => rfl, ?_⟩
  refine Finset.disjoint_left.mpr ?_
  intro a ha hb
  rw [Finset.mem_singleton] at ha hb
  subst ha
  exact absurd hb (by decide)

/-- A dependence-respecting class map is a coarser reading of provenance: the
class coordinate descends through the root-set coordinate whenever the roots
determine the class. -/
theorem class_descends_of_roots_determine [Nonempty K] {cls : E → K}
    (h : ∀ x y, P.rootsOf x = P.rootsOf y → cls x = cls y) :
    DescendsThrough cls P.rootsOf :=
  (descendsThrough_iff_refinedBy cls P.rootsOf).mpr h

end Integration.Kernel.EvidenceDependence
