import Lean

/-!
P0 canonical numeric-PNF owner/reducer semantics.

This is a literal Lean reference for the original SensibLaw Python
four-key fibre partition and FIRST-compatible role merge. It rules out
a "parallel associative fold" shortcut within a single owner.

The implementation correspondence still needs kernel-checked concrete
Rust/strict-reference receipts. This file does not assert that any Rust
binary has been compiled or certified.
-/

namespace Wikidata.Slr.NumericPnfCanonicalReducer

structure OwnerKey where
  semanticCoordinate : String
  fibreKind : String
  factorType : String
  structuralSignature : String
  deriving Repr, BEq, DecidableEq

structure RoleBinding where
  roleRef : String
  valueRef : String
  deriving Repr, BEq, DecidableEq

structure Proposal where
  proposalRef : String
  owner : OwnerKey
  roles : List RoleBinding
  provenanceRefs : List String
  deriving Repr, BEq, DecidableEq

structure Group where
  proposalRefs : List String
  occupiedRoles : List RoleBinding
  deriving Repr, BEq, DecidableEq

def roleAt (roles : List RoleBinding) (key : String) : Option String :=
  (roles.find? (fun r => r.roleRef == key)).map RoleBinding.valueRef

def compatible (occupied incoming : List RoleBinding) : Bool :=
  incoming.all fun pair =>
    match roleAt occupied pair.roleRef with
    | none => true
    | some old => old == pair.valueRef

def mergeRoles (occupied incoming : List RoleBinding) : List RoleBinding :=
  incoming.foldl (fun acc pair =>
    match roleAt acc pair.roleRef with
    | some _ => acc
    | none => acc ++ [pair]) occupied

def freshGroup (p : Proposal) : Group :=
  { proposalRefs := [p.proposalRef], occupiedRoles := p.roles }

/-- The exact first-compatible rule. No same-owner reordering theorem follows. -/
def insertFirst : List Group → Proposal → List Group
  | [], p => [freshGroup p]
  | g :: rest, p =>
      if compatible g.occupiedRoles p.roles then
        { proposalRefs := g.proposalRefs ++ [p.proposalRef],
          occupiedRoles := mergeRoles g.occupiedRoles p.roles } :: rest
      else
        g :: insertFirst rest p

/-- Input must already be ordered by the original canonical proposal-ref
    contract. The sorted-input obligation is checked outside this model. -/
def reduceOwnerCanonical (ordered : List Proposal) (owner : OwnerKey) : List Group :=
  ((ordered.filter fun p => p.owner == owner)).foldl insertFirst []

theorem first_compatible_group_is_selected
    (g : Group) (rest : List Group) (p : Proposal)
    (h : compatible g.occupiedRoles p.roles = true) :
    insertFirst (g :: rest) p =
      { proposalRefs := g.proposalRefs ++ [p.proposalRef],
        occupiedRoles := mergeRoles g.occupiedRoles p.roles } :: rest := by
  simp [insertFirst, h]

theorem incompatible_first_group_is_preserved
    (g : Group) (rest : List Group) (p : Proposal)
    (h : compatible g.occupiedRoles p.roles = false) :
    insertFirst (g :: rest) p = g :: insertFirst rest p := by
  simp [insertFirst, h]

/-- Unrelated owner proposals cannot change this owner's grouping.
    This is NOT a theorem about arbitrary same-owner reordering. -/
theorem unrelated_owner_prefix_is_irrelevant
    (prefix ordered : List Proposal) (owner : OwnerKey)
    (outside :
      (prefix.filter fun p => p.owner == owner) = []) :
    reduceOwnerCanonical (prefix ++ ordered) owner =
      reduceOwnerCanonical ordered owner := by
  simp [reduceOwnerCanonical, List.filter_append, outside]

def testOwner : OwnerKey :=
  { semanticCoordinate := "source:sentence:23",
    fibreKind := "hypothesis",
    factorType := "source-local-antecedent",
    structuralSignature := "pronoun:third-person-singular" }

def subject (value : String) : List RoleBinding :=
  [{ roleRef := "subject", valueRef := value }]

def annot (name : String) : Proposal :=
  { proposalRef := name, owner := testOwner,
    roles := subject name, provenanceRefs := ["original-source"] }

def noRole (ref : String) : Proposal :=
  { proposalRef := ref, owner := testOwner,
    roles := [], provenanceRefs := ["original-source"] }

/-- A concrete counterexample: when two incompatible local subjects are
    seen first, the later unconstrained proposal attaches to the FIRST
    of them. Reversing same-owner order changes its assignment. -/
theorem same_owner_reordering_is_not_generally_safe :
    reduceOwnerCanonical
      [annot "Bush", annot "Reagan", noRole "unconstrained"] testOwner
    ≠
    reduceOwnerCanonical
      [annot "Reagan", annot "Bush", noRole "unconstrained"] testOwner := by
  decide

inductive BalancedSign where
  | negative
  | zero
  | positive
  deriving Repr, BEq, DecidableEq

structure IndexedFibre where
  timeIndex : Nat
  scaleIndex : Nat
  sign : BalancedSign
  zeroMode : Bool
  residualRefs : List String
  sourceRevision : String
  deriving Repr, BEq, DecidableEq

def forgetSign (f : IndexedFibre) : Nat × Nat × Bool × List String × String :=
  (f.timeIndex, f.scaleIndex, f.zeroMode, f.residualRefs, f.sourceRevision)

/-- Two sign assignments collide for an observer that forgets ternary sign:
    only an explicitly sign-aware consumer can distinguish them. -/
theorem forgetting_sign_has_an_exact_observer_collision :
  forgetSign {
    timeIndex := 23, scaleIndex := 9, sign := .negative,
    zeroMode := true, residualRefs := ["ambiguous-anaphor"],
    sourceRevision := "book:original"
  } =
  forgetSign {
    timeIndex := 23, scaleIndex := 9, sign := .positive,
    zeroMode := true, residualRefs := ["ambiguous-anaphor"],
    sourceRevision := "book:original"
  } := rfl

end Wikidata.Slr.NumericPnfCanonicalReducer

#print axioms Wikidata.Slr.NumericPnfCanonicalReducer.first_compatible_group_is_selected
#print axioms Wikidata.Slr.NumericPnfCanonicalReducer.incompatible_first_group_is_preserved
#print axioms Wikidata.Slr.NumericPnfCanonicalReducer.unrelated_owner_prefix_is_irrelevant
#print axioms Wikidata.Slr.NumericPnfCanonicalReducer.same_owner_reordering_is_not_generally_safe
#print axioms Wikidata.Slr.NumericPnfCanonicalReducer.forgetting_sign_has_an_exact_observer_collision
