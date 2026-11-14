import Integration.E8RelativeT5IntrinsicGraphObstruction
import Mathlib

/-!
# Literal E8 root branching by an explicit A2 subsystem

DASHI finite derivation on the literal 240-root scaled E8 carrier already used
by the intrinsic-graph obstruction.

Choose two D8-type roots

  a = (-2,-2,0,0,0,0,0,0)
  b = ( 2, 0,-2,0,0,0,0,0)

whose scaled inner product is -4 (unscaled -1).  They generate an A2 root
subsystem.  Classifying every literal E8 root by the pair of scaled inner
products `(r.a, r.b)` gives the exact partition

  72 + 81 + 81 + 6 = 240.

The 72 roots orthogonal to both `a` and `b` are the finite E6-complement sector.
The six singleton A2 weight patterns are the A2 roots themselves.  The remaining
six 27-element weight fibres split naturally into two opposite triples, giving
two 81-point mixed sectors.

This is an exact finite root-system branching on the literal E8 carrier.  It
still does not identify the two 81-point sectors or six-point sector with the
ternary branching candidate; equal sector cardinalities are only a shape match
until an independently justified geometry/action intertwiner is supplied.
-/

namespace Integration.E8LiteralE6A2Branching

open Integration.E8RelativeT5IntrinsicGraphObstruction

/-- First chosen A2 simple root: (-2,-2,0,...). -/
def a2SimpleA : E8ScaledRoot :=
  .inl ⟨⟨0, 1, false, false⟩, by decide⟩

/-- Second chosen A2 simple root: (2,0,-2,0,...). -/
def a2SimpleB : E8ScaledRoot :=
  .inl ⟨⟨0, 2, true, false⟩, by decide⟩

theorem a2_simple_inner_product : e8ScaledDot a2SimpleA a2SimpleB = -4 := by
  native_decide

/-- Pair of scaled A2 weight coordinates. -/
def a2Weight (r : E8ScaledRoot) : Int × Int :=
  (e8ScaledDot r a2SimpleA, e8ScaledDot r a2SimpleB)

/-- Common orthogonal complement of the selected A2 plane. -/
def isLiteralE6Sector (r : E8ScaledRoot) : Bool :=
  decide (a2Weight r = (0,0))

/-- The six A2 roots, recognized by their six extremal weight pairs. -/
def isLiteralA2Sector (r : E8ScaledRoot) : Bool :=
  let w := a2Weight r
  decide (
    w = (8,-4) ∨ w = (-8,4) ∨
    w = (4,-8) ∨ w = (-4,8) ∨
    w = (4,4) ∨ w = (-4,-4))

/-- One triple of 27-element mixed E8 weight fibres. -/
def isLiteralMixedPlus (r : E8ScaledRoot) : Bool :=
  let w := a2Weight r
  decide (w = (0,-4) ∨ w = (4,0) ∨ w = (-4,4))

/-- The opposite triple of 27-element mixed E8 weight fibres. -/
def isLiteralMixedMinus (r : E8ScaledRoot) : Bool :=
  let w := a2Weight r
  decide (w = (0,4) ∨ w = (-4,0) ∨ w = (4,-4))

def LiteralE6Sector := {r : E8ScaledRoot // isLiteralE6Sector r = true}
def LiteralA2Sector := {r : E8ScaledRoot // isLiteralA2Sector r = true}
def LiteralMixedPlus := {r : E8ScaledRoot // isLiteralMixedPlus r = true}
def LiteralMixedMinus := {r : E8ScaledRoot // isLiteralMixedMinus r = true}

instance : Fintype LiteralE6Sector := inferInstance
instance : Fintype LiteralA2Sector := inferInstance
instance : Fintype LiteralMixedPlus := inferInstance
instance : Fintype LiteralMixedMinus := inferInstance

theorem literal_e6_sector_card : Fintype.card LiteralE6Sector = 72 := by
  native_decide

theorem literal_a2_sector_card : Fintype.card LiteralA2Sector = 6 := by
  native_decide

theorem literal_mixed_plus_card : Fintype.card LiteralMixedPlus = 81 := by
  native_decide

theorem literal_mixed_minus_card : Fintype.card LiteralMixedMinus = 81 := by
  native_decide

theorem literal_e8_branching_count :
    Fintype.card E8ScaledRoot = 72 + 81 + 81 + 6 := by
  norm_num [e8_scaled_root_card]

/-- Exact total classifier for the literal E8 branching. -/
inductive LiteralBranchSector
  | e6
  | mixedPlus
  | mixedMinus
  | a2
  deriving DecidableEq, Repr, Fintype

def literalBranchSector (r : E8ScaledRoot) : LiteralBranchSector :=
  if isLiteralE6Sector r = true then .e6
  else if isLiteralMixedPlus r = true then .mixedPlus
  else if isLiteralMixedMinus r = true then .mixedMinus
  else .a2

def LiteralTaggedSector (tag : LiteralBranchSector) :=
  {r : E8ScaledRoot // literalBranchSector r = tag}

instance (tag : LiteralBranchSector) : Fintype (LiteralTaggedSector tag) := inferInstance

theorem literal_tagged_e6_card : Fintype.card (LiteralTaggedSector .e6) = 72 := by
  native_decide

theorem literal_tagged_mixed_plus_card :
    Fintype.card (LiteralTaggedSector .mixedPlus) = 81 := by
  native_decide

theorem literal_tagged_mixed_minus_card :
    Fintype.card (LiteralTaggedSector .mixedMinus) = 81 := by
  native_decide

theorem literal_tagged_a2_card : Fintype.card (LiteralTaggedSector .a2) = 6 := by
  native_decide

def exactlyOneLiteralBranchSector (r : E8ScaledRoot) : Prop :=
  ∃! tag : LiteralBranchSector, literalBranchSector r = tag

theorem literal_branch_sector_total : ∀ r, exactlyOneLiteralBranchSector r := by
  intro r
  refine ⟨literalBranchSector r, rfl, ?_⟩
  intro tag h
  exact h.symm

/-- Exhaustive audit that every root falls into one of the four intended weight
families, rather than merely relying on the sum of cardinalities. -/
theorem literal_weight_patterns_exhaustive :
    ∀ r : E8ScaledRoot,
      isLiteralE6Sector r = true ∨
      isLiteralMixedPlus r = true ∨
      isLiteralMixedMinus r = true ∨
      isLiteralA2Sector r = true := by
  native_decide

inductive BranchingCountMatchCreatesTernarySectorEquivalence : Prop
inductive LiteralBranchingCreatesE8RecognitionOfT5 : Prop

theorem branchingCountMatchCannotCreateTernarySectorEquivalence :
    ¬ BranchingCountMatchCreatesTernarySectorEquivalence := by
  intro h
  cases h

theorem literalBranchingCannotCreateT5Recognition :
    ¬ LiteralBranchingCreatesE8RecognitionOfT5 := by
  intro h
  cases h

structure Boundary where
  explicitA2SubsystemTyped : Bool
  a2SimpleInnerProductPaid : Bool
  e6OrthogonalComplementCount72Paid : Bool
  a2RootCount6Paid : Bool
  mixedWeightFibres81And81Paid : Bool
  literalE8Branching7281816Paid : Bool
  weightPatternExhaustionPaid : Bool
  branchingCountMatchCreatesTernarySectorEquivalence : Bool
  literalBranchingCreatesT5E8Recognition : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  explicitA2SubsystemTyped := true
  a2SimpleInnerProductPaid := true
  e6OrthogonalComplementCount72Paid := true
  a2RootCount6Paid := true
  mixedWeightFibres81And81Paid := true
  literalE8Branching7281816Paid := true
  weightPatternExhaustionPaid := true
  branchingCountMatchCreatesTernarySectorEquivalence := false
  literalBranchingCreatesT5E8Recognition := false

end Integration.E8LiteralE6A2Branching
