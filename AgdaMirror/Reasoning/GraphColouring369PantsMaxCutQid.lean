/-!
# Native 27-grid weighted maximum cut and QID provenance — Lean mirror

Golden mathematical owner:
  DASHI.Combinatorics.GraphColouring369PantsWeightedMaxCutExact
Golden QID owner:
  DASHI.Combinatorics.GraphColouring369PantsQidParetoSnowballExact

Reuses existing Lean native 27-grid adjacency and 2-colour checkerboard.
All Nat edge weights are nonnegative. Every native adjacency edge crosses
the checkerboard and therefore every finite graph-edge list is saturated:
a universal maximum cut, not merely a sampled optimization.

The exact 54 unit edges are constructed in Agda; this mirror does not
pretend it has a kernel-proved 54-edge enumeration until mirrored.

Concept QIDs inspected on Wikidata 30 Oct 2026: Q131476 Q1137726
Q727035 Q504843 Q174733 Q303100 Q3385162 Q942557 Q840247 Q184410.
They provide navigation/identity only. QID does not prove anything about
the particular DASHI finite fixture, Monster3B or smooth pants.
-/
import Mathlib
import AgdaMirror.Reasoning.GraphColouring369PantsGridAdjacency

namespace AgdaMirror.Reasoning.GraphColouring369PantsMaxCutQid

open AgdaMirror.Reasoning.GraphColouring369PantsGridAdjacency

abbrev Partition := Voxel → Bool

structure NativeWeightedEdge where
  source : Voxel
  target : Voxel
  nativeAdjacency : VoxelAdjacent source target
  weight : Nat

def edgeScore (partition : Partition) (e : NativeWeightedEdge) : Nat :=
  if partition e.source = partition e.target then 0 else e.weight

def cutWeight (partition : Partition) : List NativeWeightedEdge → Nat
  | [] => 0
  | e :: es => edgeScore partition e + cutWeight partition es

def totalWeight : List NativeWeightedEdge → Nat
  | [] => 0
  | e :: es => e.weight + totalWeight es

theorem edgeScore_le (partition : Partition) (e : NativeWeightedEdge) :
    edgeScore partition e ≤ e.weight := by
  unfold edgeScore
  split <;> omega

theorem cutWeight_le_total (partition : Partition)
    (edges : List NativeWeightedEdge) :
    cutWeight partition edges ≤ totalWeight edges := by
  induction edges with
  | nil => exact Nat.le_refl 0
  | cons edge rest ih =>
    simp only [cutWeight, totalWeight]
    exact Nat.add_le_add (edgeScore_le partition edge) ih

theorem checkerCutsEveryEdge (e : NativeWeightedEdge) :
    checkerboard e.source ≠ checkerboard e.target :=
  checkerboard_proper e.nativeAdjacency

theorem checkerEdgeFull (e : NativeWeightedEdge) :
    edgeScore checkerboard e = e.weight := by
  simp [edgeScore, checkerCutsEveryEdge e]

theorem checkerCutIsFull (edges : List NativeWeightedEdge) :
    cutWeight checkerboard edges = totalWeight edges := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    simp only [cutWeight, totalWeight]
    rw [checkerEdgeFull, ih]

theorem checkerMaximumCut (edges : List NativeWeightedEdge)
    (competitor : Partition) :
    cutWeight competitor edges ≤ cutWeight checkerboard edges := by
  rw [checkerCutIsFull]
  exact cutWeight_le_total competitor edges

/-- Native pants paths inherit the saturated finite cut through the exact
voxel/path graph isomorphism; no smooth cobordism is inferred. -/
def pantsPartition (path : PantsPath3) : Bool :=
  checkerboard (pantsToVoxel path)

theorem pantsEdgesAllCut {p q : PantsPath3}
    (edge : PantsAdjacent p q) :
    pantsPartition p ≠ pantsPartition q :=
  checkerboard_proper (pants_to_voxel_preserves edge)

inductive QidResolution
  | verified (id : String)
  | candidate (id : String)
  | unresolved (reason : String)
  deriving Repr, DecidableEq

structure ConceptCoordinate where
  concept : String
  qid : QidResolution
  conceptOnly : Bool

def verifiedConcept (label id : String) : ConceptCoordinate :=
  ⟨label, QidResolution.verified id, true⟩

def graphTheory : ConceptCoordinate := verifiedConcept "graph theory" "Q131476"
def directedGraph : ConceptCoordinate := verifiedConcept "directed graph" "Q1137726"
def adjacencyMatrix : ConceptCoordinate := verifiedConcept "adjacency matrix" "Q727035"
def graphColouring : ConceptCoordinate := verifiedConcept "graph coloring" "Q504843"
def bipartiteGraph : ConceptCoordinate := verifiedConcept "bipartite graph" "Q174733"
def graphIsomorphism : ConceptCoordinate := verifiedConcept "graph isomorphism" "Q303100"
def graphHomomorphism : ConceptCoordinate := verifiedConcept "graph homomorphism" "Q3385162"
def maximumCut : ConceptCoordinate := verifiedConcept "maximum cut" "Q942557"
def hypergraph : ConceptCoordinate := verifiedConcept "hypergraph" "Q840247"
def fourColourTheorem : ConceptCoordinate := verifiedConcept "four color theorem" "Q184410"

def selectedFiniteGraph : ConceptCoordinate :=
  ⟨"DASHI selected finite pants/voxel graph",
   QidResolution.unresolved "no verified distinct Wikidata item", true⟩

theorem selectedFixtureQidUnresolved :
    selectedFiniteGraph.qid =
      QidResolution.unresolved "no verified distinct Wikidata item" := rfl

/-- A verified concept ID never entails a theorem or a Monster representation:
these propositions are kept separate, with no arbitrary bridge provided. -/
structure SourceAuthorityBoundary where
  qidCreatesKernelProof : Bool
  exactSameMonster3BObjectDerived : Bool
  finitePantsPathIsSmooth : Bool
  finiteSelectedCutSourceWritten : Bool
  checkedGoldenKernel : Bool

def canonicalBoundary : SourceAuthorityBoundary :=
  ⟨false, false, false, true, false⟩


/-- Typed roles are distinct: the same QID navigation syntax does NOT
    identify a discipline, a directed graph, a problem, or a proof. -/
inductive KnowledgeRole where
  | discipline | graphStructure | graphClass | representation
  | graphMorphism | computationalProblem | higherArity | theorem
  deriving DecidableEq, Repr

structure TypedConcept (role : KnowledgeRole) where
  identity : ConceptCoordinate
  note : String

def typedGraphTheory : TypedConcept .discipline :=
  ⟨graphTheory, "graph theory field, not a graph fixture"⟩
def typedDirectedGraph : TypedConcept .graphStructure :=
  ⟨directedGraph, "directed edge graph"⟩
def typedAdjacency : TypedConcept .representation :=
  ⟨adjacencyMatrix, "matrix representation, not same object"⟩
def typedGraphIsomorphism : TypedConcept .graphMorphism :=
  ⟨graphIsomorphism, "preserved native adjacency"⟩
def typedGraphHomomorphism : TypedConcept .graphMorphism :=
  ⟨graphHomomorphism, "edge preserving map"⟩
def typedMaximumCut : TypedConcept .computationalProblem :=
  ⟨maximumCut, "the cut optimization problem"⟩
def typedHypergraph : TypedConcept .higherArity :=
  ⟨hypergraph, "not a dyadic directed graph"⟩
def typedFourColourTheorem : TypedConcept .theorem :=
  ⟨fourColourTheorem, "a theorem distinct from the 2026 publication"⟩

def directedGraphDewey : String := "511.54"
def graphTheoryDewey : String := "511.5"

theorem directedAndGeneralDeweyDistinct :
    directedGraphDewey ≠ graphTheoryDewey := by decide

end AgdaMirror.Reasoning.GraphColouring369PantsMaxCutQid
