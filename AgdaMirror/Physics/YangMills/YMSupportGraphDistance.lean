import AgdaMirror.Physics.YangMills.YMSourceAuthoritySurface

/-!
Lean mirror of the lightweight graph-distance portion of
`YMSupportGraphDistance.agda`.

Every Agda postulate is collected in `ImportedGraphData`; all downstream
conclusions are functions of an explicit value of that structure.  Thus this
file proves only the structural consequences, not the imported graph facts.
-/
namespace AgdaMirror.Physics.YangMills.YMSupportGraphDistance

open YMSourceAuthoritySurface

structure FiniteSupportGraph where
  Vertex : Type
  Edge : Type
  supportEdge : Edge → Bool
  treeEdge : Edge → Bool
  treeEdgesSubsetSupportEdges : ∀ {e}, treeEdge e = true → supportEdge e = true

structure Path (G : FiniteSupportGraph) where
  start : G.Vertex
  finish : G.Vertex
  edges : List G.Edge
  valid : Bool
  pathLength : Nat
  pathLengthMatchesEdges : pathLength = edges.length

structure GraphDistanceStructure (G : FiniteSupportGraph) where
  graphDist : G.Vertex → G.Vertex → Nat
  graphDistMinimality : ∀ {u v} (p : Path G), p.start = u → p.finish = v →
    p.valid = true → graphDist u v ≤ p.pathLength

structure TreePathStructure (G : FiniteSupportGraph) where
  treePath : G.Vertex → G.Vertex → Path G
  treeEdgeCount : Nat
  treePathStart : ∀ u v, (treePath u v).start = u
  treePathFinish : ∀ u v, (treePath u v).finish = v
  treePathValid : ∀ u v, (treePath u v).valid = true
  treePathBoundedByEdgeCount : ∀ u v, (treePath u v).pathLength ≤ treeEdgeCount

def treePathLength {G} (tp : TreePathStructure G) (u v : G.Vertex) : Nat :=
  (tp.treePath u v).pathLength

theorem treePathDominatesGraphPath {G} (gd : GraphDistanceStructure G)
    (tp : TreePathStructure G) (u v : G.Vertex) :
    gd.graphDist u v ≤ treePathLength tp u v :=
  gd.graphDistMinimality (tp.treePath u v) (tp.treePathStart u v)
    (tp.treePathFinish u v) (tp.treePathValid u v)

theorem treeSizeDominatesTreePath {G} (tp : TreePathStructure G)
    (u v : G.Vertex) : treePathLength tp u v ≤ tp.treeEdgeCount :=
  tp.treePathBoundedByEdgeCount u v

/-- Exact hypothesis boundary corresponding to the Agda graph postulates. -/
structure ImportedGraphData where
  Link : Type
  supportEdge : Link → Bool
  treeEdge : Link → Bool
  treeEdgesSubsetSupportEdges : ∀ {e}, treeEdge e = true → supportEdge e = true
  graphDist : Link → Link → Nat
  treePath : (u v : Link) → Path
    { Vertex := Link, Edge := Link, supportEdge := supportEdge,
      treeEdge := treeEdge, treeEdgesSubsetSupportEdges := treeEdgesSubsetSupportEdges }
  treeEdgeCount : Nat
  treePathStart : ∀ u v, (treePath u v).start = u
  treePathFinish : ∀ u v, (treePath u v).finish = v
  treePathValid : ∀ u v, (treePath u v).valid = true
  graphDistMinimality : ∀ {u v} (p : Path
    { Vertex := Link, Edge := Link, supportEdge := supportEdge,
      treeEdge := treeEdge, treeEdgesSubsetSupportEdges := treeEdgesSubsetSupportEdges }),
    p.start = u → p.finish = v → p.valid = true → graphDist u v ≤ p.pathLength
  treePathBoundedByEdgeCount : ∀ u v, (treePath u v).pathLength ≤ treeEdgeCount

def currentFiniteSupportGraph (d : ImportedGraphData) : FiniteSupportGraph :=
  { Vertex := d.Link, Edge := d.Link, supportEdge := d.supportEdge,
    treeEdge := d.treeEdge, treeEdgesSubsetSupportEdges := d.treeEdgesSubsetSupportEdges }

def currentGraphDistanceStructure (d : ImportedGraphData) :
    GraphDistanceStructure (currentFiniteSupportGraph d) :=
  { graphDist := d.graphDist, graphDistMinimality := d.graphDistMinimality }

def currentTreePathStructure (d : ImportedGraphData) :
    TreePathStructure (currentFiniteSupportGraph d) :=
  { treePath := d.treePath, treeEdgeCount := d.treeEdgeCount,
    treePathStart := d.treePathStart, treePathFinish := d.treePathFinish,
    treePathValid := d.treePathValid,
    treePathBoundedByEdgeCount := d.treePathBoundedByEdgeCount }

structure TreePathEdgesExistWitness (d : ImportedGraphData) (u v : d.Link) where
  path : Path (currentFiniteSupportGraph d)
  startAtSource : path.start = u
  finishAtTarget : path.finish = v
  validPath : path.valid = true

def treePathEdgesExistPathWitness (d : ImportedGraphData) (u v : d.Link) :
    TreePathEdgesExistWitness d u v :=
  { path := d.treePath u v, startAtSource := d.treePathStart u v,
    finishAtTarget := d.treePathFinish u v, validPath := d.treePathValid u v }

theorem graphDistMinimalityFromWitness (d : ImportedGraphData) (u v : d.Link) :
    d.graphDist u v ≤ (d.treePath u v).pathLength :=
  d.graphDistMinimality (d.treePath u v) (d.treePathStart u v)
    (d.treePathFinish u v) (d.treePathValid u v)

structure GraphCoreP01P02P03TheoremSurface (d : ImportedGraphData) where
  p01TreePathEdgesExistSurface : ∀ (_u _v : d.Link), Path (currentFiniteSupportGraph d)
  p02GraphDistMinimalitySurface : ∀ u v : d.Link,
    d.graphDist u v ≤ (p01TreePathEdgesExistSurface u v).pathLength
  p03TreePathBoundedByEdgeCountSurface : ∀ u v : d.Link,
    (p01TreePathEdgesExistSurface u v).pathLength ≤ d.treeEdgeCount

def currentGraphCoreP01P02P03TheoremSurface (d : ImportedGraphData) :
    GraphCoreP01P02P03TheoremSurface d :=
  { p01TreePathEdgesExistSurface := d.treePath,
    p02GraphDistMinimalitySurface := graphDistMinimalityFromWitness d,
    p03TreePathBoundedByEdgeCountSurface := d.treePathBoundedByEdgeCount }

structure ImportedTreePathEdgesExist (d : ImportedGraphData) where
  sourceAuthorityId : SourceAuthorityId
  theoremLocator : String
  status : VerificationStatus
  pathExist : ∀ (_u _v : d.Link), Path (currentFiniteSupportGraph d)

structure ImportedGraphDistMinimality (d : ImportedGraphData) where
  sourceAuthorityId : SourceAuthorityId
  theoremLocator : String
  status : VerificationStatus
  minimality : ∀ u v : d.Link, ∀ p : Path (currentFiniteSupportGraph d),
    p.start = u → p.finish = v → p.valid = true → d.graphDist u v ≤ p.pathLength

structure ImportedTreePathBoundedByEdgeCount (d : ImportedGraphData) where
  sourceAuthorityId : SourceAuthorityId
  theoremLocator : String
  status : VerificationStatus
  bounded : ∀ u v : d.Link, (d.treePath u v).pathLength ≤ d.treeEdgeCount

def treePathEdgesExistWitness (d : ImportedGraphData) : ImportedTreePathEdgesExist d :=
  ⟨.diestelGraphTheory, "§1.5.1", .standardWrapper, d.treePath⟩

def graphDistMinimalityWitness (d : ImportedGraphData) : ImportedGraphDistMinimality d :=
  ⟨.diestelGraphTheory, "§1.5.1", .standardWrapper,
    fun _ _ p hs hf hv => d.graphDistMinimality p hs hf hv⟩

def treePathBoundedByEdgeCountWitness (d : ImportedGraphData) :
    ImportedTreePathBoundedByEdgeCount d :=
  ⟨.diestelGraphTheory, "§1.5.1", .standardWrapper, d.treePathBoundedByEdgeCount⟩

end AgdaMirror.Physics.YangMills.YMSupportGraphDistance
