import Integration.T5E8RelativeComplementCandidate
import Mathlib

/-!
# Intrinsic graph obstruction for the naive T5/E8 recognition

DASHI finite no-go for one *specific* proposed intrinsic geometry.

Local Python preflight constructed the standard 240 E8 roots in scaled integer
coordinates and checked that the root-addition adjacency

  alpha ~ beta  iff  <alpha,beta> = -1

is 56-regular.  In the scaled coordinates below this is dot product `-4`.

On the repository's 240-state non-diagonal five-trit carrier, the most immediate
balanced-ternary orthogonality graph

  x ~ y  iff  x != y and <x,y> = 0 in F3

is not 56-regular: the explicit witness `(0,0,1,1,1)` has degree 77 (and Python
finds degrees 77,78,79,80 across the carrier).

Therefore no recognition preserving these two *pre-existing* adjacency notions
can exist.  This does not rule out every possible T5/E8 recognition; it rules
out the naive standard-F3 orthogonality graph and demonstrates why an intrinsic
target geometry must be fixed before transporting an E8 action through a
bijection.
-/

namespace Integration.E8RelativeT5IntrinsicGraphObstruction

open Integration.TernaryHub
open Integration.TrialecticDyadicLocalComplement
open Integration.T5E8RelativeComplementCandidate

/-! ## 1. Literal 240-root E8 carrier in scaled integer coordinates -/

structure D8RootData where
  i : Fin 8
  j : Fin 8
  signI : Bool
  signJ : Bool
  deriving DecidableEq, Repr, Fintype

/-- The 112 roots with two nonzero coordinates `+-2` after scaling E8 roots by 2. -/
def D8Root := {r : D8RootData // r.i < r.j}
instance : Fintype D8Root := inferInstance

/-- Sign vectors for the 128 half-integral roots, represented after scaling by 2. -/
def halfAdmissible (s : Fin 8 → Bool) : Bool :=
  decide (((Finset.univ.filter fun i => s i = false).card % 2) = 0)

def HalfE8Root := {s : Fin 8 → Bool // halfAdmissible s = true}
instance : Fintype HalfE8Root := inferInstance

/-- Exact finite E8 root carrier: 112 D8-type plus 128 half-type roots. -/
def E8ScaledRoot := D8Root ⊕ HalfE8Root
instance : Fintype E8ScaledRoot := inferInstance

def signTwo (b : Bool) : Int := if b then 2 else -2
def signOne (b : Bool) : Int := if b then 1 else -1

def d8Coord (r : D8Root) (k : Fin 8) : Int :=
  if k = r.1.i then signTwo r.1.signI
  else if k = r.1.j then signTwo r.1.signJ
  else 0

def halfCoord (r : HalfE8Root) (k : Fin 8) : Int := signOne (r.1 k)

def e8Coord : E8ScaledRoot → Fin 8 → Int
  | .inl r => d8Coord r
  | .inr r => halfCoord r

def e8ScaledDot (a b : E8ScaledRoot) : Int :=
  ∑ k : Fin 8, e8Coord a k * e8Coord b k

theorem e8_scaled_root_card : Fintype.card E8ScaledRoot = 240 := by
  native_decide

/-- Root-addition adjacency: for norm-2 E8 roots, `alpha + beta` is a root
exactly when the unscaled inner product is -1, i.e. scaled dot product -4. -/
def E8RootNeighbor (r : E8ScaledRoot) :=
  {s : E8ScaledRoot // s ≠ r ∧ e8ScaledDot r s = -4}

instance (r : E8ScaledRoot) : Fintype (E8RootNeighbor r) := inferInstance

theorem e8_root_graph_degree :
    ∀ r : E8ScaledRoot, Fintype.card (E8RootNeighbor r) = 56 := by
  native_decide

/-! ## 2. The naive intrinsic balanced-ternary orthogonality graph -/

/-- Standard F3 dot product on the exact T5 balanced coordinates. -/
def t5Dot : T5Carrier → T5Carrier → ZMod 3
  | ⟨a0,a1,a2,a3,a4⟩, ⟨b0,b1,b2,b3,b4⟩ =>
      balSSP a0 * balSSP b0 +
      balSSP a1 * balSSP b1 +
      balSSP a2 * balSSP b2 +
      balSSP a3 * balSSP b3 +
      balSSP a4 * balSSP b4

/-- Orthogonality neighbors inside the actual non-diagonal 240-state carrier. -/
def RelativeOrthogonalNeighbor (x : RelativeT5Carrier) :=
  {y : RelativeT5Carrier // y ≠ x ∧ t5Dot x.1 y.1 = 0}

instance (x : RelativeT5Carrier) : Fintype (RelativeOrthogonalNeighbor x) := inferInstance

/-- Explicit target witness `(0,0,1,1,1)`, which is non-diagonal. -/
def ternaryWitness : RelativeT5Carrier :=
  ⟨⟨.zero, .zero, .posOne, .posOne, .posOne⟩, by native_decide⟩

theorem ternary_witness_orthogonal_degree :
    Fintype.card (RelativeOrthogonalNeighbor ternaryWitness) = 77 := by
  native_decide

/-! ## 3. No adjacency-preserving same-object recognition for these graphs -/

/-- Recognition contract with the target graph fixed *before* the equivalence.
The degree-preservation field is a necessary consequence of any genuine graph
isomorphism and is kept explicit to make the obstruction small and auditable. -/
structure IntrinsicGraphRecognition : Prop where
  rootEquiv : E8ScaledRoot ≃ RelativeT5Carrier
  neighborCardinalityPreserved :
    ∀ r : E8ScaledRoot,
      Fintype.card (E8RootNeighbor r) =
        Fintype.card (RelativeOrthogonalNeighbor (rootEquiv r))

 theorem intrinsic_graph_recognition_impossible : ¬ IntrinsicGraphRecognition := by
  intro recognition
  let r := recognition.rootEquiv.symm ternaryWitness
  have h := recognition.neighborCardinalityPreserved r
  have hE8 : Fintype.card (E8RootNeighbor r) = 56 := e8_root_graph_degree r
  have hT5 :
      Fintype.card (RelativeOrthogonalNeighbor (recognition.rootEquiv r)) = 77 := by
    simpa [r] using ternary_witness_orthogonal_degree
  rw [hE8, hT5] at h
  norm_num at h

structure Boundary where
  literalE8RootCarrier240Paid : Bool
  e8RootGraphUniformDegree56Paid : Bool
  intrinsicRelativeOrthogonalityGraphTyped : Bool
  ternaryOrthogonalityWitnessDegree77Paid : Bool
  naiveOrthogonalityGraphRecognitionBlocked : Bool
  transportedActionAloneCountsAsIndependentGeometry : Bool
  allPossibleTernaryE8RecognitionsBlocked : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  literalE8RootCarrier240Paid := true
  e8RootGraphUniformDegree56Paid := true
  intrinsicRelativeOrthogonalityGraphTyped := true
  ternaryOrthogonalityWitnessDegree77Paid := true
  naiveOrthogonalityGraphRecognitionBlocked := true
  transportedActionAloneCountsAsIndependentGeometry := false
  allPossibleTernaryE8RecognitionsBlocked := false

end Integration.E8RelativeT5IntrinsicGraphObstruction
