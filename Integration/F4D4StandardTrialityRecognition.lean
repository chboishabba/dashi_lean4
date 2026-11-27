import Integration.F4D4TrialityAlbertShape
import Mathlib

/-!
# Same-action recognition of the three 8-sectors as D4 triality weights

The 192-element kernel already gives three 8-element orbits.  This owner does
not recognize them by cardinality: it gives explicit finite graphs to the
standard D4 vector and two half-spinor weight systems and checks the four
simple-reflection actions on both sides.

Scaled standard weights are used to avoid halves:
* vector weights are `±2 e_i`;
* spinor weights are sign vectors `(±1,±1,±1,±1)` with even/odd parity.
-/

namespace Integration.F4D4StandardTrialityRecognition

open Integration.E6Minuscule27LiteralRecognition
open Integration.E6F4WeylFold
open Integration.F4D4TrialityAlbertShape

abbrev D4Weight := Fin 4 → Int

def d4 (a b c d : Int) : D4Weight := ![a,b,c,d]
def e6 (a b c d e f : Int) : DynkinLabel := ![a,b,c,d,e,f]

/-- D4 simple roots with `center` joined to all three outers. -/
def rootCenter : D4Weight := d4 0 1 (-1) 0
def rootOuter0 : D4Weight := d4 1 (-1) 0 0
def rootOuter1 : D4Weight := d4 0 0 1 (-1)
def rootOuter2 : D4Weight := d4 0 0 1 1

def dot4 (x y : D4Weight) : Int := ∑ i, x i * y i

/-- Reflection on weights scaled by two.  Every simple root has norm squared 2,
so `2 (lambda,alpha)/(alpha,alpha)` becomes `(scaledLambda,alpha)`. -/
def reflect4 (r w : D4Weight) : D4Weight :=
  fun i => w i - dot4 w r * r i

inductive D4Simple
  | center | outer0 | outer1 | outer2
  deriving DecidableEq, Repr, Fintype

def standardRoot : D4Simple → D4Weight
  | .center => rootCenter
  | .outer0 => rootOuter0
  | .outer1 => rootOuter1
  | .outer2 => rootOuter2

def standardReflect (s : D4Simple) : D4Weight → D4Weight :=
  reflect4 (standardRoot s)

/-- Apply a word in the four folded F4 generators. -/
def applyFoldWord : List FoldGenerator → DynkinLabel → DynkinLabel
  | [], x => x
  | g :: gs, x => applyFoldWord gs (foldReflect g x)

/-- Matrix of the same word; first list element acts first. -/
def foldWordMatrix : List FoldGenerator → Mat6
  | [] => identityMatrix
  | g :: gs => matrixComp (foldWordMatrix gs) (foldedGeneratorMatrix g)

/-- A D4 Coxeter generating system inside the folded 192-kernel.
Local exact search minimized the total word length. -/
def d4Word : D4Simple → List FoldGenerator
  | .center => [.g1]
  | .outer0 => [.g3]
  | .outer1 => [.g24,.g3,.g24]
  | .outer2 => [.g05,.g24,.g3,.g24,.g05]

def foldedD4Reflect (s : D4Simple) : DynkinLabel → DynkinLabel :=
  applyFoldWord (d4Word s)

def foldedD4Matrix (s : D4Simple) : Mat6 :=
  foldWordMatrix (d4Word s)

/-- Word action and matrix action agree exactly. -/
theorem folded_d4_matrix_agrees :
    ∀ s x, matrixApply (foldedD4Matrix s) x = foldedD4Reflect s x := by
  native_decide

/-- Exact D4 Coxeter matrix. -/
def d4MatrixPow (M : Mat6) : Nat → Mat6
  | 0 => identityMatrix
  | n+1 => matrixComp M (d4MatrixPow M n)

theorem folded_d4_simple_involutions :
    ∀ s, d4MatrixPow (foldedD4Matrix s) 2 = identityMatrix := by
  native_decide

theorem folded_d4_coxeter_orders :
    d4MatrixPow (matrixComp (foldedD4Matrix .center) (foldedD4Matrix .outer0)) 3 = identityMatrix ∧
    d4MatrixPow (matrixComp (foldedD4Matrix .center) (foldedD4Matrix .outer1)) 3 = identityMatrix ∧
    d4MatrixPow (matrixComp (foldedD4Matrix .center) (foldedD4Matrix .outer2)) 3 = identityMatrix ∧
    matrixComp (foldedD4Matrix .outer0) (foldedD4Matrix .outer1) =
      matrixComp (foldedD4Matrix .outer1) (foldedD4Matrix .outer0) ∧
    matrixComp (foldedD4Matrix .outer0) (foldedD4Matrix .outer2) =
      matrixComp (foldedD4Matrix .outer2) (foldedD4Matrix .outer0) ∧
    matrixComp (foldedD4Matrix .outer1) (foldedD4Matrix .outer2) =
      matrixComp (foldedD4Matrix .outer2) (foldedD4Matrix .outer1) := by
  native_decide

/-- The selected generators preserve each of the three triality orbits. -/
theorem folded_d4_generators_preserve_each_triality_orbit :
    (∀ s x, x ∈ trialityOrbit0 → foldedD4Reflect s x ∈ trialityOrbit0) ∧
    (∀ s x, x ∈ trialityOrbit1 → foldedD4Reflect s x ∈ trialityOrbit1) ∧
    (∀ s x, x ∈ trialityOrbit2 → foldedD4Reflect s x ∈ trialityOrbit2) := by
  native_decide

/-- Standard scaled D4 weight sets. -/
def spinPlusSet : Finset D4Weight :=
  { d4 1 1 1 1, d4 1 1 (-1) (-1), d4 1 (-1) 1 (-1), d4 1 (-1) (-1) 1,
    d4 (-1) 1 1 (-1), d4 (-1) 1 (-1) 1, d4 (-1) (-1) 1 1,
    d4 (-1) (-1) (-1) (-1) }

def vectorSet : Finset D4Weight :=
  { d4 2 0 0 0, d4 (-2) 0 0 0, d4 0 2 0 0, d4 0 (-2) 0 0,
    d4 0 0 2 0, d4 0 0 (-2) 0, d4 0 0 0 2, d4 0 0 0 (-2) }

def spinMinusSet : Finset D4Weight :=
  { d4 1 1 1 (-1), d4 1 1 (-1) 1, d4 1 (-1) 1 1, d4 (-1) 1 1 1,
    d4 1 (-1) (-1) (-1), d4 (-1) 1 (-1) (-1), d4 (-1) (-1) 1 (-1),
    d4 (-1) (-1) (-1) 1 }

/-- Explicit same-object graphs found by exact finite action matching. -/
def sector0SpinPlusGraph : Finset (DynkinLabel × D4Weight) :=
  { (e6 (-1) (-1) 0 1 0 0, d4 1 (-1) 1 (-1)),
    (e6 (-1) 0 0 0 0 0, d4 (-1) (-1) (-1) (-1)),
    (e6 (-1) 0 1 (-1) 1 0, d4 (-1) 1 1 (-1)),
    (e6 (-1) 1 0 0 0 0, d4 1 1 (-1) (-1)),
    (e6 0 (-1) 0 0 0 1, d4 (-1) (-1) 1 1),
    (e6 0 0 (-1) 1 (-1) 1, d4 1 (-1) (-1) 1),
    (e6 0 0 0 0 0 1, d4 1 1 1 1),
    (e6 0 1 0 (-1) 0 1, d4 (-1) 1 (-1) 1) }

def sector1VectorGraph : Finset (DynkinLabel × D4Weight) :=
  { (e6 (-1) 0 1 0 0 (-1), d4 0 0 0 2),
    (e6 0 (-1) 0 1 (-1) 0, d4 0 2 0 0),
    (e6 0 (-1) 1 0 0 0, d4 0 0 (-2) 0),
    (e6 0 0 0 1 (-1) 0, d4 (-2) 0 0 0),
    (e6 0 0 1 (-1) 0 0, d4 2 0 0 0),
    (e6 0 1 0 0 (-1) 0, d4 0 0 2 0),
    (e6 0 1 1 (-1) 0 0, d4 0 (-2) 0 0),
    (e6 1 0 0 0 (-1) 1, d4 0 0 0 (-2)) }

def sector2SpinMinusGraph : Finset (DynkinLabel × D4Weight) :=
  { (e6 0 (-1) 0 0 1 (-1), d4 1 1 (-1) 1),
    (e6 0 0 (-1) 1 0 (-1), d4 (-1) 1 1 1),
    (e6 0 0 0 0 1 (-1), d4 (-1) (-1) (-1) 1),
    (e6 0 1 0 (-1) 1 (-1), d4 1 (-1) 1 1),
    (e6 1 (-1) (-1) 1 0 0, d4 (-1) 1 (-1) (-1)),
    (e6 1 0 (-1) 0 0 0, d4 1 1 1 (-1)),
    (e6 1 0 0 (-1) 1 0, d4 1 (-1) (-1) (-1)),
    (e6 1 1 (-1) 0 0 0, d4 (-1) (-1) 1 (-1)) }

/-- The graphs cover exactly the three paid E6 sectors and the three standard
D4 weight systems. -/
theorem graph_images_are_exact :
    sector0SpinPlusGraph.image Prod.fst = trialityOrbit0 ∧
    sector0SpinPlusGraph.image Prod.snd = spinPlusSet ∧
    sector1VectorGraph.image Prod.fst = trialityOrbit1 ∧
    sector1VectorGraph.image Prod.snd = vectorSet ∧
    sector2SpinMinusGraph.image Prod.fst = trialityOrbit2 ∧
    sector2SpinMinusGraph.image Prod.snd = spinMinusSet := by
  native_decide

/-- Same-action intertwining for all four simple reflections on all three
representations. -/
theorem sector0_same_d4_action :
    ∀ s p, p ∈ sector0SpinPlusGraph →
      (foldedD4Reflect s p.1, standardReflect s p.2) ∈ sector0SpinPlusGraph := by
  native_decide

theorem sector1_same_d4_action :
    ∀ s p, p ∈ sector1VectorGraph →
      (foldedD4Reflect s p.1, standardReflect s p.2) ∈ sector1VectorGraph := by
  native_decide

theorem sector2_same_d4_action :
    ∀ s p, p ∈ sector2SpinMinusGraph →
      (foldedD4Reflect s p.1, standardReflect s p.2) ∈ sector2SpinMinusGraph := by
  native_decide

/-- Closure under the selected four simple reflections. -/
def expandSelectedD4 (S : Finset Mat6) : Finset Mat6 :=
  S ∪ S.image (matrixComp (foldedD4Matrix .center)) ∪
      S.image (matrixComp (foldedD4Matrix .outer0)) ∪
      S.image (matrixComp (foldedD4Matrix .outer1)) ∪
      S.image (matrixComp (foldedD4Matrix .outer2))

def selectedD4ClosureN : Nat → Finset Mat6
  | 0 => {identityMatrix}
  | n+1 => expandSelectedD4 (selectedD4ClosureN n)

def selectedD4Closure : Finset Mat6 := selectedD4ClosureN 12

/-- The four recognized simple reflections generate exactly the previously
independent 192-element kernel. -/
theorem selected_d4_closure_card_192 : selectedD4Closure.card = 192 := by
  native_decide

theorem selected_d4_closure_eq_kernel : selectedD4Closure = d4KernelSet := by
  native_decide

structure Boundary where
  standardVector8Recognized : Bool
  standardSpinPlus8Recognized : Bool
  standardSpinMinus8Recognized : Bool
  fourSimpleReflectionIntertwinersPaid : Bool
  fullSelectedD4ClosureEqualsKernel : Bool
  actualOctonionCoordinateIntertwinerPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  standardVector8Recognized := true
  standardSpinPlus8Recognized := true
  standardSpinMinus8Recognized := true
  fourSimpleReflectionIntertwinersPaid := true
  fullSelectedD4ClosureEqualsKernel := true
  actualOctonionCoordinateIntertwinerPaid := false

end Integration.F4D4StandardTrialityRecognition
