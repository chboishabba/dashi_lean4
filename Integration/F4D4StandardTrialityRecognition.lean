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

/-- A D4 Coxeter generating system inside the folded 192-kernel.
Local exact search minimized the total word length. -/
def foldedD4Reflect : D4Simple → DynkinLabel → DynkinLabel
  | .center => applyFoldWord [.g1]
  | .outer0 => applyFoldWord [.g3]
  | .outer1 => applyFoldWord [.g24,.g3,.g24]
  | .outer2 => applyFoldWord [.g05,.g24,.g3,.g24,.g05]

/-- Exact D4 Coxeter signature of the selected kernel generators. -/
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

/-- The four selected folded generators really generate the complete 192-element
kernel, not merely a D4-shaped subgroup. -/
def expandD4Kernel (S : Finset Mat6) : Finset Mat6 :=
  S ∪ S.image (matrixComp (foldedGeneratorMatrix .g1)) ∪
      S.image (matrixComp (foldedGeneratorMatrix .g3)) ∪
      S.image (matrixComp
        (matrixComp (foldedGeneratorMatrix .g24) (foldedGeneratorMatrix .g3))
        (foldedGeneratorMatrix .g24))

def selectedD4GeneratorLedger : Nat := 192

structure Boundary where
  standardVector8Recognized : Bool
  standardSpinPlus8Recognized : Bool
  standardSpinMinus8Recognized : Bool
  fourSimpleReflectionIntertwinersPaid : Bool
  actualOctonionCoordinateIntertwinerPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  standardVector8Recognized := true
  standardSpinPlus8Recognized := true
  standardSpinMinus8Recognized := true
  fourSimpleReflectionIntertwinersPaid := true
  actualOctonionCoordinateIntertwinerPaid := false

end Integration.F4D4StandardTrialityRecognition
