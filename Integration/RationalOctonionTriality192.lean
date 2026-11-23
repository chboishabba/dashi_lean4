import Integration.RationalAlbertTrialityBasis
import Mathlib

/-!
# Explicit 192-element octonion triality subgroup

Local exact search over the repo-native Cayley-Dickson multiplication tensor
finds three signed-monomial triality generators:

* `a`: common octonion automorphism of order 2;
* `b`: common octonion automorphism of order 3;
* `x`: an order-2 genuine triality triple with three different 8-actions.

Their componentwise closure has exactly 192 elements.  Every element preserves
`Re((uv)w)` on the literal octonion basis.  This gives an explicit finite
triality producer of the correct W(D4) order independently of the folded-E6
weight calculation.
-/

namespace Integration.RationalOctonionTriality192

open Integration.RationalCayleyDicksonOctonion
open Integration.RationalAlbertTrialityBasis
open RationalOctonion

structure SignedBasisMap where
  perm : Fin 8 → Fin 8
  neg : Fin 8 → Bool
  deriving DecidableEq, Repr

/-- Scalar sign of one signed basis image. -/
def signQ (g : SignedBasisMap) (i : Fin 8) : ℚ := if g.neg i then -1 else 1

def idMap : SignedBasisMap := ⟨fun i => i, fun _ => false⟩

/-- Composition `a ∘ b`. -/
def composeMap (a b : SignedBasisMap) : SignedBasisMap where
  perm i := a.perm (b.perm i)
  neg i := xor (b.neg i) (a.neg (b.perm i))

structure TrialityTriple where
  left middle right : SignedBasisMap
  deriving DecidableEq, Repr


def idTriple : TrialityTriple := ⟨idMap,idMap,idMap⟩

def composeTriple (a b : TrialityTriple) : TrialityTriple :=
  ⟨composeMap a.left b.left, composeMap a.middle b.middle,
   composeMap a.right b.right⟩

private def signs8
    (s0 s1 s2 s3 s4 s5 s6 s7 : Bool) : Fin 8 → Bool :=
  ![s0,s1,s2,s3,s4,s5,s6,s7]

private def perm8
    (p0 p1 p2 p3 p4 p5 p6 p7 : Fin 8) : Fin 8 → Fin 8 :=
  ![p0,p1,p2,p3,p4,p5,p6,p7]

/-- Order-two common octonion automorphism from the exact search. -/
def genA : SignedBasisMap :=
  ⟨perm8 0 1 2 3 4 5 6 7,
   signs8 false true false true true false true false⟩

/-- Order-three common octonion automorphism from the exact search. -/
def genB : SignedBasisMap :=
  ⟨perm8 0 5 1 4 7 2 6 3,
   signs8 false false true true true true false false⟩

/-- Genuine triality generator, first 8-dimensional component. -/
def genX0 : SignedBasisMap :=
  ⟨perm8 7 6 5 4 3 2 1 0,
   signs8 false true true true true true true false⟩

/-- Genuine triality generator, second 8-dimensional component. -/
def genX1 : SignedBasisMap :=
  ⟨perm8 7 6 5 4 3 2 1 0,
   signs8 true true true true true true true true⟩

/-- Genuine triality generator, third 8-dimensional component. -/
def genX2 : SignedBasisMap :=
  ⟨perm8 0 1 2 3 4 5 6 7,
   signs8 false true false false true true false true⟩


def trialityA : TrialityTriple := ⟨genA,genA,genA⟩
def trialityB : TrialityTriple := ⟨genB,genB,genB⟩
def trialityX : TrialityTriple := ⟨genX0,genX1,genX2⟩

/-- The native octonion triality tensor on basis vectors. -/
def basisTriality (i j k : Fin 8) : ℚ :=
  realPart ((octBasis i * octBasis j) * octBasis k)

/-- Signed-monomial triality preservation, sufficient because the form is
trilinear and the eight basis vectors span the coordinate carrier. -/
def PreservesBasisTriality (g : TrialityTriple) : Prop :=
  ∀ i j k,
    signQ g.left i * signQ g.middle j * signQ g.right k *
      basisTriality (g.left.perm i) (g.middle.perm j) (g.right.perm k)
      = basisTriality i j k

 theorem generatorA_preserves_triality : PreservesBasisTriality trialityA := by
  native_decide
 theorem generatorB_preserves_triality : PreservesBasisTriality trialityB := by
  native_decide
 theorem generatorX_preserves_triality : PreservesBasisTriality trialityX := by
  native_decide

/-- Exact finite closure under the three independent triality generators. -/
def expand (S : Finset TrialityTriple) : Finset TrialityTriple :=
  S ∪ S.image (composeTriple trialityA) ∪
      S.image (composeTriple trialityB) ∪
      S.image (composeTriple trialityX)

def closureN : Nat → Finset TrialityTriple
  | 0 => {idTriple}
  | n+1 => expand (closureN n)

/-- Python preflight found Cayley diameter 10 for these generators. -/
def triality192 : Finset TrialityTriple := closureN 10

theorem triality192_card : triality192.card = 192 := by native_decide

theorem triality192_stable : closureN 11 = triality192 := by native_decide

/-- Every element of the exact 192-element closure preserves the literal
Cayley-Dickson triality tensor. -/
theorem triality192_preserves :
    ∀ g ∈ triality192, PreservesBasisTriality g := by
  native_decide

/-- The common generators have the S4-side orders found by the exact search. -/
theorem genA_square : composeMap genA genA = idMap := by native_decide

theorem genB_cube : composeMap genB (composeMap genB genB) = idMap := by native_decide

theorem genX_square : composeTriple trialityX trialityX = idTriple := by native_decide

structure Boundary where
  explicitTrialityGeneratorsPaid : Bool
  generatedOrder192Paid : Bool
  closureStablePaid : Bool
  basisTrialityPreservationPaid : Bool
  sameObjectWithFoldedD4KernelPaid : Bool
  fullSpin8RecognitionPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  explicitTrialityGeneratorsPaid := true
  generatedOrder192Paid := true
  closureStablePaid := true
  basisTrialityPreservationPaid := true
  sameObjectWithFoldedD4KernelPaid := false
  fullSpin8RecognitionPaid := false

end Integration.RationalOctonionTriality192
