import Integration.RationalAlbertNative
import Mathlib

/-!
# Native signed-basis octonion automorphisms and Albert lifts

Two explicit signed permutations of the seven imaginary rational-octonion basis
vectors preserve the repository Cayley-Dickson product.  Local exhaustive basis
closure gives a finite signed-basis octonion subgroup of order 1344.  This file
proves the two generators algebraically and lifts them diagonally to genuine
Albert Jordan/cubic automorphisms.

The order 1344 is retained as finite diagnostic data; it is not promoted to the
full algebraic group G2.
-/

namespace Integration.RationalAlbertSignedBasisAutomorphisms

open Integration.RationalCayleyDicksonOctonion
open Integration.RationalAlbertNative
open RationalQuaternion RationalOctonion RationalAlbertNative.RationalAlbert

abbrev O8 := RationalOctonion
abbrev A27 := RationalAlbertNative.RationalAlbert

/-- e1 -> -e1, e2 -> e2, e3 -> -e3, e4<->e5, e6<->e7. -/
def octA (x : O8) : O8 :=
  ⟨⟨x.first.q0,-x.first.q1,x.first.q2,-x.first.q3⟩,
   ⟨x.second.q1,x.second.q0,x.second.q3,x.second.q2⟩⟩

/-- Pure basis permutation 1->2,2->5,3->7,4->3,5->1,6->6,7->4. -/
def octB (x : O8) : O8 :=
  ⟨⟨x.first.q0,x.second.q1,x.first.q1,x.second.q0⟩,
   ⟨x.second.q3,x.first.q2,x.second.q2,x.first.q3⟩⟩

theorem octA_mul (x y : O8) : octA (x*y)=octA x * octA y := by
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
  rcases a with ⟨a0,a1,a2,a3⟩; rcases b with ⟨b0,b1,b2,b3⟩
  rcases c with ⟨c0,c1,c2,c3⟩; rcases d with ⟨d0,d1,d2,d3⟩
  ext <;> apply RationalQuaternion.ext <;>
    simp [octA, HMul.hMul, Mul.mul, RationalOctonion.mul,
      RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

theorem octB_mul (x y : O8) : octB (x*y)=octB x * octB y := by
  rcases x with ⟨a,b⟩; rcases y with ⟨c,d⟩
  rcases a with ⟨a0,a1,a2,a3⟩; rcases b with ⟨b0,b1,b2,b3⟩
  rcases c with ⟨c0,c1,c2,c3⟩; rcases d with ⟨d0,d1,d2,d3⟩
  ext <;> apply RationalQuaternion.ext <;>
    simp [octB, HMul.hMul, Mul.mul, RationalOctonion.mul,
      RationalQuaternion.mul, RationalQuaternion.conj] <;> ring

theorem octA_conj (x : O8) : octA (RationalOctonion.conj x)=RationalOctonion.conj (octA x) := by
  rcases x with ⟨a,b⟩; rcases a with ⟨a0,a1,a2,a3⟩; rcases b with ⟨b0,b1,b2,b3⟩
  ext <;> apply RationalQuaternion.ext <;>
    simp [octA, RationalOctonion.conj, RationalQuaternion.conj]

theorem octB_conj (x : O8) : octB (RationalOctonion.conj x)=RationalOctonion.conj (octB x) := by
  rcases x with ⟨a,b⟩; rcases a with ⟨a0,a1,a2,a3⟩; rcases b with ⟨b0,b1,b2,b3⟩
  ext <;> apply RationalQuaternion.ext <;>
    simp [octB, RationalOctonion.conj, RationalQuaternion.conj]

theorem octA_norm (x : O8) : RationalOctonion.normSq (octA x)=RationalOctonion.normSq x := by
  rcases x with ⟨a,b⟩; rcases a with ⟨a0,a1,a2,a3⟩; rcases b with ⟨b0,b1,b2,b3⟩
  simp [octA,RationalOctonion.normSq,RationalQuaternion.normSq]; ring

theorem octB_norm (x : O8) : RationalOctonion.normSq (octB x)=RationalOctonion.normSq x := by
  rcases x with ⟨a,b⟩; rcases a with ⟨a0,a1,a2,a3⟩; rcases b with ⟨b0,b1,b2,b3⟩
  simp [octB,RationalOctonion.normSq,RationalQuaternion.normSq]; ring

def liftOct (f : O8 → O8) (X : A27) : A27 :=
  ⟨X.diagonal0,X.diagonal1,X.diagonal2,f X.off12,f X.off20,f X.off01⟩

def liftA : A27 → A27 := liftOct octA
def liftB : A27 → A27 := liftOct octB

theorem liftA_product (X Y : A27) :
    liftA (jordanProduct X Y)=jordanProduct (liftA X) (liftA Y) := by
  rcases X with ⟨a,b,c,x,y,z⟩; rcases Y with ⟨d,e,f,p,q,r⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  rcases p with ⟨p1,p2⟩; rcases q with ⟨q1,q2⟩; rcases r with ⟨r1,r2⟩
  ext <;> try { apply RationalOctonion.ext <;> apply RationalQuaternion.ext } <;>
    simp [liftA,liftOct,octA,jordanProduct,innerO,halfO,HMul.hMul,Mul.mul,
      RationalOctonion.mul,RationalOctonion.conj,RationalOctonion.realPart,
      RationalQuaternion.mul,RationalQuaternion.conj] <;> ring

theorem liftB_product (X Y : A27) :
    liftB (jordanProduct X Y)=jordanProduct (liftB X) (liftB Y) := by
  rcases X with ⟨a,b,c,x,y,z⟩; rcases Y with ⟨d,e,f,p,q,r⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  rcases p with ⟨p1,p2⟩; rcases q with ⟨q1,q2⟩; rcases r with ⟨r1,r2⟩
  ext <;> try { apply RationalOctonion.ext <;> apply RationalQuaternion.ext } <;>
    simp [liftB,liftOct,octB,jordanProduct,innerO,halfO,HMul.hMul,Mul.mul,
      RationalOctonion.mul,RationalOctonion.conj,RationalOctonion.realPart,
      RationalQuaternion.mul,RationalQuaternion.conj] <;> ring

theorem liftA_cubic (X : A27) : cubic (liftA X)=cubic X := by
  rcases X with ⟨a,b,c,x,y,z⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  simp [liftA,liftOct,octA,cubic,RationalOctonion.normSq,RationalOctonion.realPart,
    HMul.hMul,Mul.mul,RationalOctonion.mul,RationalQuaternion.mul,
    RationalQuaternion.normSq,RationalQuaternion.conj]; ring

theorem liftB_cubic (X : A27) : cubic (liftB X)=cubic X := by
  rcases X with ⟨a,b,c,x,y,z⟩
  rcases x with ⟨x1,x2⟩; rcases y with ⟨y1,y2⟩; rcases z with ⟨z1,z2⟩
  simp [liftB,liftOct,octB,cubic,RationalOctonion.normSq,RationalOctonion.realPart,
    HMul.hMul,Mul.mul,RationalOctonion.mul,RationalQuaternion.mul,
    RationalQuaternion.normSq,RationalQuaternion.conj]; ring

def localSignedBasisOctonionClosureOrder : Nat := 1344

structure Boundary where
  octonionGeneratorsPaid : Bool
  octonionProductPreservationPaid : Bool
  octonionConjugationPreservationPaid : Bool
  octonionNormPreservationPaid : Bool
  AlbertLiftProductPreservationPaid : Bool
  AlbertLiftCubicPreservationPaid : Bool
  localClosureOrder1344Recorded : Bool
  fullG2PaidHere : Bool
  fullF4PaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  octonionGeneratorsPaid := true
  octonionProductPreservationPaid := true
  octonionConjugationPreservationPaid := true
  octonionNormPreservationPaid := true
  AlbertLiftProductPreservationPaid := true
  AlbertLiftCubicPreservationPaid := true
  localClosureOrder1344Recorded := true
  fullG2PaidHere := false
  fullF4PaidHere := false

end Integration.RationalAlbertSignedBasisAutomorphisms
