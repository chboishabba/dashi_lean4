import Integration.RationalOctonionTriality192
import Integration.RationalOctonionTriality192Obstruction
import Mathlib

/-!
# D4 Weyl group as a quotient of a rational-octonion triality normalizer

A direct 192-element signed-monomial subgroup was the wrong recognition target:
Weyl groups arise as normalizer quotients.  Exact local search finds five
signed-monomial triality generators whose closure has order 6144.  Forgetting
basis signs gives a 192-element permutation quotient, with a 32-element sign
kernel.

Inside that quotient four involutions satisfy the D4 Coxeter presentation and
generate all 192 elements.  This is the correct finite triality architecture:

  1 -> K_32 -> N_6144 -> W(D4)_192 -> 1.

No claim about continuous Spin(8) is made here; this is an exact finite
normalizer/quotient producer on the repo-native octonion triality tensor.
-/

namespace Integration.RationalOctonionD4TrialityNormalizer

open Integration.RationalOctonionTriality192

private def perm8
    (p0 p1 p2 p3 p4 p5 p6 p7 : Fin 8) : Fin 8 → Fin 8 :=
  ![p0,p1,p2,p3,p4,p5,p6,p7]
private def signs8
    (s0 s1 s2 s3 s4 s5 s6 s7 : Bool) : Fin 8 → Bool :=
  ![s0,s1,s2,s3,s4,s5,s6,s7]
private def smap (p : Fin 8 → Fin 8) (s : Fin 8 → Bool) : SignedBasisMap := ⟨p,s⟩

/-- Order-two linear-part lift. -/
def lift0 : TrialityTriple :=
  let p := perm8 0 4 2 6 1 5 3 7
  ⟨ smap p (signs8 false false false true false true true true),
    smap p (signs8 true true true false true false false false),
    smap p (signs8 true true true false true false false false) ⟩

/-- Order-three linear-part lift. -/
def lift1 : TrialityTriple :=
  let p := perm8 0 6 2 4 5 3 7 1
  let s := signs8 false false false false false false false false
  ⟨smap p s,smap p s,smap p s⟩

/-- Three affine-translation lifts generating the 2^3 part of the D4 Weyl
quotient; their signed lifts generate a larger 2-kernel upstairs. -/
def lift2 : TrialityTriple :=
  ⟨ smap (perm8 1 0 3 2 5 4 7 6) (signs8 false false false false false false false false),
    smap (perm8 0 1 2 3 4 5 6 7) (signs8 false true false true false true true false),
    smap (perm8 1 0 3 2 5 4 7 6) (signs8 true true false false false false false false) ⟩

def lift3 : TrialityTriple :=
  ⟨ smap (perm8 2 3 0 1 6 7 4 5) (signs8 true true true true true true true true),
    smap (perm8 0 1 2 3 4 5 6 7) (signs8 true false false true true true false false),
    smap (perm8 2 3 0 1 6 7 4 5) (signs8 true false true false false false false false) ⟩

def lift4 : TrialityTriple :=
  ⟨ smap (perm8 4 5 6 7 0 1 2 3) (signs8 false false false false false false false false),
    smap (perm8 0 1 2 3 4 5 6 7) (signs8 false true true true true false false false),
    smap (perm8 4 5 6 7 0 1 2 3) (signs8 true false false false true false false false) ⟩

/-- Every chosen lift is an actual basis-triality symmetry. -/
theorem lift0_preserves : PreservesBasisTriality lift0 := by native_decide
theorem lift1_preserves : PreservesBasisTriality lift1 := by native_decide
theorem lift2_preserves : PreservesBasisTriality lift2 := by native_decide
theorem lift3_preserves : PreservesBasisTriality lift3 := by native_decide
theorem lift4_preserves : PreservesBasisTriality lift4 := by native_decide


def generator : Fin 5 → TrialityTriple := ![lift0,lift1,lift2,lift3,lift4]

def expandNormalizer (S : Finset TrialityTriple) : Finset TrialityTriple :=
  S ∪ S.image (composeTriple lift0) ∪ S.image (composeTriple lift1) ∪
      S.image (composeTriple lift2) ∪ S.image (composeTriple lift3) ∪
      S.image (composeTriple lift4)

def normalizerN : Nat → Finset TrialityTriple
  | 0 => {idTriple}
  | n+1 => expandNormalizer (normalizerN n)

def trialityNormalizer6144 : Finset TrialityTriple := normalizerN 10

theorem normalizer_card_6144 : trialityNormalizer6144.card = 6144 := by native_decide
theorem normalizer_stable : normalizerN 11 = trialityNormalizer6144 := by native_decide

theorem normalizer_preserves_triality :
    ∀ g ∈ trialityNormalizer6144, PreservesBasisTriality g := by native_decide

structure PermTriple where
  left middle right : Fin 8 → Fin 8
  deriving DecidableEq, Repr


def eraseSigns (g : TrialityTriple) : PermTriple :=
  ⟨g.left.perm,g.middle.perm,g.right.perm⟩
def idPermTriple : PermTriple := ⟨fun i=>i,fun i=>i,fun i=>i⟩

def composePerm (a b : Fin 8 → Fin 8) : Fin 8 → Fin 8 := fun i => a (b i)
def composePermTriple (a b : PermTriple) : PermTriple :=
  ⟨composePerm a.left b.left,composePerm a.middle b.middle,
   composePerm a.right b.right⟩

/-- Weyl quotient action obtained by forgetting the torus/sign lift. -/
def d4WeylQuotient : Finset PermTriple := trialityNormalizer6144.image eraseSigns

def signKernel32 : Finset TrialityTriple :=
  trialityNormalizer6144.filter fun g => eraseSigns g = idPermTriple

theorem d4_quotient_card_192 : d4WeylQuotient.card = 192 := by native_decide
theorem sign_kernel_card_32 : signKernel32.card = 32 := by native_decide

/-- Evaluate a word in the five normalizer generators. -/
def evalWord (w : List (Fin 5)) : TrialityTriple :=
  w.foldl (fun acc i => composeTriple acc (generator i)) idTriple

/-- Four quotient involutions discovered by exact finite search.  Generator 1
below is the central D4 node; the other three are mutually commuting leaves. -/
def cox0 : PermTriple := eraseSigns (evalWord [0,1,1,0,1,0])
def cox1 : PermTriple := eraseSigns (evalWord [0])
def cox2 : PermTriple := eraseSigns (evalWord [0,1,1,0,1,0,2])
def cox3 : PermTriple := eraseSigns (evalWord [1,0,1,4,1])


def permPow (g : PermTriple) : Nat → PermTriple
  | 0 => idPermTriple
  | n+1 => composePermTriple g (permPow g n)

 theorem coxeter_involutions :
    permPow cox0 2=idPermTriple ∧ permPow cox1 2=idPermTriple ∧
    permPow cox2 2=idPermTriple ∧ permPow cox3 2=idPermTriple := by native_decide

/-- D4 star: cox1 is joined by order-three edges to the three commuting leaves. -/
theorem d4_coxeter_adjacent_orders :
    permPow (composePermTriple cox0 cox1) 3=idPermTriple ∧
    permPow (composePermTriple cox2 cox1) 3=idPermTriple ∧
    permPow (composePermTriple cox3 cox1) 3=idPermTriple := by native_decide

theorem d4_coxeter_nonadjacent_commute :
    composePermTriple cox0 cox2=composePermTriple cox2 cox0 ∧
    composePermTriple cox0 cox3=composePermTriple cox3 cox0 ∧
    composePermTriple cox2 cox3=composePermTriple cox3 cox2 := by native_decide


def expandCoxeter (S : Finset PermTriple) : Finset PermTriple :=
  S ∪ S.image (composePermTriple cox0) ∪ S.image (composePermTriple cox1) ∪
      S.image (composePermTriple cox2) ∪ S.image (composePermTriple cox3)
def coxeterN : Nat → Finset PermTriple
  | 0 => {idPermTriple}
  | n+1 => expandCoxeter (coxeterN n)
def d4CoxeterImage : Finset PermTriple := coxeterN 12

theorem d4_coxeter_image_card_192 : d4CoxeterImage.card = 192 := by native_decide
theorem d4_coxeter_image_stable : coxeterN 13 = d4CoxeterImage := by native_decide

/-- The D4 Coxeter-generated permutation action is exactly the sign-erased
quotient of the 6144-element triality normalizer. -/
theorem coxeter_image_eq_triality_quotient : d4CoxeterImage = d4WeylQuotient := by
  native_decide

structure Boundary where
  explicitTrialityNormalizerPaid : Bool
  normalizerOrder6144Paid : Bool
  signKernelOrder32Paid : Bool
  quotientOrder192Paid : Bool
  d4CoxeterPresentationPaid : Bool
  d4CoxeterGeneratorsExhaustQuotientPaid : Bool
  continuousSpin8RecognitionPaid : Bool
  sameObjectWithFoldedE6D4KernelPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  explicitTrialityNormalizerPaid := true
  normalizerOrder6144Paid := true
  signKernelOrder32Paid := true
  quotientOrder192Paid := true
  d4CoxeterPresentationPaid := true
  d4CoxeterGeneratorsExhaustQuotientPaid := true
  continuousSpin8RecognitionPaid := false
  sameObjectWithFoldedE6D4KernelPaid := false

end Integration.RationalOctonionD4TrialityNormalizer
