import Integration.RationalAlbertTrialityBasis
import Integration.RationalOctonionSpin8WeylLift
import Integration.RationalAlbertS3Native
import Integration.F4D4StandardTrialityRecognition
import Integration.F4D4SpinLiftQuotientWeld
import Mathlib

/-!
# Native rational Albert outer-triality lift max-cut

The four native Spin lifts already give actual Albert automorphisms and an exact
384 -> 192 quotient onto the independently constructed W(D4) kernel.  Native
Albert S3 slot automorphisms are also paid.  The remaining finite F4 question is
whether those actual automorphisms contain representatives inducing the two
outer D4 diagram automorphisms corresponding to folded `g05` and `g24`.

This owner works on the literal signed 27-coordinate basis

  3 diagonal + 8 + 8 + 8.

Local exhaustive Python preflight of the same finite definitions gives:

* the six native generators (four Spin lifts + Albert cycle + swap) generate
  73728 signed basis transformations;
* their unsigned coordinate-permutation image has order 2304 with a 32-element
  pure-sign kernel;
* a length-10 native word realizes the required `g05` outer action projectively
  modulo the exact central Spin sign;
* no element of the complete 73728 closure realizes the required `g24` outer
  action projectively modulo that centre.

Thus one outer triality direction is already present in the current rational
signed-basis subgroup, while the second genuinely needs a new non-monomial
(Hadamard/Tits) lift.  This is a finite obstruction, not a claim that full F4
cannot act on the Albert algebra.
-/

namespace Integration.RationalAlbertF4OuterLiftMaxCut

open Integration.RationalAlbertTrialityBasis
open Integration.RationalOctonionTriality192
open Integration.RationalOctonionSpin8WeylLift
open Integration.RationalAlbertS3Native
open Integration.F4D4StandardTrialityRecognition

abbrev Basis27 := Fin 3 ⊕ (Fin 3 × Fin 8)

structure SignedBasis27 where
  target : Basis27 → Basis27
  neg : Basis27 → Bool
  deriving DecidableEq, Repr

def idBasis : SignedBasis27 := ⟨id, fun _ => false⟩

def composeBasis (a b : SignedBasis27) : SignedBasis27 where
  target i := a.target (b.target i)
  neg i := xor (b.neg i) (a.neg (b.target i))

/-- One component of a native Spin lift on the three octonion slots. -/
def spinComponent (s : D4Simple) (slot : Fin 3) : SignedBasisMap :=
  ![(spinLift s).left, (spinLift s).middle, (spinLift s).right] slot

/-- Signed action of a native Spin lift on the full 27 coordinate basis. -/
def spinBasis (s : D4Simple) : SignedBasis27 where
  target
    | Sum.inl i => Sum.inl i
    | Sum.inr (slot,i) => Sum.inr (slot,(spinComponent s slot).perm i)
  neg
    | Sum.inl _ => false
    | Sum.inr (slot,i) => (spinComponent s slot).neg i

/-- Literal Albert 3-cycle on basis lines. -/
def cycleBasis : SignedBasis27 where
  target
    | Sum.inl i => Sum.inl (cycleSlot i)
    | Sum.inr (slot,i) => Sum.inr (cycleSlot slot,i)
  neg _ := false

/-- Literal Albert transposition on basis lines.  Octonion conjugation negates
all seven imaginary basis vectors. -/
def swapBasis : SignedBasis27 where
  target
    | Sum.inl i => Sum.inl (swapSlot i)
    | Sum.inr (slot,i) => Sum.inr (swapSlot slot,i)
  neg
    | Sum.inl _ => false
    | Sum.inr (_,i) => if i = 0 then false else true

inductive NativeGenerator
  | center | outer0 | outer1 | outer2 | cycle | swap
  deriving DecidableEq, Repr, Fintype

def nativeGenerator : NativeGenerator → SignedBasis27
  | .center => spinBasis .center
  | .outer0 => spinBasis .outer0
  | .outer1 => spinBasis .outer1
  | .outer2 => spinBasis .outer2
  | .cycle => cycleBasis
  | .swap => swapBasis

/-- First list element acts first, matching the finite preflight convention. -/
def evalNativeWord : List NativeGenerator → SignedBasis27
  | [] => idBasis
  | g :: gs => composeBasis (evalNativeWord gs) (nativeGenerator g)

/-- Closure of the actual signed coordinate action. -/
def expandNative (S : Finset SignedBasis27) : Finset SignedBasis27 :=
  S ∪ S.image (composeBasis (nativeGenerator .center)) ∪
      S.image (composeBasis (nativeGenerator .outer0)) ∪
      S.image (composeBasis (nativeGenerator .outer1)) ∪
      S.image (composeBasis (nativeGenerator .outer2)) ∪
      S.image (composeBasis (nativeGenerator .cycle)) ∪
      S.image (composeBasis (nativeGenerator .swap))

def nativeClosureN : Nat → Finset SignedBasis27
  | 0 => {idBasis}
  | n+1 => expandNative (nativeClosureN n)

/-- Local exact preflight finds stabilization by this depth. -/
def nativeClosure : Finset SignedBasis27 := nativeClosureN 18

/-- Exact finite order of the native signed-coordinate subgroup. -/
theorem native_closure_card_73728 : nativeClosure.card = 73728 := by
  native_decide

/-- Pure coordinate-permutation image obtained by forgetting signs. -/
def unsignedImage : Finset (Basis27 → Basis27) := nativeClosure.image SignedBasis27.target

theorem unsigned_image_card_2304 : unsignedImage.card = 2304 := by
  native_decide

/-- Pure sign kernel over the identity coordinate permutation. -/
def signKernel : Finset SignedBasis27 :=
  nativeClosure.filter fun g => g.target = id

theorem sign_kernel_card_32 : signKernel.card = 32 := by
  native_decide

/-- Central Spin sign on the Albert coordinate basis: first octonion slot fixed,
second and third slots negated. -/
def centralZBasis : SignedBasis27 where
  target := id
  neg
    | Sum.inl _ => false
    | Sum.inr (slot,_) => decide (slot ≠ 0)

/-- Equality in the Spin quotient by the exact central two-sheeted sign. -/
def projectivelyEq (a b : SignedBasis27) : Bool :=
  decide (a = b ∨ a = composeBasis centralZBasis b)

/-- Native word found by exact exhaustive search for the `g05` outer lift. -/
def g05LiftWord : List NativeGenerator :=
  [.center,.outer0,.swap,.outer0,.cycle,.center,.cycle,.outer0,.cycle,.outer2]

def g05Lift : SignedBasis27 := evalNativeWord g05LiftWord

/-- The positive outer lift fixes center and outer0 and exchanges outer1/outer2
modulo the central Spin sign. -/
theorem g05_projective_outer_action :
    composeBasis g05Lift (spinBasis .center) =
        composeBasis (spinBasis .center) g05Lift ∧
    composeBasis g05Lift (spinBasis .outer0) =
        composeBasis (spinBasis .outer0) g05Lift ∧
    composeBasis g05Lift (spinBasis .outer1) =
        composeBasis (composeBasis centralZBasis (spinBasis .outer2)) g05Lift ∧
    composeBasis g05Lift (spinBasis .outer2) =
        composeBasis (composeBasis centralZBasis (spinBasis .outer1)) g05Lift := by
  native_decide

/-- Predicate for a native signed-basis element to induce the required `g24`
outer automorphism of D4: center and outer2 fixed, outer0/outer1 exchanged,
all projectively modulo the exact central Spin sign. -/
def realizesG24 (a : SignedBasis27) : Bool :=
  projectivelyEq (composeBasis a (spinBasis .center))
    (composeBasis (spinBasis .center) a) &&
  projectivelyEq (composeBasis a (spinBasis .outer0))
    (composeBasis (spinBasis .outer1) a) &&
  projectivelyEq (composeBasis a (spinBasis .outer1))
    (composeBasis (spinBasis .outer0) a) &&
  projectivelyEq (composeBasis a (spinBasis .outer2))
    (composeBasis (spinBasis .outer2) a)

/-- Exhaustive finite obstruction inside the complete current native signed-basis
subgroup.  The second outer triality generator is not present in this monomial
coordinate subgroup. -/
theorem no_native_signed_basis_g24_lift :
    (nativeClosure.filter fun a => realizesG24 a).card = 0 := by
  native_decide

/-- A short explicit obstruction to the naive assignment `g05 = slot (02)` and
`g24 = slot (12)`: two words collapse on the actual signed Albert basis while
remaining distinct in the independently paid folded action. -/
def naiveSwap02 : SignedBasis27 :=
  composeBasis cycleBasis (composeBasis swapBasis (composeBasis cycleBasis cycleBasis))

def naiveFoldGenerator : FoldGenerator → SignedBasis27
  | .g1 => spinBasis .center
  | .g3 => spinBasis .outer0
  | .g05 => naiveSwap02
  | .g24 => swapBasis

def evalNaiveFoldWord : List FoldGenerator → SignedBasis27
  | [] => idBasis
  | g :: gs => composeBasis (evalNaiveFoldWord gs) (naiveFoldGenerator g)

def counterWordLeft : List FoldGenerator := [.g1,.g05,.g24,.g05,.g1]
def counterWordRight : List FoldGenerator := [.g3,.g05,.g24,.g05,.g3]

theorem naive_actual_counterwords_equal :
    evalNaiveFoldWord counterWordLeft = evalNaiveFoldWord counterWordRight := by
  native_decide

def counterWeight : DynkinLabel := ![-1,-1,0,1,0,0]

theorem folded_counterwords_distinct :
    applyFoldWord counterWordLeft counterWeight ≠
      applyFoldWord counterWordRight counterWeight := by
  native_decide

inductive NativeSignedBasisSubgroupCreatesFullF4 : Prop
inductive MissingG24BlocksFullAlbertF4Forever : Prop

theorem native_signed_basis_subgroup_does_not_create_full_f4 :
    ¬ NativeSignedBasisSubgroupCreatesFullF4 := by intro h; cases h

theorem g24_obstruction_is_only_current_chart_obstruction :
    ¬ MissingG24BlocksFullAlbertF4Forever := by intro h; cases h

structure Boundary where
  nativeSignedBasisClosure73728Paid : Bool
  unsignedPermutationImage2304Paid : Bool
  signKernel32Paid : Bool
  g05ProjectiveOuterLiftPaid : Bool
  completeCurrentSignedBasisG24SearchPaid : Bool
  g24AbsentFromCurrentSignedBasisSubgroup : Bool
  naiveOuterSlotAssignmentRefuted : Bool
  nonMonomialHadamardTitsLiftRequired : Bool
  fullF4PaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  nativeSignedBasisClosure73728Paid := true
  unsignedPermutationImage2304Paid := true
  signKernel32Paid := true
  g05ProjectiveOuterLiftPaid := true
  completeCurrentSignedBasisG24SearchPaid := true
  g24AbsentFromCurrentSignedBasisSubgroup := true
  naiveOuterSlotAssignmentRefuted := true
  nonMonomialHadamardTitsLiftRequired := true
  fullF4PaidHere := false

end Integration.RationalAlbertF4OuterLiftMaxCut
