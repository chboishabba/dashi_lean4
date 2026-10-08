import Integration.RationalOctonionTriality192
import Integration.F4D4StandardTrialityRecognition
import Mathlib

/-!
# Native octonion Spin(8) Weyl lift

The earlier 192-element signed-monomial triality subgroup is not W(D4).  The
correct finite normalizer object is a central double cover.

Exact local solution of the literal Cayley-Dickson triality tensor produces
four signed-monomial triples lifting the four recognized D4 simple
reflections.  Their closure has order 384.  Every lift squares to the same
central element

  z = (I, -I, -I),

and `z^2 = 1`.  The vector component has image order 192, while the full triple
closure retains the spinorial central sign.  Thus the finite object has the
expected Spin/Tits-extension shape rather than a split copy of W(D4).
-/

namespace Integration.RationalOctonionSpin8WeylLift

open Integration.RationalOctonionTriality192
open Integration.F4D4StandardTrialityRecognition

private def p8
    (a b c d e f g h : Fin 8) : Fin 8 → Fin 8 := ![a,b,c,d,e,f,g,h]

private def s8
    (a b c d e f g h : Bool) : Fin 8 → Bool := ![a,b,c,d,e,f,g,h]

private def smap
    (p : Fin 8 → Fin 8) (n : Fin 8 → Bool) : SignedBasisMap := ⟨p,n⟩

/-- Lift of the central D4 simple reflection. -/
def liftCenter : TrialityTriple :=
  ⟨ smap (p8 0 1 4 5 2 3 6 7)
          (s8 false false false false false false false false),
    smap (p8 1 0 5 4 3 2 7 6)
          (s8 false true true false true false false true),
    smap (p8 1 0 5 4 3 2 7 6)
          (s8 true false true false true false false true) ⟩

/-- First outer D4 simple reflection. -/
def liftOuter0 : TrialityTriple :=
  ⟨ smap (p8 2 3 0 1 4 5 6 7)
          (s8 false false false false false false false false),
    smap (p8 3 2 1 0 5 4 7 6)
          (s8 false false true true true false false true),
    smap (p8 1 0 3 2 7 6 5 4)
          (s8 true false false true true false true false) ⟩

/-- Second outer D4 simple reflection. -/
def liftOuter1 : TrialityTriple :=
  ⟨ smap (p8 0 1 2 3 6 7 4 5)
          (s8 false false false false false false false false),
    smap (p8 3 2 1 0 5 4 7 6)
          (s8 true false true false false true false true),
    smap (p8 3 2 1 0 5 4 7 6)
          (s8 false false true true false true false true) ⟩

/-- Third outer D4 simple reflection. -/
def liftOuter2 : TrialityTriple :=
  ⟨ smap (p8 0 1 2 3 6 7 4 5)
          (s8 false false false false false true false true),
    smap (p8 1 0 3 2 7 6 5 4)
          (s8 true false false true true true false false),
    smap (p8 1 0 3 2 7 6 5 4)
          (s8 false true false true true true false false) ⟩

def spinLift : D4Simple → TrialityTriple
  | .center => liftCenter
  | .outer0 => liftOuter0
  | .outer1 => liftOuter1
  | .outer2 => liftOuter2

/-- All four lifts preserve the actual repo-native octonion triality tensor. -/
theorem spin_lifts_preserve_basis_triality :
    ∀ s, PreservesBasisTriality (spinLift s) := by
  native_decide

/-- Central spin sign: trivial on the vector component and `-I` on both
half-spinor components. -/
def centralZ : TrialityTriple :=
  ⟨ idMap,
    smap (p8 0 1 2 3 4 5 6 7)
          (s8 true true true true true true true true),
    smap (p8 0 1 2 3 4 5 6 7)
          (s8 true true true true true true true true) ⟩

def spinPow (g : TrialityTriple) : Nat → TrialityTriple
  | 0 => idTriple
  | n+1 => composeTriple g (spinPow g n)

theorem central_z_square : composeTriple centralZ centralZ = idTriple := by
  native_decide

/-- Each simple-reflection lift squares to the same central sign. -/
theorem simple_lifts_square_to_central_z :
    ∀ s, composeTriple (spinLift s) (spinLift s) = centralZ := by
  native_decide

/-- Coxeter relations hold projectively: connected products cube to either
`1` or the central sign, and disconnected products square to either `1` or the
central sign.  Hence the quotient by `<z>` has the D4 Coxeter presentation. -/
theorem projective_d4_coxeter_relations :
    let c := spinLift .center
    let a := spinLift .outer0
    let b := spinLift .outer1
    let d := spinLift .outer2
    (spinPow (composeTriple c a) 3 = centralZ) ∧
    (spinPow (composeTriple c b) 3 = centralZ) ∧
    (spinPow (composeTriple c d) 3 = idTriple) ∧
    (spinPow (composeTriple a b) 2 = idTriple) ∧
    (spinPow (composeTriple a d) 2 = idTriple) ∧
    (spinPow (composeTriple b d) 2 = centralZ) := by
  native_decide

/-- Closure under the four Spin lifts. -/
def expandSpinLift (S : Finset TrialityTriple) : Finset TrialityTriple :=
  S ∪ S.image (composeTriple liftCenter) ∪
      S.image (composeTriple liftOuter0) ∪
      S.image (composeTriple liftOuter1) ∪
      S.image (composeTriple liftOuter2)

def spinLiftClosureN : Nat → Finset TrialityTriple
  | 0 => {idTriple}
  | n+1 => expandSpinLift (spinLiftClosureN n)

def spinLift384 : Finset TrialityTriple := spinLiftClosureN 12

theorem spin_lift_closure_card_384 : spinLift384.card = 384 := by
  native_decide

theorem spin_lift_closure_stable : spinLiftClosureN 13 = spinLift384 := by
  native_decide

/-- Projection to the vector component. -/
def vectorImage : Finset SignedBasisMap := spinLift384.image TrialityTriple.left

/-- The vector projection forgets exactly the spinorial central double cover. -/
theorem vector_image_card_192 : vectorImage.card = 192 := by
  native_decide

/-- The central sign is genuinely nontrivial in the triple closure but invisible
on the vector component. -/
theorem central_z_nontrivial : centralZ ≠ idTriple := by
  native_decide

theorem central_z_in_closure : centralZ ∈ spinLift384 := by
  native_decide

/-- Corrected boundary relative to the earlier 192-candidate obstruction. -/
structure Boundary where
  fourExplicitSpinLiftsPaid : Bool
  literalOctonionTrialityPreservationPaid : Bool
  commonCentralSquarePaid : Bool
  projectiveD4CoxeterPaid : Bool
  spinLiftClosure384Paid : Bool
  vectorProjection192Paid : Bool
  previousSplit192CandidateStillRefuted : Bool
  signedMonomialRouteUniversallyBlocked : Bool
  quotientSameObjectWithFoldedD4Paid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  fourExplicitSpinLiftsPaid := true
  literalOctonionTrialityPreservationPaid := true
  commonCentralSquarePaid := true
  projectiveD4CoxeterPaid := true
  spinLiftClosure384Paid := true
  vectorProjection192Paid := true
  previousSplit192CandidateStillRefuted := true
  signedMonomialRouteUniversallyBlocked := false
  quotientSameObjectWithFoldedD4Paid := false

end Integration.RationalOctonionSpin8WeylLift
