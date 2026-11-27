import Integration.RationalOctonionTriality192
import Mathlib

/-!
# Order-spectrum obstruction: 192 triality candidate is not W(D4)

The explicit signed-monomial triality closure has order 192, but group order is
not group recognition.  Compare its exact element-order spectrum with the
standard even-signed-permutation realization of W(D4).

The spectra differ, so this candidate cannot be the desired W(D4) triality
lift.  This forces the next construction to use a genuinely different
(non-monomial in this basis) Spin(8) triality representation, rather than
promoting the numerical order coincidence.
-/

namespace Integration.RationalOctonionTriality192Obstruction

open Integration.RationalOctonionTriality192

/-- Powers in the candidate triality group. -/
def triplePow (g : TrialityTriple) : Nat → TrialityTriple
  | 0 => idTriple
  | n+1 => composeTriple g (triplePow g n)

def candidateOrder2 (g : TrialityTriple) : Bool :=
  decide (g ≠ idTriple ∧ triplePow g 2 = idTriple)
def candidateOrder3 (g : TrialityTriple) : Bool :=
  decide (g ≠ idTriple ∧ triplePow g 3 = idTriple)
def candidateOrder4 (g : TrialityTriple) : Bool :=
  decide (triplePow g 4 = idTriple ∧ triplePow g 2 ≠ idTriple)
def candidateOrder6 (g : TrialityTriple) : Bool :=
  decide (triplePow g 6 = idTriple ∧ triplePow g 2 ≠ idTriple ∧ triplePow g 3 ≠ idTriple)

 theorem candidate_order2_count :
    (triality192.filter fun g => candidateOrder2 g).card = 39 := by native_decide
 theorem candidate_order3_count :
    (triality192.filter fun g => candidateOrder3 g).card = 32 := by native_decide
 theorem candidate_order4_count :
    (triality192.filter fun g => candidateOrder4 g).card = 24 := by native_decide
 theorem candidate_order6_count :
    (triality192.filter fun g => candidateOrder6 g).card = 96 := by native_decide

structure SignedMap4 where
  perm : Fin 4 → Fin 4
  neg : Fin 4 → Bool
  deriving DecidableEq, Repr, Fintype


def id4 : SignedMap4 := ⟨fun i=>i, fun _=>false⟩

def comp4 (a b : SignedMap4) : SignedMap4 where
  perm i := a.perm (b.perm i)
  neg i := xor (b.neg i) (a.neg (b.perm i))

/-- Finite predicate for a genuine signed permutation with even sign parity. -/
def isD4Weyl (g : SignedMap4) : Bool :=
  decide (Function.Injective g.perm) &&
    decide (((Finset.univ.filter fun i => g.neg i).card % 2) = 0)

/-- Standard W(D4): even signed permutations of four coordinates. -/
def standardWD4 : Finset SignedMap4 :=
  Finset.univ.filter fun g => isD4Weyl g

 theorem standard_wd4_card : standardWD4.card = 192 := by native_decide


def pow4 (g : SignedMap4) : Nat → SignedMap4
  | 0 => id4
  | n+1 => comp4 g (pow4 g n)

def order2_4 (g : SignedMap4) : Bool := decide (g ≠ id4 ∧ pow4 g 2 = id4)
def order3_4 (g : SignedMap4) : Bool := decide (g ≠ id4 ∧ pow4 g 3 = id4)
def order4_4 (g : SignedMap4) : Bool := decide (pow4 g 4 = id4 ∧ pow4 g 2 ≠ id4)
def order6_4 (g : SignedMap4) : Bool :=
  decide (pow4 g 6 = id4 ∧ pow4 g 2 ≠ id4 ∧ pow4 g 3 ≠ id4)

 theorem wd4_order2_count : (standardWD4.filter fun g => order2_4 g).card = 43 := by native_decide
 theorem wd4_order3_count : (standardWD4.filter fun g => order3_4 g).card = 32 := by native_decide
 theorem wd4_order4_count : (standardWD4.filter fun g => order4_4 g).card = 84 := by native_decide
 theorem wd4_order6_count : (standardWD4.filter fun g => order6_4 g).card = 32 := by native_decide

/-- Exact finite obstruction: equal cardinality 192 does not give group
recognition; the order spectra already disagree. -/
theorem candidate_not_wd4_by_order4_count :
    (triality192.filter fun g => candidateOrder4 g).card ≠
      (standardWD4.filter fun g => order4_4 g).card := by
  native_decide

structure Boundary where
  candidateOrder192Paid : Bool
  standardWD4Order192Paid : Bool
  candidateOrderSpectrumPaid : Bool
  standardWD4OrderSpectrumPaid : Bool
  candidateRefutedAsWD4 : Bool
  signedMonomialBasisRouteStillOpen : Bool
  nonMonomialSpin8RouteRequired : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  candidateOrder192Paid := true
  standardWD4Order192Paid := true
  candidateOrderSpectrumPaid := true
  standardWD4OrderSpectrumPaid := true
  candidateRefutedAsWD4 := true
  signedMonomialBasisRouteStillOpen := false
  nonMonomialSpin8RouteRequired := true

end Integration.RationalOctonionTriality192Obstruction
