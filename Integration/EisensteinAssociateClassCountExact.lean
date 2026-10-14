import Integration.EisensteinCanonicalAssociateExact

namespace Dashi.EisensteinAssociateClassCountExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinRepresentationCriterionExact
open Dashi.EisensteinSplitExponentChoiceExact
open Dashi.EisensteinChoiceRepresentativeExact
open Dashi.EisensteinChoiceRecoveryExact
open Dashi.EisensteinCanonicalAssociateExact

/-- Positive norm-`n` associate classes, kept as literal `Associates` values
with a witness that the class contains a norm-`n` Eisenstein integer.  The
positivity and inert-even proofs are explicit parameters so this finite type is
only constructed on the represented branch. -/
def NormAssociateClass
    (n : Nat) (_hn : 0 < n) (_H : InertEvenCondition n) :=
  {a : Associates EisensteinQA //
    ∃ z : EisensteinQA,
      QuadraticAlgebra.norm z = n ∧ Associates.mk z = a}

noncomputable def normClassRepresentative
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n)
    (a : NormAssociateClass n hn H) : EisensteinQA :=
  Classical.choose a.property

theorem normClassRepresentative_norm
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n)
    (a : NormAssociateClass n hn H) :
    QuadraticAlgebra.norm (normClassRepresentative n hn H a) = n :=
  (Classical.choose_spec a.property).1

theorem normClassRepresentative_mk
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n)
    (a : NormAssociateClass n hn H) :
    Associates.mk (normClassRepresentative n hn H a) = a.1 :=
  (Classical.choose_spec a.property).2

noncomputable def choiceToNormAssociateClass
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n)
    (c : SplitChoice n) : NormAssociateClass n hn H :=
  ⟨Associates.mk (choiceRepresentative n H c),
    ⟨choiceRepresentative n H c,
      choiceRepresentative_norm n hn H c, rfl⟩⟩

noncomputable def normAssociateClassToChoice
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n)
    (a : NormAssociateClass n hn H) : SplitChoice n :=
  splitChoiceOfRepresentation
    (normClassRepresentative n hn H a) n hn
    (normClassRepresentative_norm n hn H a)

/-- Split choices and positive norm-`n` associate classes are exactly the same
finite information. -/
noncomputable def normAssociateClassEquivSplitChoice
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n) :
    SplitChoice n ≃ NormAssociateClass n hn H where
  toFun := choiceToNormAssociateClass n hn H
  invFun := normAssociateClassToChoice n hn H
  left_inv := by
    intro c
    let a := choiceToNormAssociateClass n hn H c
    let z := normClassRepresentative n hn H a
    have hzNorm : QuadraticAlgebra.norm z = n :=
      normClassRepresentative_norm n hn H a
    have hzMk : Associates.mk z = Associates.mk (choiceRepresentative n H c) := by
      simpa [a, choiceToNormAssociateClass] using
        normClassRepresentative_mk n hn H a
    have hassoc : Associated z (choiceRepresentative n H c) :=
      Associates.quot_mk_eq_mk_iff.mp hzMk
    have hchoice := splitChoiceOfRepresentation_eq_of_associated
      z (choiceRepresentative n H c) n hn hzNorm
      (choiceRepresentative_norm n hn H c) hassoc
    change normAssociateClassToChoice n hn H a = c
    dsimp [normAssociateClassToChoice, z]
    rw [hchoice]
    exact splitChoice_choiceRepresentative n hn H c
  right_inv := by
    intro a
    apply Subtype.ext
    let z := normClassRepresentative n hn H a
    let hz : QuadraticAlgebra.norm z = n :=
      normClassRepresentative_norm n hn H a
    let c : SplitChoice n := splitChoiceOfRepresentation z n hn hz
    let Hz : InertEvenCondition n :=
      (norm_representable_iff_inert_even n hn).1 ⟨z, hz⟩
    have hHz : Hz = H := Subsingleton.elim _ _
    have hassoc0 := represented_element_associated_to_choiceRepresentative z n hn hz
    have hassoc : Associated z (choiceRepresentative n H c) := by
      simpa [c, Hz, hHz] using hassoc0
    have hmk : Associates.mk z = Associates.mk (choiceRepresentative n H c) :=
      Associates.quot_mk_eq_mk_iff.mpr hassoc
    have hrep : Associates.mk z = a.1 :=
      normClassRepresentative_mk n hn H a
    change Associates.mk (choiceRepresentative n H
      (normAssociateClassToChoice n hn H a)) = a.1
    simpa [normAssociateClassToChoice, z, hz, c] using hmk.symm.trans hrep

noncomputable instance normAssociateClassFintype
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n) :
    Fintype (NormAssociateClass n hn H) :=
  Fintype.ofEquiv (SplitChoice n)
    (normAssociateClassEquivSplitChoice n hn H)

/-- Exact associate-class count: one class for each independent split-prime
exponent choice. -/
theorem card_normAssociateClass
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n) :
    Fintype.card (NormAssociateClass n hn H)
      = ∏ p ∈ splitPrimeFactors n, (n.factorization p + 1) := by
  calc
    Fintype.card (NormAssociateClass n hn H)
        = Fintype.card (SplitChoice n) :=
          Fintype.card_congr (normAssociateClassEquivSplitChoice n hn H).symm
    _ = ∏ p ∈ splitPrimeFactors n, (n.factorization p + 1) :=
      card_splitChoice n

structure EisensteinAssociateClassCountBoundary where
  literalAssociateClassCarrierPaid : Bool := true
  splitChoiceEquivalencePaid : Bool := true
  exactProductCardinalityPaid : Bool := true
  sixUnitOrbitLiftPaid : Bool := false
  geometricCoordinateFiberPaid : Bool := false

def canonicalBoundary : EisensteinAssociateClassCountBoundary := {}

end Dashi.EisensteinAssociateClassCountExact
