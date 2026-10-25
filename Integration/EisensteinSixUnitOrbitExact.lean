import Integration.EisensteinAssociateClassCountExact
import Integration.EisensteinSixUnitsExact

namespace Dashi.EisensteinSixUnitOrbitExact

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinRepresentationCriterionExact
open Dashi.EisensteinSplitExponentChoiceExact
open Dashi.EisensteinChoiceRepresentativeExact
open Dashi.EisensteinChoiceRecoveryExact
open Dashi.EisensteinCanonicalAssociateExact
open Dashi.EisensteinSixUnitsExact

/-- Literal positive norm fibre, parameterized by the criterion receipt used to
construct its finite presentation. -/
def PositiveNormFiber
    (n : Nat) (_hn : 0 < n) (_H : InertEvenCondition n) :=
  {z : EisensteinQA // QuadraticAlgebra.norm z = n}

/-- The exact six-element unit code already classified by the repository. -/
def EisensteinUnitCode := {u : EisensteinQA // u ∈ eisensteinUnits}

instance : Fintype EisensteinUnitCode := Fintype.ofFinite _

/-- Unit choice × split-prime exponent choice. -/
def NormFiberCode (n : Nat) := EisensteinUnitCode × SplitChoice n

noncomputable instance normFiberCodeFintype (n : Nat) : Fintype (NormFiberCode n) :=
  inferInstance

/-- Every listed unit has norm one. -/
theorem unitCode_norm_one (u : EisensteinUnitCode) :
    QuadraticAlgebra.norm u.1 = 1 := by
  exact (isUnit_iff_norm_eq_one u.1).1
    (all_listed_units_are_units u.1 u.2)

/-- Canonical representatives of positive norm are nonzero. -/
theorem choiceRepresentative_ne_zero
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n)
    (c : SplitChoice n) : choiceRepresentative n H c ≠ 0 := by
  intro hzero
  have hnorm := choiceRepresentative_norm n hn H c
  rw [hzero] at hnorm
  simp at hnorm
  omega

/-- Multiplying by a unit does not change the associate class. -/
theorem unit_mul_associated_right
    (u x : EisensteinQA) (hu : IsUnit u) : Associated (u * x) x := by
  rcases hu with ⟨U, hU⟩
  refine ⟨U⁻¹, ?_⟩
  rw [← hU]
  simp [mul_assoc, mul_comm, mul_left_comm]

/-- Decode one unit orbit and one split choice into an actual lattice element. -/
noncomputable def decodeNormFiberCode
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n)
    (x : NormFiberCode n) : PositiveNormFiber n hn H :=
  ⟨x.1.1 * choiceRepresentative n H x.2, by
    rw [map_mul, unitCode_norm_one,
      choiceRepresentative_norm n hn H x.2]
    simp⟩

/-- The unit × split-choice encoding is injective.  Choice injectivity is paid
at the associate level first; cancellation by the nonzero canonical
representative then recovers the unit. -/
theorem decodeNormFiberCode_injective
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n) :
    Function.Injective (decodeNormFiberCode n hn H) := by
  intro x y hxy
  rcases x with ⟨u, c⟩
  rcases y with ⟨v, d⟩
  have huvEq :
      u.1 * choiceRepresentative n H c
        = v.1 * choiceRepresentative n H d := by
    exact congrArg Subtype.val hxy
  have huUnit : IsUnit u.1 := all_listed_units_are_units u.1 u.2
  have hvUnit : IsUnit v.1 := all_listed_units_are_units v.1 v.2
  have hleft : Associated
      (u.1 * choiceRepresentative n H c)
      (choiceRepresentative n H c) :=
    unit_mul_associated_right u.1 _ huUnit
  have hright : Associated
      (v.1 * choiceRepresentative n H d)
      (choiceRepresentative n H d) :=
    unit_mul_associated_right v.1 _ hvUnit
  have hmiddle : Associated
      (u.1 * choiceRepresentative n H c)
      (v.1 * choiceRepresentative n H d) := by
    rw [huvEq]
    exact Associated.refl _
  have hrepAssoc : Associated
      (choiceRepresentative n H c)
      (choiceRepresentative n H d) :=
    hleft.symm.trans (hmiddle.trans hright)
  have hcd : c = d := by
    by_contra hne
    exact choiceRepresentative_not_associated_of_ne n hn H c d hne hrepAssoc
  subst d
  have hrep0 : choiceRepresentative n H c ≠ 0 :=
    choiceRepresentative_ne_zero n hn H c
  have huv : u.1 = v.1 := by
    exact mul_right_cancel₀ hrep0 huvEq
  apply Prod.ext
  · exact Subtype.ext huv
  · rfl

/-- Every represented element is a unit multiple of the canonical
representative selected by its split-exponent observer. -/
theorem decodeNormFiberCode_surjective
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n) :
    Function.Surjective (decodeNormFiberCode n hn H) := by
  intro z
  let c : SplitChoice n := splitChoiceOfRepresentation z.1 n hn z.2
  let Hz : InertEvenCondition n :=
    (norm_representable_iff_inert_even n hn).1 ⟨z.1, z.2⟩
  have hHz : Hz = H := Subsingleton.elim _ _
  have hassoc0 := represented_element_associated_to_choiceRepresentative
    z.1 n hn z.2
  have hassoc : Associated z.1 (choiceRepresentative n H c) := by
    simpa [c, Hz, hHz] using hassoc0
  rcases hassoc with ⟨U, hU⟩
  let uval : EisensteinQA := (↑(U⁻¹) : EisensteinQA)
  have huUnit : IsUnit uval := by
    exact (U⁻¹).isUnit
  have huMem : uval ∈ eisensteinUnits :=
    (mem_eisensteinUnits_iff_isUnit uval).2 huUnit
  let code : NormFiberCode n := (⟨uval, huMem⟩, c)
  refine ⟨code, ?_⟩
  apply Subtype.ext
  change uval * choiceRepresentative n H c = z.1
  calc
    uval * choiceRepresentative n H c
        = uval * (z.1 * (U : EisensteinQA)) := by rw [← hU]
    _ = z.1 := by
      simp [uval, mul_assoc, mul_comm, mul_left_comm]

/-- Literal equivalence between the norm fibre and the six-unit orbit over the
split-choice parameter space. -/
noncomputable def normFiberCodeEquiv
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n) :
    NormFiberCode n ≃ PositiveNormFiber n hn H :=
  Equiv.ofBijective (decodeNormFiberCode n hn H)
    ⟨decodeNormFiberCode_injective n hn H,
      decodeNormFiberCode_surjective n hn H⟩

noncomputable instance positiveNormFiberFintype
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n) :
    Fintype (PositiveNormFiber n hn H) :=
  Fintype.ofEquiv (NormFiberCode n) (normFiberCodeEquiv n hn H)

/-- The explicit unit code really has cardinality six. -/
theorem card_eisensteinUnitCode : Fintype.card EisensteinUnitCode = 6 := by
  simpa [EisensteinUnitCode] using eisensteinUnits_card

/-- Exact literal norm-fibre cardinality on the representable branch. -/
theorem card_positiveNormFiber
    (n : Nat) (hn : 0 < n) (H : InertEvenCondition n) :
    Fintype.card (PositiveNormFiber n hn H)
      = 6 * ∏ p ∈ splitPrimeFactors n, (n.factorization p + 1) := by
  calc
    Fintype.card (PositiveNormFiber n hn H)
        = Fintype.card (NormFiberCode n) :=
          Fintype.card_congr (normFiberCodeEquiv n hn H).symm
    _ = Fintype.card EisensteinUnitCode * Fintype.card (SplitChoice n) := by
          simp [NormFiberCode]
    _ = 6 * ∏ p ∈ splitPrimeFactors n, (n.factorization p + 1) := by
          rw [card_eisensteinUnitCode, card_splitChoice]

structure EisensteinSixUnitOrbitBoundary where
  explicitSixUnitCodeReused : Bool := true
  unitTimesChoiceEncodingPaid : Bool := true
  encodingInjectivePaid : Bool := true
  encodingSurjectivePaid : Bool := true
  literalNormFiberEquivalencePaid : Bool := true
  literalNormFiberCardinalityPaid : Bool := true
  geometricBoundedEnumeratorWeldPaid : Bool := false
  divisorCharacterEqualityPaid : Bool := false

def canonicalBoundary : EisensteinSixUnitOrbitBoundary := {}

end Dashi.EisensteinSixUnitOrbitExact
