import Synthesis.MillenniumBSDCMOddPrimeRationalSquareSupportExact
import Synthesis.MillenniumBSDCMAllPrimeLocalFirstParityExact
import Synthesis.MillenniumBSDExplicitSelmerSubgroup
import Mathlib.Tactic

/-!
# BSD: actual all-place explicit 2-Selmer intersection equals torsion codes

This is a finite exact descent theorem on the ORIGINAL
explicitTwoSelmerSubgroup in the existing rational square-class pair,
not a synthetic candidate Boolean table.

* All-prime first local Kummer parity -> first class [1] or [-1].
* Odd-prime second local Kummer parity -> second class among
  [1],[-1],[2],[-2].
* Original archimedean real sign equality -> precisely the four pairs
  already inhabited by the four selected rational 2-torsion points.

The classical cohomological Selmer comparison and elliptic Sha[2]
long exact sequence remain separate obligations. Source-written only;
local Lean kernel has NOT been run.
-/

namespace Synthesis.Millennium.BSD

/-- Odd-prime local conditions force the SECOND global original
rational square class into four literal representatives. -/
theorem cmRationalSecondSquareClass_fourSupport_of_allLocalImages
    (c : RatSquareClass × RatSquareClass)
    (hloc :
      ∀ pv : Nat.Primes,
        letI : Fact pv.1.Prime := ⟨pv.2⟩
        localizeKummerPair pv.1 c ∈ LocalKummerImage pv.1) :
    c.2 = squareClassOf oneNZ ∨
    c.2 = squareClassOf negOneNZ ∨
    c.2 = squareClassOf twoNZ ∨
    c.2 = squareClassOf negTwoNZ := by
  rcases c with ⟨first, second⟩
  revert hloc
  refine Quotient.inductionOn second ?_
  intro a hloc
  apply cmRationalSquareClass_fourSupport_of_oddPrimeEven a
  intro p hp hne
  letI : Fact p.Prime := ⟨hp⟩
  have hmem :
      localizeKummerPair p (first, squareClassOf a) ∈
        LocalKummerImage p :=
    hloc (⟨p, hp⟩ : Nat.Primes)
  have hval :=
    cmQpOddLocalKummerImage_secondParity_zero
      (p := p) hne
      (localizeKummerPair p (first, squareClassOf a))
      hmem
  change
    cmQpSquareClassValuationParity p
      (localizeSquareClass p (squareClassOf a)) = 0 at hval
  have hcomm :=
    cmQpSquareClassParity_localize_rational_rep (p := p) a
  rw [hval] at hcomm
  have hcast :
      (padicValRat p (a : ℚ) : ZMod 2) = 0 := by
    simpa using hcomm.symm
  exact ZMod.intCast_eq_zero_iff_even.mp hcast

/-- All classes of the genuine original explicit Selmer subgroup
have second x-T class [1],[-1],[2], or [-2]. -/
theorem cmExplicitTwoSelmer_secondSquareClass_fourSupport
    (s : explicitTwoSelmerSubgroup) :
    ((s : RatSquareClass × RatSquareClass).2) =
        squareClassOf oneNZ ∨
    ((s : RatSquareClass × RatSquareClass).2) =
        squareClassOf negOneNZ ∨
    ((s : RatSquareClass × RatSquareClass).2) =
        squareClassOf twoNZ ∨
    ((s : RatSquareClass × RatSquareClass).2) =
        squareClassOf negTwoNZ := by
  have hloc :
      ∀ pv : Nat.Primes,
        letI : Fact pv.1.Prime := ⟨pv.2⟩
        localizeKummerPair pv.1
          (s : RatSquareClass × RatSquareClass) ∈
            LocalKummerImage pv.1 := s.property.2
  exact cmRationalSecondSquareClass_fourSupport_of_allLocalImages
    (s : RatSquareClass × RatSquareClass) hloc

/-- Original real sign equality rejects precisely the mismatched
first/second square-class signs. The survivors are four actual
torsion Kummer pairs, not a newly invented finite group. -/
theorem cmExplicitTwoSelmer_only_torsionKummer
    (s : explicitTwoSelmerSubgroup) :
    (s : RatSquareClass × RatSquareClass) =
        torsionKummer .infinity ∨
    (s : RatSquareClass × RatSquareClass) =
        torsionKummer .zero ∨
    (s : RatSquareClass × RatSquareClass) =
        torsionKummer .one ∨
    (s : RatSquareClass × RatSquareClass) =
        torsionKummer .negOne := by
  have hFirst :=
    cmExplicitTwoSelmer_firstSquareClass_unitSupport s
  have hSecond :=
    cmExplicitTwoSelmer_secondSquareClass_fourSupport s
  have hReal :
      squareClassSignBit
        ((s : RatSquareClass × RatSquareClass).1) =
      squareClassSignBit
        ((s : RatSquareClass × RatSquareClass).2) :=
    (by
      have h :
          realKummerLocalization (s : RatSquareClass × RatSquareClass) ∈
            RealKummerImage := s.property.1
      exact h)
  rcases s with ⟨⟨a, b⟩, hs⟩
  simp only [Prod.fst, Prod.snd, Subtype.coe_mk] at hFirst hSecond hReal ⊢
  rcases hFirst with hFirst | hFirst
  · rcases hSecond with hSecond | hSecond | hSecond | hSecond
    · exact Or.inl (by simpa [torsionKummer] using
        (Prod.ext hFirst hSecond))
    · have hbad : False := by
        simpa [hFirst, hSecond,
          squareClassSignBit_mk, oneNZ, negOneNZ,
          signBit_one, signBit_neg_one] using hReal
      exact hbad.elim
    · exact Or.inr (Or.inr (Or.inl (by
        simpa [torsionKummer] using (Prod.ext hFirst hSecond))))
    · have hbad : False := by
        simpa [hFirst, hSecond,
          squareClassSignBit_mk, oneNZ, negTwoNZ,
          signBit_one, signBit_neg_one] using hReal
      exact hbad.elim
  · rcases hSecond with hSecond | hSecond | hSecond | hSecond
    · have hbad : False := by
        simpa [hFirst, hSecond,
          squareClassSignBit_mk, negOneNZ, oneNZ,
          signBit_one, signBit_neg_one] using hReal
      exact hbad.elim
    · exact Or.inr (Or.inl (by
        simpa [torsionKummer] using (Prod.ext hFirst hSecond)))
    · have hbad : False := by
        simpa [hFirst, hSecond,
          squareClassSignBit_mk, negOneNZ, twoNZ,
          signBit_one, signBit_neg_one] using hReal
      exact hbad.elim
    · exact Or.inr (Or.inr (Or.inr (by
        simpa [torsionKummer] using (Prod.ext hFirst hSecond))))

/-- Exactly the selected four torsion Kummer PAIRS occur in the
original all-place explicit Selmer subgroup. This equality of
sets is a stronger original-object result than the earlier finite
16-code enumerator. It is NOT yet an isomorphism to the classical
cohomological 2-Selmer group. -/
theorem cmExplicitTwoSelmer_carrier_eq_four_torsion :
    (explicitTwoSelmerSubgroup : Set
      (RatSquareClass × RatSquareClass)) =
      {c | c = torsionKummer .infinity ∨
           c = torsionKummer .zero ∨
           c = torsionKummer .one ∨
           c = torsionKummer .negOne} := by
  ext c
  constructor
  · intro hc
    exact cmExplicitTwoSelmer_only_torsionKummer ⟨c, hc⟩
  · intro hc
    rcases hc with h | h | h | h
    · subst c
      exact torsionKummer_mem_explicitTwoSelmerSubgroup .infinity
    · subst c
      exact torsionKummer_mem_explicitTwoSelmerSubgroup .zero
    · subst c
      exact torsionKummer_mem_explicitTwoSelmerSubgroup .one
    · subst c
      exact torsionKummer_mem_explicitTwoSelmerSubgroup .negOne

end Synthesis.Millennium.BSD
