import Synthesis.MillenniumBSDCMSupportedSquareClassFiniteCandidatesExact
import Mathlib.Tactic

/-!
# CM BSD: real-sign candidate quotient by explicit rational two-torsion

The existing geometric Kummer source records the selected rational torsion
Kummer square-class representatives in x-T order:

  O       -> (1,1)
  (0,0)   -> (-1,-1)
  (1,0)   -> (1,2)
  (-1,0)  -> (-1,-2).

The entries in this file are *finite bit encodings* of precisely those
four pairs. The equality of the finite encodings to the original Galois
cohomology classes remains a separate same-object theorem.

For the S={2,infinity} candidates, the necessary real-sign condition
has eight codes. The four torsion Kummer codes form one four-element
subset and the other four codes form a disjoint coset. The remaining
numerical cut is to exclude that coset by actual local Kummer tests,
especially at 2, and to identify these candidates with the original
cohomological Selmer.

NO theorem here claims the other coset is actually 2-adically excluded,
or concludes Selmer cardinality four from the finite encodings alone.
-/

namespace Synthesis.Millennium.BSD

/-- Finite x-T code for infinity, the Kummer identity. -/
def cmInfinityXTCode : CMSupportedSquareClassPairBits :=
  ((false, false), (false, false))

/-- Finite x-T code for (0,0): (-1,-1). -/
def cmZeroTorsionXTCode : CMSupportedSquareClassPairBits :=
  ((true, false), (true, false))

/-- Finite x-T code for (1,0): (1,2). -/
def cmOneTorsionXTCode : CMSupportedSquareClassPairBits :=
  ((false, false), (false, true))

/-- Finite x-T code for (-1,0): (-1,-2). -/
def cmMinusOneTorsionXTCode : CMSupportedSquareClassPairBits :=
  ((true, false), (true, true))

/-- Precisely the four selected finite Kummer torsion codes. -/
def cmTorsionXTCodes : Finset CMSupportedSquareClassPairBits :=
  {cmInfinityXTCode, cmZeroTorsionXTCode,
    cmOneTorsionXTCode, cmMinusOneTorsionXTCode}

/-- The torsion set has exactly four distinct bit codes. -/
theorem cmTorsionXTCodes_card :
    cmTorsionXTCodes.card = 4 := by
  decide

/-- Torsion encodings satisfy the necessary real-sign relation. -/
theorem cmTorsionXTCodes_realSign
    (c : CMSupportedSquareClassPairBits)
    (hc : c ∈ cmTorsionXTCodes) :
    cmRealSignCompatibleCandidate c := by
  rcases c with ⟨⟨s₁, v₁⟩, ⟨s₂, v₂⟩⟩
  cases s₁ <;> cases v₁ <;> cases s₂ <;> cases v₂ <;> decide at hc ⊢

/-- On the eight real-sign-compatible codes, the torsion subset is
identified by the 2-valuation parity of the *first* x-T coordinate.
This is a finite identity, NOT a theorem that p=2 excludes all others. -/
theorem cmTorsionXTCodes_iff_realSign_and_firstParityZero
    (c : CMSupportedSquareClassPairBits) :
    c ∈ cmTorsionXTCodes ↔
      cmRealSignCompatibleCandidate c ∧ c.1.2 = false := by
  rcases c with ⟨⟨s₁, v₁⟩, ⟨s₂, v₂⟩⟩
  cases s₁ <;> cases v₁ <;> cases s₂ <;> cases v₂ <;> decide

/-- Exactly four of the eight real-sign candidates lie outside the
finite torsion-code subset. -/
theorem cmRealSign_nonTorsionCodes_card :
    (Finset.univ.filter
      (fun c : CMSupportedSquareClassPairBits =>
        cmRealSignCompatibleCandidate c ∧
          c ∉ cmTorsionXTCodes)).card = 4 := by
  decide

/-- The explicit pair (2,1) is merely a code witness for the second
coset; it is NOT a claim that a rational elliptic point has that x-T
Kummer image. -/
def cmAlternativeCosetCode : CMSupportedSquareClassPairBits :=
  ((false, true), (false, false))

theorem cmAlternativeCosetCode_realSign :
    cmRealSignCompatibleCandidate cmAlternativeCosetCode := by
  decide

theorem cmAlternativeCosetCode_not_torsion :
    cmAlternativeCosetCode ∉ cmTorsionXTCodes := by
  decide

/-- Finite structural reduction: any candidate predicate supported in
the real-sign sieve and excluding all four non-torsion codes is supported
entirely on the four torsion codes. This is the exact finite consumer of
the outstanding genuine 2-adic image theorem. -/
theorem cmFilter_supported_on_torsion
    (valid : CMSupportedSquareClassPairBits → Prop)
    (hReal : ∀ c, valid c → cmRealSignCompatibleCandidate c)
    (hExclude :
      ∀ c, cmRealSignCompatibleCandidate c →
        c ∉ cmTorsionXTCodes → ¬ valid c)
    (c : CMSupportedSquareClassPairBits)
    (hc : valid c) :
    c ∈ cmTorsionXTCodes := by
  by_contra hn
  exact (hExclude c (hReal c hc) hn) hc

/-- If, in addition, all four torsion codes are genuinely in the
candidate predicate, the predicate equals the finite torsion-code set.
This theorem does not assert that the actual Selmer group is such a
predicate or that its image is the finite code space. -/
theorem cmFilter_eq_torsion_of_local_certificate
    (valid : CMSupportedSquareClassPairBits → Prop)
    (hReal : ∀ c, valid c → cmRealSignCompatibleCandidate c)
    (hExclude :
      ∀ c, cmRealSignCompatibleCandidate c →
        c ∉ cmTorsionXTCodes → ¬ valid c)
    (hTorsion : ∀ c, c ∈ cmTorsionXTCodes → valid c)
    (c : CMSupportedSquareClassPairBits) :
    valid c ↔ c ∈ cmTorsionXTCodes := by
  constructor
  · exact cmFilter_supported_on_torsion valid hReal hExclude c
  · exact hTorsion c

end Synthesis.Millennium.BSD
