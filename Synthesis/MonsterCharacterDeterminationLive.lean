import Mathlib.RepresentationTheory.Character

/-!
# Live finite-character determination tail

Promoted from the earlier DASHI multiplicity probe.  For finite-group
representations over an algebraically closed nonmodular field, character inner
products determine Hom multiplicities of simple representations.

In particular, if an actual multiplicity representation `V` has character

  character(V) = character(T12) + character(T78)

with `T12` and `T78` simple and nonisomorphic, then each occurs with multiplicity
one and every third simple type has multiplicity zero.  Combined with Maschke
semisimplicity / the live isotypic assembly machinery, the abstract `12+78`
representation decomposition is therefore a compiler consequence of a SAME-
OBJECT character identity, not an additional Monster action-intertwiner input.

This owner does not construct the actual 6.Suz/normalizer multiplicity action,
orient zeta versus zeta^2, or transport the external selected-phase character
onto that actual action.
-/

namespace Synthesis.MonsterCharacterDeterminationLive

open CategoryTheory

noncomputable section

universe u

variable {k G : Type u}
variable [Field k] [Group G] [Fintype G]
variable [Invertible (Fintype.card G : k)] [IsAlgClosed k]

/-- Equal characters of simple finite-group representations force an
    equivariant isomorphism. -/
theorem nonemptyIsoOfCharacterEq
    (V W : FDRep k G) [Simple V] [Simple W]
    (hchar : V.character = W.character) :
    Nonempty (V ≅ W) := by
  classical
  by_contra hno
  have hVW := FDRep.char_orthonormal V W
  have hVV := FDRep.char_orthonormal V V
  rw [if_neg hno] at hVW
  have hself : Nonempty (V ≅ V) := ⟨Iso.refl V⟩
  rw [if_pos hself] at hVV
  rw [← hchar] at hVW
  exact one_ne_zero (hVV.symm.trans hVW)

/-- In a representation with character `T + S`, the simple type `T` occurs with
Hom multiplicity one. -/
theorem castFinrankHomLeftEqOneOfCharacterEqAdd
    (V T S : FDRep k G) [Simple T] [Simple S]
    (hTS : ¬ Nonempty (T ≅ S))
    (hchar : V.character = T.character + S.character) :
    (Module.finrank k (T ⟶ V) : k) = 1 := by
  classical
  rw [← FDRep.scalar_product_char_eq_finrank_equivariant T V, hchar]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, smul_add]
  have hTT := FDRep.char_orthonormal T T
  have hST := FDRep.char_orthonormal S T
  have hTself : Nonempty (T ≅ T) := ⟨Iso.refl T⟩
  have hSTno : ¬ Nonempty (S ≅ T) := by
    intro h
    exact hTS ⟨h.some.symm⟩
  rw [if_pos hTself] at hTT
  rw [if_neg hSTno] at hST
  rw [hTT, hST]
  simp

/-- Symmetric one-copy multiplicity for `S`. -/
theorem castFinrankHomRightEqOneOfCharacterEqAdd
    (V T S : FDRep k G) [Simple T] [Simple S]
    (hTS : ¬ Nonempty (T ≅ S))
    (hchar : V.character = T.character + S.character) :
    (Module.finrank k (S ⟶ V) : k) = 1 := by
  classical
  rw [← FDRep.scalar_product_char_eq_finrank_equivariant S V, hchar]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, smul_add]
  have hTSorth := FDRep.char_orthonormal T S
  have hSS := FDRep.char_orthonormal S S
  have hSself : Nonempty (S ≅ S) := ⟨Iso.refl S⟩
  rw [if_neg hTS] at hTSorth
  rw [if_pos hSself] at hSS
  rw [hTSorth, hSS]
  simp

/-- Every third simple type absent from the two-term character has zero Hom
multiplicity. -/
theorem castFinrankHomOtherEqZeroOfCharacterEqAdd
    (V T S U : FDRep k G) [Simple T] [Simple S] [Simple U]
    (hUT : ¬ Nonempty (U ≅ T))
    (hUS : ¬ Nonempty (U ≅ S))
    (hchar : V.character = T.character + S.character) :
    (Module.finrank k (U ⟶ V) : k) = 0 := by
  classical
  rw [← FDRep.scalar_product_char_eq_finrank_equivariant U V, hchar]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, smul_add]
  have hTU := FDRep.char_orthonormal T U
  have hSU := FDRep.char_orthonormal S U
  have hTUno : ¬ Nonempty (T ≅ U) := by
    intro h
    exact hUT ⟨h.some.symm⟩
  have hSUno : ¬ Nonempty (S ≅ U) := by
    intro h
    exact hUS ⟨h.some.symm⟩
  rw [if_neg hTUno] at hTU
  rw [if_neg hSUno] at hSU
  rw [hTU, hSU]
  simp

structure Boundary where
  equalSimpleCharacterClassifierSourceWritten : Bool
  twoSimpleCharacterMultiplicitySourceWritten : Bool
  otherSimpleMultiplicityZeroSourceWritten : Bool
  maschkeMakesCharacterMultiplicityRepresentationDetermining : Bool
  twelveSeventyEightIntertwinerStillIndependentInput : Bool
  actualSuzukiMultiplicityActionPaidHere : Bool
  absoluteZetaOrientationPaidHere : Bool
  actualSuzukiMultiplicityCharacterTransportPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  equalSimpleCharacterClassifierSourceWritten := true
  twoSimpleCharacterMultiplicitySourceWritten := true
  otherSimpleMultiplicityZeroSourceWritten := true
  maschkeMakesCharacterMultiplicityRepresentationDetermining := true
  twelveSeventyEightIntertwinerStillIndependentInput := false
  actualSuzukiMultiplicityActionPaidHere := false
  absoluteZetaOrientationPaidHere := false
  actualSuzukiMultiplicityCharacterTransportPaidHere := false

end

end Synthesis.MonsterCharacterDeterminationLive
