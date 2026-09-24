import Mathlib.RepresentationTheory.Character

/-!
# Monster character-determination donor

Small cross-prover theorems used by the DASHI Monster 3B Stone--von Neumann lane.

The mathematical inputs are mathlib's `FDRep.char_orthonormal` and
`FDRep.scalar_product_char_eq_finrank_equivariant`.  We do not re-prove
Maschke's theorem or Schur's lemma here.

This module stays generic representation theory.  It does not identify any
particular Monster, extraspecial, zeta-sector, or Base369 carrier.
-/

namespace Synthesis

open CategoryTheory

noncomputable section

universe u

variable {k G : Type u}
variable [Field k] [Group G] [Fintype G]
variable [Invertible (Fintype.card G : k)] [IsAlgClosed k]

/-- Equal characters of simple finite-group representations force an
    equivariant isomorphism. -/
theorem nonempty_iso_of_character_eq
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

/-- If the character of `V` is the sum of two non-isomorphic simple
    characters, the first simple occurs with equivariant-Hom multiplicity one.

    The result is stated after casting `finrank` to the coefficient field; this
    is exactly the codomain of mathlib's character inner-product theorem and
    avoids adding an unnecessary characteristic-zero hypothesis. -/
theorem cast_finrank_hom_left_eq_one_of_character_eq_add
    (V T S : FDRep k G) [Simple T] [Simple S]
    (hTS : ¬ Nonempty (T ≅ S))
    (hchar : V.character = T.character + S.character) :
    (Module.finrank k (T ⟶ V) : k) = 1 := by
  classical
  rw [← FDRep.scalar_product_char_eq_finrank_equivariant T V]
  rw [hchar]
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

/-- Symmetric companion of
    `cast_finrank_hom_left_eq_one_of_character_eq_add`. -/
theorem cast_finrank_hom_right_eq_one_of_character_eq_add
    (V T S : FDRep k G) [Simple T] [Simple S]
    (hTS : ¬ Nonempty (T ≅ S))
    (hchar : V.character = T.character + S.character) :
    (Module.finrank k (S ⟶ V) : k) = 1 := by
  classical
  rw [← FDRep.scalar_product_char_eq_finrank_equivariant S V]
  rw [hchar]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, smul_add]
  have hTSorth := FDRep.char_orthonormal T S
  have hSS := FDRep.char_orthonormal S S
  have hSself : Nonempty (S ≅ S) := ⟨Iso.refl S⟩
  rw [if_neg hTS] at hTSorth
  rw [if_pos hSself] at hSS
  rw [hTSorth, hSS]
  simp

/-- Every third simple character absent from `T + S` has equivariant-Hom
    multiplicity zero in `V`. -/
theorem cast_finrank_hom_other_eq_zero_of_character_eq_add
    (V T S U : FDRep k G) [Simple T] [Simple S] [Simple U]
    (hUT : ¬ Nonempty (U ≅ T))
    (hUS : ¬ Nonempty (U ≅ S))
    (hchar : V.character = T.character + S.character) :
    (Module.finrank k (U ⟶ V) : k) = 0 := by
  classical
  rw [← FDRep.scalar_product_char_eq_finrank_equivariant U V]
  rw [hchar]
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

end

end Synthesis
