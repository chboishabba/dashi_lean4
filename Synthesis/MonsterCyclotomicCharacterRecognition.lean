import Integration.FiniteCharacterDeterminesSimpleRep
import Mathlib.RepresentationTheory.FinGroupCharZero
import Synthesis.MonsterActualMultiplicityCharacter

/-!
# Character recognition directly over the original cyclotomic field

No algebraic closure or scalar extension is needed for the rank-one source
blocks. Reuse the pinned mathlib character/Hom dimension identity and the
existing Integration.FiniteCharacterDeterminesSimpleRep constructor.

The proof of simpleOfEndRankOne is the reverse implication of Sophie Morel's
FDRep.simple_iff_end_is_rank_one in Mathlib/RepresentationTheory/FinGroupCharZero.lean,
pinned revision 8f9d9cff6bd728b17a24e163c9402775d9e6a365 (Apache 2.0).
That direction uses only Maschke/injectivity, not IsAlgClosed. The converse
is NOT asserted over an arbitrary field. DASHI contribution: remove that
unneeded hypothesis for the source norm-one consumer and attach actual Hom.
Source-written; no local Lean kernel available.
-/

namespace Synthesis.MonsterCyclotomicCharacterRecognition
open CategoryTheory Limits
noncomputable section
universe u
variable {k G : Type u} [Field k] [Group G] [Fintype G]
variable [CharZero k]
variable [Invertible (Fintype.card G : k)] [Invertible (Nat.card G : k)]
variable [NeZero (Nat.card G : k)]

/-- Adapted from Sophie Morel, mathlib, cited above. Only the sufficiency
direction of the original algebraically-closed theorem is used. -/
theorem simpleOfEndRankOne (V : FDRep k G)
    (h : Module.finrank k (V ⟶ V) = 1) : Simple V := by
  refine { mono_isIso_iff_nonzero {W} f _ := ⟨fun hf habs ↦ ?_, fun hf ↦ ?_⟩ }
  · rw [habs, isIsoZero_iff_source_target_isZero] at hf
    obtain ⟨g, hg⟩ : ∃ g : V ⟶ V, g ≠ 0 :=
      (Module.finrank_pos_iff_exists_ne_zero (R := k)).mp (by grind)
    exact hg (hf.2.eq_zero_of_src g)
  · suffices Epi f by exact isIso_of_mono_of_epi f
    suffices Epi (Abelian.image.ι f) by
      rw [← Abelian.image.fac f]
      exact epi_comp _ _
    rw [← Abelian.image.fac f] at hf
    set ι := Abelian.image.ι f
    set φ := Injective.factorThru (𝟙 _) ι
    have hφι : φ ≫ ι ≠ 0 := by
      intro habs
      have hιφ : 𝟙 _ = ι ≫ φ := (Injective.comp_factorThru (𝟙 _) ι).symm
      apply_fun (· ≫ ι) at hιφ
      simp_all
    obtain ⟨c, hc⟩ : ∃ c : k, c • _ = 𝟙 V :=
      (finrank_eq_one_iff_of_nonzero' _ hφι).mp h (𝟙 V)
    refine Preadditive.epi_of_cancel_zero _ (fun g hg ↦ ?_)
    apply_fun (· ≫ g) at hc
    simpa [hg] using hc.symm

/-- Pinned mathlib uses invOf and Fintype.card, not the later Nat.card API. -/
def pairing (a b : G → k) : k :=
  ⅟(Fintype.card G : k) • ∑ g : G, b g * a g⁻¹

theorem pairing_hom (V W : FDRep k G) :
    pairing V.character W.character = (Module.finrank k (V ⟶ W) : k) :=
  FDRep.scalar_product_char_eq_finrank_equivariant V W

theorem endRankOneOfNorm (V : FDRep k G)
    (h : pairing V.character V.character = 1) :
    Module.finrank k (V ⟶ V) = 1 := by
  have hh := (pairing_hom V V).symm.trans h
  exact_mod_cast hh

theorem normOneOfEndRank (V : FDRep k G)
    (h : Module.finrank k (V ⟶ V) = 1) :
    pairing V.character V.character = 1 := by
  rw [pairing_hom, h, Nat.cast_one]

/-- A source norm-one row and SAME actual character equality suffice to
construct both simple objects and an actual K-linear equivariant iso. -/
theorem isoOfNormOneAndCharacter (V T : FDRep k G)
    (hsource : pairing T.character T.character = 1)
    (hchar : V.character = T.character) : Nonempty (T ≅ V) := by
  letI : Simple T := simpleOfEndRankOne T (endRankOneOfNorm T hsource)
  letI : Simple V := simpleOfEndRankOne V
    (endRankOneOfNorm V (by rw [hchar]; exact hsource))
  exact Integration.FiniteCharacterDeterminesSimpleRep.isoOfEqualCharacters T V hchar.symm

/-- Independent source and target Hom gauges are lines over K itself. -/
theorem crossHomRankOne (V T : FDRep k G)
    (hsource : pairing T.character T.character = 1)
    (hchar : V.character = T.character) :
    Module.finrank k (T ⟶ V) = 1 := by
  have h := (pairing_hom T V).symm
  rw [hchar, hsource] at h
  exact_mod_cast h

/-- Every nonzero point of that intrinsic Hom line is an isomorphism.
No chosen numerical seed or extension-field coefficient is required. -/
theorem nonzeroHomIsIso (V T : FDRep k G)
    (hsource : pairing T.character T.character = 1)
    (hchar : V.character = T.character)
    (f : T ⟶ V) (hf : f ≠ 0) : IsIso f := by
  letI : Simple T := simpleOfEndRankOne T (endRankOneOfNorm T hsource)
  letI : Simple V := simpleOfEndRankOne V
    (endRankOneOfNorm V (by rw [hchar]; exact hsource))
  exact CategoryTheory.isIso_of_hom_simple hf

/-- The parity split already has separate 12 and 78 carriers. These two
character identities produce both actual ordinary equivalences directly in K.
Their independent gauges are not equated. -/
theorem twoBlocks (V12 V78 T12 T78 : FDRep k G)
    (n12 : pairing T12.character T12.character = 1)
    (n78 : pairing T78.character T78.character = 1)
    (h12 : V12.character = T12.character)
    (h78 : V78.character = T78.character) :
    Nonempty (T12 ≅ V12) ∧ Nonempty (T78 ≅ V78) :=
  ⟨isoOfNormOneAndCharacter V12 T12 n12 h12,
   isoOfNormOneAndCharacter V78 T78 n78 h78⟩

end
end Synthesis.MonsterCyclotomicCharacterRecognition
