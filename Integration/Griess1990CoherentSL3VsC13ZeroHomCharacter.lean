import Integration.Griess1990MoufangCoherentSL3Section
import Mathlib.RepresentationTheory.Character
import Mathlib

/-!
# STEELMAN/BIDI max-cut: zero equivariant maps for full Griess SL3(3),
# but 52-dimensional equivariant Hom for the selected C13 restriction.

**ORIGINAL authorship**:
- Chih-Han Sah (1974), J. Algebra 29, 255-302, prior cohomology.
- R. L. Griess Jr. (1976), Pacific J. Math. 63, 405-409,
  DOI 10.2140/pjm.1976.63.405, actual abstract splitting.
- R. L. Griess Jr. (1990), J. Algebra 131, 281-293,
  DOI 10.1016/0021-8693(90)90176-O, this particular original
  Moufang order81, 27-dimensional exceptional Albert algebra.
- Classical Maschke/Schur character orthogonality, not DASHI theory.
- Mathlib's RepresentationTheory.Character and its original
  formalisation authors (e.g. Antoine Labelle); reuse its actual
  'FDRep.scalar_product_char_eq_finrank_equivariant' owner, not
  source-written fake character axioms.

The independently rerun ACTUAL original Griess 81-loop section has
5616 automorphisms and was evaluated in TWO independent ways,
giving five JOINT character bins on the literal same group:
 (χ_J0, χ_grade26, count):
   ( 26,26,1), (2,2,819), (0,0,3132), (-1,2,1560), (-1,8,104).
This is stronger than the earlier individual squared norms
χ_J0²=5616, χ_grade²=3*5616:
           Σ_g χ_J0(g) χ_grade26(g) = 0.
Thus by standard character theory the complex equivariant Hom
of actual irreducible Jordan traceless26 and rationalised original
nonzero-grade26 permutation module is ZERO in BOTH directions.
In particular, no nonzero equivariant map, not merely no invertible
intertwiner, for this specified coherent full SL3 section.
All 27 source-character-conjugate complements are equivalent
by original kernel conjugation, so this selected-section obstruction
persists for the source-allowed family.

Meanwhile the coherent three-shear source word has order13;
both 26D characters on its subgroup C13 have value 26 at identity
and 0 on all twelve other elements. The equivariant Hom under
C13 has complex dimension 26²/13 = 52. An explicit invertible
rational 26×26 C13 intertwiner was separately paid earlier.
No physical/Jordan product/P3³-graph/Monster VOA claim follows.

STATUS / dependency discipline:
- The FIVE-BIN arithmetic below is a fully finite Lean proof target.
- Its identification with the ACTUAL source section's character
  functions requires a future Lean/Agda kernel group/action witness,
  NOT supplied by a printed histogram or a synthetic character.
- The conditional theorem consumes the actual Mathlib character
  orthogonality/equivariant-Hom statement, not a new axiom.
- No Lean/Lake executable was available here; source-written,
  NOT kernel-checked. Independently executed local finite solver PASS.
-/

namespace Integration.Griess1990CoherentSL3VsC13ZeroHomCharacter

/-- Five independently computed exact original-source joint bins.
This is the signed numerator, avoiding any rounding or division. -/
theorem source_joint_character_numerator_zero :
    (26:ℤ)*26 + 819*2*2 + 3132*0*0 +
      1560*(-1)*2 + 104*(-1)*8 = 0 := by
  norm_num

theorem source_original_J0_character_norm :
    (26:ℤ)^2 + 819*2^2 + 3132*0^2 +
      1560*(-1)^2 + 104*(-1)^2 = 5616 := by
  norm_num

theorem source_grade_permutation_character_norm :
    (26:ℤ)^2 + 819*2^2 + 3132*0^2 +
      1560*2^2 + 104*8^2 = 3*5616 := by
  norm_num

/-- Coherent C13 cyclic Hom dimension computed from actual
  (26,0,...,0) character in BOTH degree-26 modules. -/
theorem source_C13_character_hom_dimension :
    (26*26 : ℕ) = 13*52 := by
  norm_num

/-- Mathlib's existing general theorem does ALL of the theory.
To APPLY this lemma to the original M81 data, one must still build
both ACTUAL FDRep objects and kernel-prove their 5616 joint
character bins; hsum is deliberately an unpaid proof parameter.
This guards against promoting local Python into a Lean proof. -/
theorem equivariant_hom_finrank_zero_of_source_character_sum
    {G : Type*} [Group G] [Fintype G]
    (V W : FDRep ℂ G)
    (hsum : (∑ g : G, W.character g * V.character g⁻¹) = 0) :
    Module.finrank ℂ (V ⟶ W) = 0 := by
  have h := FDRep.scalar_product_char_eq_finrank_equivariant V W
  rw [hsum] at h
  simpa using h.symm

end Integration.Griess1990CoherentSL3VsC13ZeroHomCharacter
