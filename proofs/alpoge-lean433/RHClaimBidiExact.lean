import Development.AutomorphicArithmetic.CharacterBoxes.ClaimStrip
import Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter
import Formalism.GammaFactorNonvanishing.CritLine

/-!
# Actual original-claim BIDI at the shallowest common logical cut.

The original proof author already defines identical right-half-plane
nonvanishing targets as `Claim.HalfPlane` and `UpperTheory.EveryCharacter`.
The original `Claim.zeta_iff` is the exact `Claim.Zeta ↔ RiemannHypothesis`.
Consume these real source declarations, not a new RH ontology.

The immediate DASHI G2 signed-energy and projective-balance estimates are
DIFFERENT propositions and are not deductions of this equivalence.
This file intentionally supplies no bridge to those unrelated inequalities.
Source-written at Lean v4.33.1; kernel receipt pending. No CI.
-/

namespace DASHI.AlpogeRH.ClaimBidi

/-- The two original producer surfaces are definitionally identical. -/
theorem original_halfplane_iff_every_character :
    Claim.HalfPlane ↔ UpperTheory.EveryCharacter := Iff.rfl

/-- Exact original zeta target matches Mathlib RH: source proof, no proxy. -/
theorem original_zeta_iff_mathlib_rh :
    Claim.Zeta ↔ RiemannHypothesis := Claim.zeta_iff

/-- Forward steelman: all-character nonvanishing already produces RH. -/
theorem rh_of_original_halfplane (h : Claim.HalfPlane) :
    RiemannHypothesis :=
  Formalism.VW.rh_of_every
    (original_halfplane_iff_every_character.mp h)

/-- Reverse-solve: RH is the literal original zeta-claim target. -/
theorem original_zeta_of_rh (h : RiemannHypothesis) : Claim.Zeta :=
  original_zeta_iff_mathlib_rh.mpr h

theorem rh_of_original_zeta (h : Claim.Zeta) : RiemannHypothesis :=
  original_zeta_iff_mathlib_rh.mp h

#print axioms original_halfplane_iff_every_character
#print axioms original_zeta_iff_mathlib_rh
#print axioms rh_of_original_halfplane

end DASHI.AlpogeRH.ClaimBidi
