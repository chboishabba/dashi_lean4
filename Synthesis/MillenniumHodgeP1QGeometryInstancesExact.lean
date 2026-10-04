import Synthesis.MillenniumHodgeP1QRulingCyclesExact
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Hodge max-cut: selected P¹ geometry instances

The two ruling maps are literal sections of the two pullback projections.
Because the selected Proj structure morphism is separated, both pullback
projections are separated.  A section of a separated morphism is a closed
immersion (`IsClosedImmersion.of_comp` applied to the identity composite),
and closed immersions are quasi-compact.  This discharges the pushforward
properness requirement without introducing an auxiliary projective-space
carrier or a synthetic ruling model.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

/-- The displayed `P¹_Q -> Spec Q` map is separated: it is the canonical
`Proj.toSpecZero` map followed by a scheme isomorphism. -/
noncomputable instance p1QToSpecQ_isSeparated : IsSeparated p1QToSpecQ := by
  dsimp [p1QToSpecQ, p1QToGradeZeroSpec, P1QScheme]
  infer_instance

/-- The first pullback projection is separated by base change. -/
noncomputable instance p1QPullbackFst_isSeparated :
    IsSeparated (pullback.fst p1QToSpecQ p1QToSpecQ) := by
  infer_instance

/-- The second pullback projection is separated by base change. -/
noncomputable instance p1QPullbackSnd_isSeparated :
    IsSeparated (pullback.snd p1QToSpecQ p1QToSpecQ) := by
  infer_instance

/-- The first ruling is a genuine closed immersion because it is a section of
`pullback.fst`, a separated morphism. -/
noncomputable instance p1QRulingOne_isClosedImmersion :
    IsClosedImmersion p1QRulingOne := by
  haveI : IsClosedImmersion
      (p1QRulingOne ≫ pullback.fst p1QToSpecQ p1QToSpecQ) := by
    rw [p1QRulingOne_fst]
    infer_instance
  exact IsClosedImmersion.of_comp
    p1QRulingOne (pullback.fst p1QToSpecQ p1QToSpecQ)

/-- The second ruling is likewise a genuine closed immersion. -/
noncomputable instance p1QRulingTwo_isClosedImmersion :
    IsClosedImmersion p1QRulingTwo := by
  haveI : IsClosedImmersion
      (p1QRulingTwo ≫ pullback.snd p1QToSpecQ p1QToSpecQ) := by
    rw [p1QRulingTwo_snd]
    infer_instance
  exact IsClosedImmersion.of_comp
    p1QRulingTwo (pullback.snd p1QToSpecQ p1QToSpecQ)

/-- Consequently the first genuine ruling pushforward satisfies Mathlib's
quasi-compactness requirement. -/
noncomputable instance p1QRulingOne_quasiCompact : QuasiCompact p1QRulingOne := by
  infer_instance

/-- Consequently the second genuine ruling pushforward satisfies Mathlib's
quasi-compactness requirement. -/
noncomputable instance p1QRulingTwo_quasiCompact : QuasiCompact p1QRulingTwo := by
  infer_instance

/-!
MAX-CUT STATUS

PAID HERE, subject to exact-head kernel certification:
* separatedness of the selected `P¹_Q -> Spec Q` map;
* separatedness of both product projections;
* both actual ruling maps are closed immersions;
* therefore both actual ruling maps are quasi-compact.

The only standard geometry instance still required by
`MillenniumHodgeP1QRulingCyclesExact` is now

  `IrreducibleSpace P1QScheme`.

Once that is paid, the literal ruling cycles and their swap anti-invariance
instantiate with no further cycle plumbing.  The next separate project is a
genuine scheme-level cycle-class map and its naturality.
-/

end

end Synthesis.Millennium.Hodge
