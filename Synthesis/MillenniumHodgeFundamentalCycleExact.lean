import Synthesis.MillenniumHodgeRealAlgebraicCycleMultiplicityExact
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Tactic

/-!
# Hodge max-cut: genuine fundamental cycle of an irreducible scheme

Mathlib defines an `AlgebraicCycle X R` as a locally finite coefficient
function on scheme points, using the equivalence between irreducible closed
subsets and their generic points.  Consequently the fundamental cycle of an
irreducible scheme is represented on the literal Mathlib carrier by the
singleton cycle at `genericPoint X` with coefficient one.

No Chow group or synthetic cycle carrier is introduced here.
-/

namespace Synthesis.Millennium.Hodge

open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicCycle

noncomputable section

universe u

section Fundamental

variable (X : Scheme.{u}) [IrreducibleSpace X] [DecidableEq X]

/-- Genuine fundamental algebraic cycle of an irreducible scheme. -/
noncomputable def fundamentalCycle : AlgebraicCycle X ℤ :=
  pointCycle (genericPoint X)

@[simp] theorem fundamentalCycle_genericPoint :
    fundamentalCycle X (genericPoint X) = 1 := by
  simp [fundamentalCycle, pointCycle]

@[simp] theorem fundamentalCycle_off_genericPoint
    (x : X) (hx : x ≠ genericPoint X) :
    fundamentalCycle X x = 0 := by
  simp [fundamentalCycle, pointCycle, hx]

/-- The fundamental cycle is nonzero on every nonempty irreducible scheme,
visibly at its generic point. -/
theorem fundamentalCycle_ne_zero : fundamentalCycle X ≠ 0 := by
  intro h
  have hcoeff := congrArg
    (fun D : AlgebraicCycle X ℤ => D (genericPoint X)) h
  simpa using hcoeff

end Fundamental

/-!
MAX-CUT STATUS

PAID HERE, subject to exact-head kernel certification:
* a genuine fundamental cycle on Mathlib's actual `AlgebraicCycle` carrier;
* coefficient one at the scheme generic point and zero off it;
* nontriviality.

SELECTED P¹×P¹ NEXT WELD:
* provide/infer `IrreducibleSpace P1QScheme` for the literal Proj already built;
* prove the two actual ruling embeddings are quasicompact;
* define D₁,D₂ as `actualCyclePushforward p1QRulingOne/Two
  (fundamentalCycle P1QScheme)`;
* prove residue-degree weighted pushforward compatibility with postcomposition
  by the actual factor-swap isomorphism.

After those real geometric/API obligations, the existing
`p1Q_ruling_difference_antiInvariant_of_exchange` closes the cycle regression.
-/

end

end Synthesis.Millennium.Hodge
