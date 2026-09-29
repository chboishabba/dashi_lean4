import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Integration.OggSSPP2F4ActualEllipticGroup
import Integration.OggSSPP2BanerjeeF4ZetaCoordinates

/-!
# P and Q as actual points of Banerjee's F4 elliptic group

These are NOT nine-state labels. They inhabit Mathlib's actual abelian
group of nonsingular affine Weierstrass points, with zero at infinity.

  P = (0,0), Q = (1,zeta).

The proposed map ZMod 3 × ZMod 3 → E(F4) is given literally by elliptic
scalar multiplication and addition. This module intentionally does NOT
declare an AddEquiv or a theorem that this map is additive/bijective:
those require proving three-torsion and independence for actual group
points, not just a count or a tangent identity.
-/

namespace Integration.OggSSPP2F4ActualGroupGenerators

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace Z := Integration.OggSSPP2BanerjeeF4ZetaCoordinates
namespace E := Integration.OggSSPP2F4ActualEllipticGroup

/-- Literal first generator of the genuine Mathlib elliptic group. -/
noncomputable def P : E.ActualCurveGroup :=
  E.fromAffineEquation 0 0 (by norm_num)

/-- Literal second generator; its membership is the F4 trace-one theorem. -/
noncomputable def Q : E.ActualCurveGroup :=
  E.fromAffineEquation 1 Z.zeta (by
    simpa using Z.zeta_trace_one)

/-- The candidate rank-two ternary chart in the ACTUAL elliptic group. -/
noncomputable def candidateChart
    (a b : ZMod 3) : E.ActualCurveGroup :=
  a.val • P + b.val • Q

theorem chart_zero_zero :
    candidateChart 0 0 = 0 := by
  simp [candidateChart]

theorem chart_one_zero :
    candidateChart 1 0 = P := by
  simp [candidateChart]

theorem chart_zero_one :
    candidateChart 0 1 = Q := by
  simp [candidateChart]

/--
Exact outstanding source-independent group-theoretic conditions.

The future theorem must discharge them in the actual elliptic group, not
from a Bool ledger or an arbitrary finite-sector equivalence.
-/
def threeTorsionGoal : Prop :=
  (3 : ℕ) • P = 0 ∧ (3 : ℕ) • Q = 0

def independentBasisGoal : Prop :=
  ∀ a b : ZMod 3, candidateChart a b = 0 → a = 0 ∧ b = 0

def actualChartIsBijectiveGoal : Prop :=
  Function.Bijective (fun ab : ZMod 3 × ZMod 3 =>
    candidateChart ab.1 ab.2)

structure Boundary where
  PAsActualEllipticGroupPointConstructed : Bool
  QAsActualEllipticGroupPointConstructed : Bool
  chartUsesActualEllipticAddition : Bool
  threeTorsionPaid : Bool
  independentBasisPaid : Bool
  bijectiveGroupChartPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  PAsActualEllipticGroupPointConstructed := true
  QAsActualEllipticGroupPointConstructed := true
  chartUsesActualEllipticAddition := true
  threeTorsionPaid := false
  independentBasisPaid := false
  bijectiveGroupChartPaid := false

end Integration.OggSSPP2F4ActualGroupGenerators
