import Mathlib
import Integration.OggSSPP2F4ActualGroupGenerators
import Integration.OggSSPP2F4ActualGroupRelations
import Integration.OggSSPP2F4ActualGroupCardinality

/-!
# Actual C3² basis for the Banerjee F4 elliptic group

This file upgrades the candidate chart

  (a,b) ↦ a • P + b • Q

from a set-level expression to an additive group equivalence.  The proof uses
ONLY the actual Mathlib elliptic group relations already established:

  3P=0, 3Q=0,

plus the x-coordinate separation of P and Q and the actual group cardinality 9.

The finite case splits are over ZMod 3 coefficients, not over a surrogate
nine-state carrier.
-/

namespace Integration.OggSSPP2F4ActualGroupBasis

namespace B := Integration.OggSSPP2BanerjeeF4UniversalDeformationSource
namespace E := Integration.OggSSPP2F4ActualEllipticGroup
namespace G := Integration.OggSSPP2F4ActualGroupGenerators
namespace R := Integration.OggSSPP2F4ActualGroupRelations
namespace C := Integration.OggSSPP2F4ActualGroupCardinality

open WeierstrassCurve

theorem P_ne_zero : G.P ≠ 0 := by
  unfold G.P E.fromAffineEquation
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

theorem Q_ne_zero : G.Q ≠ 0 := by
  unfold G.Q E.fromAffineEquation
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-- P and Q cannot agree because their x-coordinates are 0 and 1. -/
theorem P_ne_Q : G.P ≠ G.Q := by
  intro h
  have hx := congrArg WeierstrassCurve.Affine.Point.xRep h
  simp [G.P, G.Q, E.fromAffineEquation] at hx

/-- P also cannot equal -Q, since negation preserves the x-coordinate. -/
theorem P_ne_neg_Q : G.P ≠ -G.Q := by
  intro h
  have hx := congrArg WeierstrassCurve.Affine.Point.xRep h
  simp [G.P, G.Q, E.fromAffineEquation] at hx

theorem two_nsmul_P :
    (2 : ℕ) • G.P = -G.P := by
  simpa [two_nsmul] using R.P_add_P_eq_neg_P

theorem two_nsmul_Q :
    (2 : ℕ) • G.Q = -G.Q := by
  simpa [two_nsmul] using R.Q_add_Q_eq_neg_Q

/--
The candidate chart is additive.  This is finite coefficient normalization
modulo 3; the only nontrivial reductions are 3P=0 and 3Q=0.
-/
theorem candidateChart_add
    (a b c d : ZMod 3) :
    G.candidateChart (a + c) (b + d) =
      G.candidateChart a b + G.candidateChart c d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [G.candidateChart, two_nsmul, R.P_add_P_eq_neg_P,
      R.Q_add_Q_eq_neg_Q, R.three_nsmul_P, R.three_nsmul_Q] <;> abel

def chartHom : (ZMod 3 × ZMod 3) →+ E.ActualCurveGroup where
  toFun ab := G.candidateChart ab.1 ab.2
  map_zero' := G.chart_zero_zero
  map_add' ab cd := by
    simpa using candidateChart_add ab.1 ab.2 cd.1 cd.2

/--
The only coefficient pair mapping to elliptic infinity is (0,0).
-/
theorem candidateChart_eq_zero_iff
    (a b : ZMod 3) :
    G.candidateChart a b = 0 ↔ a = 0 ∧ b = 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [G.candidateChart, two_nsmul, R.P_add_P_eq_neg_P,
      R.Q_add_Q_eq_neg_Q, P_ne_zero, Q_ne_zero, P_ne_Q, P_ne_neg_Q] <;>
    abel

theorem chartHom_ker_eq_bot :
    chartHom.ker = ⊥ := by
  ext ab
  simp [chartHom, candidateChart_eq_zero_iff, Prod.ext_iff]

theorem chartHom_injective :
    Function.Injective chartHom := by
  exact AddMonoidHom.ker_eq_bot.mp chartHom_ker_eq_bot

theorem domain_cardinality :
    Fintype.card (ZMod 3 × ZMod 3) = 9 := by
  native_decide

theorem chartHom_bijective :
    Function.Bijective chartHom := by
  apply (Fintype.bijective_iff_injective_and_card chartHom).2
  exact ⟨chartHom_injective, by
    rw [domain_cardinality, C.actual_curve_group_cardinality]⟩

/--
The desired genuine additive equivalence:
E(F4) is the rank-two ternary group, with the actual elliptic group law.
-/
noncomputable def actualC3SquareAddEquiv :
    (ZMod 3 × ZMod 3) ≃+ E.ActualCurveGroup :=
  AddEquiv.ofBijective chartHom chartHom_bijective

@[simp] theorem actualC3SquareAddEquiv_apply
    (a b : ZMod 3) :
    actualC3SquareAddEquiv (a,b) = G.candidateChart a b := rfl

@[simp] theorem actualC3SquareAddEquiv_zero :
    actualC3SquareAddEquiv (0,0) = 0 := by
  simp

@[simp] theorem actualC3SquareAddEquiv_first :
    actualC3SquareAddEquiv (1,0) = G.P := by
  simp [actualC3SquareAddEquiv_apply, G.chart_one_zero]

@[simp] theorem actualC3SquareAddEquiv_second :
    actualC3SquareAddEquiv (0,1) = G.Q := by
  simp [actualC3SquareAddEquiv_apply, G.chart_zero_one]

structure Boundary where
  actualEllipticGroupUsed : Bool
  actualPQTorsionUsed : Bool
  chartAdditivityProved : Bool
  chartKernelTrivialProved : Bool
  actualGroupCardinalityNineUsed : Bool
  genuineC3SquareAddEquivConstructed : Bool
  frobeniusMatrixIntertwinerProved : Bool
  shearMatrixIntertwinerProved : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  actualEllipticGroupUsed := true
  actualPQTorsionUsed := true
  chartAdditivityProved := true
  chartKernelTrivialProved := true
  actualGroupCardinalityNineUsed := true
  genuineC3SquareAddEquivConstructed := true
  frobeniusMatrixIntertwinerProved := false
  shearMatrixIntertwinerProved := false

end Integration.OggSSPP2F4ActualGroupBasis
