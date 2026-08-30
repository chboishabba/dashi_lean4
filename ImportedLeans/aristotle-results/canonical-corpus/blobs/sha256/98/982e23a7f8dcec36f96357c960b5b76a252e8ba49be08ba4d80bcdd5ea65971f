/-
# Thin consumers of one shared normalized-window certificate

The response envelope, the strict cross margin, the residual-budget object and the
final `hdom` all refer to the same `NormalizedNarrowWindowTriple`.  This prevents
later stages from silently recombining bounds proved for different tapers or
different windows.

Nothing here asserts existence; the producers are
`LiteralWeilNarrowWindowDomination` (which constructs an actual triple, an actual
envelope and the strict endpoint comparison) and `LiteralWeilWindowSchurInstance`
(which feeds the result into the literal Schur admission gate).
-/
import Zeta23Bridge.NormalizedNarrowWindowCertificate
import Zeta23Bridge.LiteralWeilDetRestBoundMonotonicity
import Zeta23Bridge.LiteralWeilWindowSchurResidualBudget
import Zeta23Bridge.LiteralWeilWindowSchurAdmission

noncomputable section

namespace Zeta23Bridge
namespace WindowSchurSharedCertificate

open Zeta23Bridge.LiteralWeilLeadingCoefficientCovariance
open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient
open Zeta23Bridge.LiteralWeilWindowRatioSeparation
open Zeta23Bridge.LiteralWeilDetRestBoundMonotonicity
open Zeta23Bridge.LiteralWeilWindowSchurResidualBudget
open Zeta23Bridge.NormalizedNarrowWindowCertificate
open Zeta23Bridge.LiteralWeilWindowSchurAdmission
open Zeta23Bridge.CoshWindowSeparation
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.MultiTaperSchurCore
open Zeta23Bridge.LiteralWeilTwoTaperCoefficientGate

/-- Ten endpoint/envelope quantities, all indexed by the exact window triple they
bound. -/
structure ResponseEnvelope (w : NormalizedNarrowWindowTriple) (a b : ℝ) where
  Pa : ℝ
  Pb : ℝ
  Q0a : ℝ
  Q0b : ℝ
  Q1a : ℝ
  Q1b : ℝ
  C0a : ℝ
  C0b : ℝ
  C1a : ℝ
  C1b : ℝ
  pA : targetLeadingCoeff w.p a ≤ Pa
  pB : targetLeadingCoeff w.p b ≤ Pb
  q0A : targetLeadingCoeff w.q0 a ≤ Q0a
  q0B : targetLeadingCoeff w.q0 b ≤ Q0b
  q1A : targetLeadingCoeff w.q1 a ≤ Q1a
  q1B : targetLeadingCoeff w.q1 b ≤ Q1b
  c0A : covForm w.p w.q0 a ≤ C0a
  c0B : covForm w.p w.q0 b ≤ C0b
  c1A : covForm w.p w.q1 a ≤ C1a
  c1B : covForm w.p w.q1 b ≤ C1b

/-- The literal strict cross signal owned by the same window triple. -/
def crossMargin (w : NormalizedNarrowWindowTriple) (lam a b : ℝ) : ℝ :=
  4 * lam ^ 2 *
    (covForm w.p w.q0 a * covForm w.p w.q1 b -
      covForm w.p w.q1 a * covForm w.p w.q0 b)

/-- The envelope value of the quartic remainder. -/
def envelopeBudget {w : NormalizedNarrowWindowTriple} {a b : ℝ}
    (e : ResponseEnvelope w a b) (lam : ℝ) : ℝ :=
  endpointDetRestBound lam e.Pa e.Pb e.Q0a e.Q0b e.Q1a e.Q1b e.C0a e.C0b e.C1a e.C1b

/-- Transport the ten certified response inequalities through the literal quartic
remainder polynomial. -/
theorem detRestBound_le_envelope {w : NormalizedNarrowWindowTriple} {a b : ℝ}
    (e : ResponseEnvelope w a b) (lam : ℝ) :
    detRestBound w.p w.q0 w.q1 lam a b ≤ envelopeBudget e lam :=
  detRestBound_mono
    w.pNorm.continuous w.pNorm.compactSupport
    w.q0Norm.continuous w.q0Norm.compactSupport
    w.q1Norm.continuous w.q1Norm.compactSupport
    w.pNorm.nonneg w.q0Norm.nonneg w.q1Norm.nonneg
    e.pA e.pB e.q0A e.q0B e.q1A e.q1B e.c0A e.c0B e.c1A e.c1B

/-- Once the single symbolic endpoint comparison closes, the residual-budget object
of the generic compiler is inhabited. -/
def budgetDataOfEndpointComparison {w : NormalizedNarrowWindowTriple} {a b : ℝ}
    (e : ResponseEnvelope w a b) (lam : ℝ)
    (hstrict : envelopeBudget e lam < crossMargin w lam a b) :
    WindowSchurResidualBudgetData w.p w.q0 w.q1 lam a b :=
  { budget := envelopeBudget e lam
    detRestBound_le_budget := detRestBound_le_envelope e lam
    budget_lt_crossMargin := hstrict }

/-- Final thin consumer: no individual continuity, support or sign fact remains
exposed — one window object and one inequality generate `hdom`. -/
theorem hdom_of_endpointComparison {w : NormalizedNarrowWindowTriple} {a b : ℝ}
    (e : ResponseEnvelope w a b) (lam : ℝ)
    (hstrict : envelopeBudget e lam < crossMargin w lam a b) :
    |detRest w.p w.q0 w.q1 lam a b| < crossMargin w lam a b :=
  hdom_of_budget
    w.pNorm.continuous w.pNorm.compactSupport
    w.q0Norm.continuous w.q0Norm.compactSupport
    w.q1Norm.continuous w.q1Norm.compactSupport
    w.pNorm.nonneg w.q0Norm.nonneg w.q1Norm.nonneg
    (budgetDataOfEndpointComparison e lam hstrict)

/-- **End-to-end one-zero admission from the shared certificate plus one endpoint
inequality.** -/
theorem exists_radius_transverseComp_ne_zero_of_endpointComparison
    {σ ρ : Zeros} {w : NormalizedNarrowWindowTriple}
    (e : ResponseEnvelope w (heightOf σ) (heightOf ρ)) (lam : ℝ)
    (ha : 0 < heightOf σ) (hab : heightOf σ < heightOf ρ)
    (hgate :
      coshDiff (heightOf ρ) w.be0 w.be1 * coshDiff (heightOf σ) w.al0 w.al2
        < coshDiff (heightOf ρ) w.al0 w.al2 * coshDiff (heightOf σ) w.be0 w.be1)
    (hstrict : envelopeBudget e lam < crossMargin w lam (heightOf σ) (heightOf ρ))
    (hmsig : 0 < ((Zeta23.zetaZeroConfig).mult σ : ℝ))
    (hmrho : 0 < ((Zeta23.zetaZeroConfig).mult ρ : ℝ)) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 →
      transverseComp (zeroRespVec (windowPair w.p w.q0 w.q1 lam) r σ)
        (zeroRespVec (windowPair w.p w.q0 w.q1 lam) r ρ) ≠ 0 :=
  exists_radius_windowPair_transverseComp_ne_zero
    w.pWindow w.q0Window w.q1Window
    w.lowPositive w.lowOrdered w.lowMiddleSeparated w.middleOrdered w.middleTopSeparated
    ha hab hgate (hdom_of_endpointComparison e lam hstrict) hmsig hmrho

end WindowSchurSharedCertificate
end Zeta23Bridge
