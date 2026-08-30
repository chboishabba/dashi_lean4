/-
# The first *inhabited* literal window-Schur admission

Everything upstream of this module was conditional on the domination hypothesis

    |detRest p q₀ q₁ λ a b| < 4 λ² (cross determinant),

supplied by hand.  `LiteralWeilNarrowWindowDomination` discharges it for an explicit
family of unit-mass tent tapers in symmetric windows of a sufficiently small common
half-width.  This module feeds that construction into the literal Schur gate and
records the resulting unconditional statements:

* `exists_normalizedTriple_endpointComparison` — the shared certificate architecture is
  inhabited: an actual `NormalizedNarrowWindowTriple`, an actual `ResponseEnvelope`
  over it, and the single strict endpoint comparison;
* `exists_windowSchurResidualBudgetData` — the generic residual-budget object of the
  compiler is inhabited;
* `exists_windowPair_wedgeSq_pos` and `exists_windowPair_transverseComp_ne_zero` — for
  two zeros of distinct positive heights and positive multiplicity there really is a
  constructed positive test family, and radii at which the literal Gram wedge is
  strictly positive, i.e. at which the nuisance zero is Schur-eliminated exactly while
  the target survives.

The three centres `1 < 2 < 3` and the polarisation `λ = 1` are arbitrary admissible
choices; the domination theorem works for every nonzero `λ` and every ordered triple
of positive centres.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilNarrowWindowDomination
import Zeta23Bridge.WindowSchurSharedCertificate

noncomputable section

open scoped Real
open MeasureTheory Set

namespace Zeta23Bridge
namespace LiteralWeilWindowSchurInstance

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient
open Zeta23Bridge.LiteralWeilLeadingCoefficientCovariance
open Zeta23Bridge.LiteralWeilWindowRatioSeparation
open Zeta23Bridge.LiteralWeilNarrowWindowDomination
open Zeta23Bridge.LiteralWeilTwoTaperCoefficientGate
open Zeta23Bridge.LiteralWeilWindowSchurAdmission
open Zeta23Bridge.LiteralWeilWindowSchurResidualBudget
open Zeta23Bridge.NormalizedNarrowWindowCertificate
open Zeta23Bridge.WindowSchurSharedCertificate
open Zeta23Bridge.MultiTaperSchurCore
open Zeta23Bridge.CoshWindowSeparation

/-- The tautological response envelope of a window triple: each of the ten entries is
the response itself.  Its budget is exactly `detRestBound`. -/
def exactEnvelope (w : NormalizedNarrowWindowTriple) (a b : ℝ) : ResponseEnvelope w a b :=
  ⟨targetLeadingCoeff w.p a, targetLeadingCoeff w.p b,
    targetLeadingCoeff w.q0 a, targetLeadingCoeff w.q0 b,
    targetLeadingCoeff w.q1 a, targetLeadingCoeff w.q1 b,
    covForm w.p w.q0 a, covForm w.p w.q0 b, covForm w.p w.q1 a, covForm w.p w.q1 b,
    le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

theorem envelopeBudget_exactEnvelope (w : NormalizedNarrowWindowTriple) (a b lam : ℝ) :
    envelopeBudget (exactEnvelope w a b) lam = detRestBound w.p w.q0 w.q1 lam a b := by
  unfold envelopeBudget exactEnvelope
    LiteralWeilDetRestBoundMonotonicity.endpointDetRestBound detRestBound
  ring

/-- **The shared window certificate is inhabited.**  For every nonzero polarisation and
every pair of heights `0 < a < b` there is an actual normalized narrow-window triple,
carrying an actual response envelope, whose endpoint budget is strictly below the
strict cross margin, and which satisfies the four-endpoint window gate. -/
theorem exists_normalizedTriple_endpointComparison {lam a b : ℝ} (hlam : lam ≠ 0)
    (ha : 0 < a) (hab : a < b) :
    ∃ w : NormalizedNarrowWindowTriple,
      coshDiff b w.be0 w.be1 * coshDiff a w.al0 w.al2
          < coshDiff b w.al0 w.al2 * coshDiff a w.be0 w.be1 ∧
        envelopeBudget (exactEnvelope w a b) lam < crossMargin w lam a b := by
  obtain ⟨p, q0, q1, al0, be0, al1, be1, al2, be2, hp, hq0, hq1, hpm, hq0m, hq1m,
    hal0, h0, h01, h1, h12, _h2, hgate, hbound⟩ :=
    exists_windowTriple_detRestBound_lt (lam := lam) (a := a) (b := b)
      (c0 := 1) (c1 := 2) (c2 := 3) hlam ha hab one_pos one_lt_two (by norm_num)
  refine ⟨⟨p, q0, q1, al0, be0, al1, be1, al2, be2, ⟨hp, hpm⟩, ⟨hq0, hq0m⟩, ⟨hq1, hq1m⟩,
      hal0, h0, h01, h1, h12⟩, hgate, ?_⟩
  rw [envelopeBudget_exactEnvelope]
  exact hbound

/-- **The generic residual-budget object is inhabited.**  `R ≤ B < M` is realised by an
actual window triple. -/
theorem exists_windowSchurResidualBudgetData {lam a b : ℝ} (hlam : lam ≠ 0)
    (ha : 0 < a) (hab : a < b) :
    ∃ w : NormalizedNarrowWindowTriple,
      Nonempty (WindowSchurResidualBudgetData w.p w.q0 w.q1 lam a b) := by
  obtain ⟨w, _, hstrict⟩ := exists_normalizedTriple_endpointComparison hlam ha hab
  exact ⟨w, ⟨budgetDataOfEndpointComparison (exactEnvelope w a b) lam hstrict⟩⟩
/-- **The domination hypothesis holds for an actual constructed family.** -/
theorem exists_windowTriple_hdom {lam a b : ℝ} (hlam : lam ≠ 0) (ha : 0 < a) (hab : a < b) :
    ∃ w : NormalizedNarrowWindowTriple,
      |detRest w.p w.q0 w.q1 lam a b| < crossMargin w lam a b := by
  obtain ⟨w, _, hstrict⟩ := exists_normalizedTriple_endpointComparison hlam ha hab
  exact ⟨w, hdom_of_endpointComparison (exactEnvelope w a b) lam hstrict⟩

/-! ## The literal Schur admission, unconditionally -/

/-- **A literal nearby nuisance zero can be Schur-eliminated by an actually constructed
positive test family.**  For two zeros of the literal carrier with distinct positive
heights and positive multiplicities there exist explicit tapers `p, q₀, q₁`, an explicit
polarisation, and a radius threshold below which the two literal response vectors span a
nondegenerate plane. -/
theorem exists_windowPair_wedgeSq_pos {σ ρ : Zeros}
    (ha : 0 < heightOf σ) (hab : heightOf σ < heightOf ρ)
    (hmsig : 0 < ((Zeta23.zetaZeroConfig).mult σ : ℝ))
    (hmrho : 0 < ((Zeta23.zetaZeroConfig).mult ρ : ℝ)) :
    ∃ (p q0 q1 : ℝ → ℝ) (lam r0 : ℝ), 0 < r0 ∧ r0 ≤ 1 ∧
      ∀ r : ℝ, 0 < r → r ≤ r0 →
        0 < wedgeSq (zeroRespVec (windowPair p q0 q1 lam) r σ)
              (zeroRespVec (windowPair p q0 q1 lam) r ρ) := by
  obtain ⟨p, q0, q1, al0, be0, al1, be1, al2, be2, hp, hq0, hq1, _hpm, _hq0m, _hq1m,
    hal0, h0, h01, h1, h12, _h2, hgate, hbound⟩ :=
    exists_windowTriple_detRestBound_lt (lam := (1:ℝ)) (a := heightOf σ) (b := heightOf ρ)
      (c0 := 1) (c1 := 2) (c2 := 3) one_ne_zero ha hab one_pos one_lt_two (by norm_num)
  have hdom := detRest_dominated_of_bound hp.cont hp.cpt hq0.cont hq0.cpt hq1.cont hq1.cpt
    hp.nonneg hq0.nonneg hq1.nonneg hbound
  have hL := (leadingCrossDet_windowPair_ne_zero (lam := (1:ℝ)) hp hq0 hq1 hal0 h0 h01 h1 h12
    ha hab hgate hdom hmsig hmrho).2
  obtain ⟨r0, hr0, hr01, hw⟩ := exists_radius_wedgeSq_pos
    (windowPair_continuous hp.cont hq0.cont hq1.cont 1)
    (windowPair_compactSupport hp.cpt hq0.cpt hq1.cpt 1) hL
  exact ⟨p, q0, q1, 1, r0, hr0, hr01, hw⟩

/-- The same admission in transverse form: the target response survives the exact
projection that annihilates the nuisance response. -/
theorem exists_windowPair_transverseComp_ne_zero {σ ρ : Zeros}
    (ha : 0 < heightOf σ) (hab : heightOf σ < heightOf ρ)
    (hmsig : 0 < ((Zeta23.zetaZeroConfig).mult σ : ℝ))
    (hmrho : 0 < ((Zeta23.zetaZeroConfig).mult ρ : ℝ)) :
    ∃ (p q0 q1 : ℝ → ℝ) (lam r0 : ℝ), 0 < r0 ∧ r0 ≤ 1 ∧
      ∀ r : ℝ, 0 < r → r ≤ r0 →
        transverseComp (zeroRespVec (windowPair p q0 q1 lam) r σ)
          (zeroRespVec (windowPair p q0 q1 lam) r ρ) ≠ 0 := by
  obtain ⟨p, q0, q1, lam, r0, hr0, hr01, hw⟩ :=
    exists_windowPair_wedgeSq_pos ha hab hmsig hmrho
  exact ⟨p, q0, q1, lam, r0, hr0, hr01, fun r hrpos hrle =>
    transverseComp_ne_zero_of_wedgeSq_pos (hw r hrpos hrle)⟩

end LiteralWeilWindowSchurInstance
end Zeta23Bridge
