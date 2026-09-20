import Synthesis.RiemannHighDeterministicSchurNoGo
import Zeta23Bridge.LiteralWeilTwoTaperCoefficientGate
import Zeta23Bridge.ProjectedTwoZeroCutsetCore

/-!
# Corrected high-side one-zero Schur cutset

The deterministic pole/Gamma quotient is exact and therefore cannot furnish a
strict cluster-vs-off comparison.  The useful Schur projection is instead the
one already justified by the localized-window machinery: remove a selected
same-ordinate zero-response nuisance direction while preserving the target
zero-response direction.

For a two-taper family g and radius r, write

  T = response(target),
  N = response(nuisance),
  C_rest = cluster - T - N.

The literal short-support projective balance gives

  T + N + C_rest - Off - Gamma - Pole = 0.

Projecting orthogonally to N kills the selected nuisance exactly:

  P_Nperp T
    + P_Nperp C_rest
    - P_Nperp Off
    - P_Nperp Gamma
    - P_Nperp Pole = 0.

If the target survives this projection, use the canonical scalar observer
x |-> <P_Nperp T, x>.  The target contribution is then exactly
||P_Nperp T||^2 > 0.  A signed bound on the remaining projected channels below
that energy yields contradiction.

This file closes that algebraic compiler.  It does not manufacture the missing
C^2 short window lift or the signed projected residual estimate.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.MultiTaperSchurCore
open Zeta23Bridge.ProjectedTwoZeroCutsetCore
open Zeta23Bridge.LiteralWeilTwoTaperCoefficientGate
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile

def clusterVec2 (g : Fin 2 → ℝ → ℝ) (t r : ℝ) : Fin 2 → ℝ :=
  fun j => clusterHeightDefect (g j) t r

def offOrdVec2 (g : Fin 2 → ℝ → ℝ) (t r : ℝ) : Fin 2 → ℝ :=
  fun j => offOrdProjectiveDefect (g j) t r

def gammaVec2 (g : Fin 2 → ℝ → ℝ) (t r : ℝ) : Fin 2 → ℝ :=
  fun j => gammaProjectiveDefect (g j) t r

def poleVec2 (g : Fin 2 → ℝ → ℝ) (t r : ℝ) : Fin 2 → ℝ :=
  fun j => poleProjectiveDefect (g j) t r

def sameOrdRestVec2
    (g : Fin 2 → ℝ → ℝ) (t r : ℝ) (target nuisance : Zeros) :
    Fin 2 → ℝ :=
  clusterVec2 g t r
    - zeroRespVec g r target
    - zeroRespVec g r nuisance

theorem oneZeroCutset_balance
    {g : Fin 2 → ℝ → ℝ} {t r : ℝ} {target nuisance : Zeros}
    (hgs : ∀ j, ContDiff ℝ 2 (g j))
    (hgc : ∀ j, HasCompactSupport (g j))
    (heven : ∀ j u, g j (-u) = g j u)
    (hshort : ∀ j u, g j u ≠ 0 → |u| < Real.log 2) :
    zeroRespVec g r target
      + zeroRespVec g r nuisance
      + sameOrdRestVec2 g t r target nuisance
      + (- offOrdVec2 g t r)
      + (- gammaVec2 g t r)
      + (- poleVec2 g t r)
      = 0 := by
  funext j
  have hj :=
    clusterHeightDefect_eq_threeProjectiveChannels
      (hgs j) (hgc j) (heven j) (hshort j) t r
  simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
  unfold sameOrdRestVec2 clusterVec2 offOrdVec2 gammaVec2 poleVec2
  dsimp
  linarith

theorem oneZeroCutset_projected_balance
    {g : Fin 2 → ℝ → ℝ} {t r : ℝ} {target nuisance : Zeros}
    (hgs : ∀ j, ContDiff ℝ 2 (g j))
    (hgc : ∀ j, HasCompactSupport (g j))
    (heven : ∀ j u, g j (-u) = g j u)
    (hshort : ∀ j u, g j u ≠ 0 → |u| < Real.log 2)
    (hnuisance : zeroRespVec g r nuisance ≠ 0) :
    transverseComp (zeroRespVec g r nuisance) (zeroRespVec g r target)
      + transverseComp (zeroRespVec g r nuisance)
          (sameOrdRestVec2 g t r target nuisance)
      + transverseComp (zeroRespVec g r nuisance) (- offOrdVec2 g t r)
      + transverseComp (zeroRespVec g r nuisance) (- gammaVec2 g t r)
      + transverseComp (zeroRespVec g r nuisance) (- poleVec2 g t r)
      = 0 := by
  have hbal :=
    oneZeroCutset_balance
      (g := g) (t := t) (r := r)
      (target := target) (nuisance := nuisance)
      hgs hgc heven hshort
  have hq :=
    congrArg (transverseComp (zeroRespVec g r nuisance)) hbal
  repeat' rw [transverseComp_add] at hq
  rw [transverseComp_self hnuisance] at hq
  simp only [add_zero, zero_add] at hq
  simpa [transverseComp, dotP, normSqP] using hq

def targetProjected
    (g : Fin 2 → ℝ → ℝ) (r : ℝ) (target nuisance : Zeros) :
    Fin 2 → ℝ :=
  transverseComp (zeroRespVec g r nuisance) (zeroRespVec g r target)

def dotObserver2 (v : Fin 2 → ℝ) : AdditiveObserver (Fin 2) where
  toFun := dotP v
  map_add := dotP_add_right v
  map_zero := by
    unfold dotP
    simp

theorem dotObserver2_self (v : Fin 2 → ℝ) :
    dotObserver2 v v = normSqP v := by
  rfl

structure HighOneZeroSchurResidualPayment
    {g : Fin 2 → ℝ → ℝ} {t r : ℝ}
    (target nuisance : Zeros) where
  targetSurvives :
    targetProjected g r target nuisance ≠ 0

  sameOrdBudget : ℝ
  externalBudget : ℝ

  sameOrd_bound :
    |dotP (targetProjected g r target nuisance)
      (transverseComp (zeroRespVec g r nuisance)
        (sameOrdRestVec2 g t r target nuisance))|
      ≤ sameOrdBudget

  external_bound :
    |dotP (targetProjected g r target nuisance)
        (transverseComp (zeroRespVec g r nuisance) (- offOrdVec2 g t r))
      +
      dotP (targetProjected g r target nuisance)
        (transverseComp (zeroRespVec g r nuisance) (- gammaVec2 g t r))
      +
      dotP (targetProjected g r target nuisance)
        (transverseComp (zeroRespVec g r nuisance) (- poleVec2 g t r))|
      ≤ externalBudget

  budget_lt_target :
    sameOrdBudget + externalBudget
      < normSqP (targetProjected g r target nuisance)

theorem false_of_oneZeroSchurResidualPayment
    {g : Fin 2 → ℝ → ℝ} {t r : ℝ} {target nuisance : Zeros}
    (hgs : ∀ j, ContDiff ℝ 2 (g j))
    (hgc : ∀ j, HasCompactSupport (g j))
    (heven : ∀ j u, g j (-u) = g j u)
    (hshort : ∀ j u, g j u ≠ 0 → |u| < Real.log 2)
    (hnuisance : zeroRespVec g r nuisance ≠ 0)
    (P : HighOneZeroSchurResidualPayment
      (g := g) (t := t) (r := r) target nuisance) :
    False := by
  let T := targetProjected g r target nuisance
  let R := transverseComp (zeroRespVec g r nuisance)
    (sameOrdRestVec2 g t r target nuisance)
  let O := transverseComp (zeroRespVec g r nuisance) (- offOrdVec2 g t r)
  let G := transverseComp (zeroRespVec g r nuisance) (- gammaVec2 g t r)
  let Q := transverseComp (zeroRespVec g r nuisance) (- poleVec2 g t r)
  let L := dotObserver2 T

  have hTpos : 0 < normSqP T :=
    normSqP_pos_of_ne_zero P.targetSurvives

  let D : ProjectedFarTailMarginData (Fin 2) :=
    { L := L
      target := T
      zeroTail := R
      prime := O
      gamma := G
      pole := Q
      targetMargin := normSqP T
      zeroBudget := P.sameOrdBudget
      arithBudget := P.externalBudget
      targetMargin_pos := hTpos
      targetMargin_le := by
        change normSqP T ≤ dotP T T
        rfl
      zeroTail_bound := by
        change |dotP T R| ≤ P.sameOrdBudget
        exact P.sameOrd_bound
      arithmetic_bound := by
        change |dotP T O + dotP T G + dotP T Q| ≤ P.externalBudget
        exact P.external_bound
      budget_lt_margin := by
        exact P.budget_lt_target }

  have hnot := no_projected_balance D
  have hvec :=
    oneZeroCutset_projected_balance
      (g := g) (t := t) (r := r)
      (target := target) (nuisance := nuisance)
      hgs hgc heven hshort hnuisance
  have hscalar := congrArg (dotP T) hvec
  repeat' rw [dotP_add_right] at hscalar
  have hz : dotP T (0 : Fin 2 → ℝ) = 0 := by
    unfold dotP
    simp
  rw [hz] at hscalar
  exact hnot hscalar

end Synthesis
