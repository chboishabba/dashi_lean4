/-
# Which budgets can complete the pole-quotient lane, and which cannot

`PoleQuotientComplementMargin.lean` isolated the *consumer* of the pole-quotient
lane as ordered algebra: with the literal three-channel balance

    D_cluster + D_off + D_Γ = 0,

budgets `|D_off| ≤ B_off`, `|D_Γ| ≤ B_Γ`, a margin `M ≤ D_cluster` and the strict
comparison `B_off + B_Γ < M` are contradictory (`false_of_split_budget`).

This module records the exact contrapositive form of that compiler together with
the constraint it places on how the budgets may be *obtained*.  The key inequality
is

    B_off + B_Γ ≥ |D_off| + |D_Γ| ≥ |D_off + D_Γ| = D_cluster    (`cluster_le_budget_sum`),

valid for every pair of correct budgets.  Read as a statement about proofs, this
says:

* **a budget derived through the balance itself is useless.**  Any estimate of the
  complement channels that routes through `D_off + D_Γ = −D_cluster`, or through
  any quantity already bounded below by `D_cluster`, automatically produces
  `B_off + B_Γ ≥ D_cluster` and can never yield the strict comparison.  The
  budgets have to come from an *independent* analysis of the off-ordinate zero sum
  and of the gamma bracket;
* **the strict comparison is exactly as strong as the contradiction.**
  `not_strict_margin_of_budgets` derives `¬ (B_off + B_Γ < M)` from the remaining
  premises, so the strict comparison and the contradiction it feeds are two
  readings of one fact: inside the context of a hypothetical off-line zero, a
  proof of the strict comparison *is* a proof of the Riemann Hypothesis.  Nothing
  here says such a proof exists, and nothing here says it cannot exist;
* **one-sided budgets are no weaker and no stronger.**  The compiler only uses the
  two lower bounds `−B_off ≤ D_off`, `−B_Γ ≤ D_Γ`
  (`not_strict_margin_of_signed_budgets`), so replacing the absolute values by
  signed bounds changes nothing;
* **the sharpest conceivable budgets are the exact channel values.**
  `not_strict_margin_with_exact_gamma` and `not_strict_margin_with_exact_offOrdinate`
  put `|ℓ(Q_Γ)|` and `|ℓ(Q_offOrd)|` themselves in place of the budgets.  So the
  target of §29.4 is not "make `B_Γ` smaller than `|ℓ(Q_Γ)|`" — that is
  impossible — but "evaluate both channels to within the cluster margin of
  `PoleQuotientClusterMargin.lean`".

Finally `budget_sum_ge_baseline_add_margin` records the resulting pin: every
correct budget sum is at least the height-free baseline *plus* the explicit
second-moment margin of any zero of the target ordinate.

No `sorry`, no `axiom`, no numerical evidence, and nothing here assumes or weakens
the Riemann Hypothesis.
-/
import Zeta23Bridge.PoleQuotientClusterMargin

noncomputable section

open MeasureTheory
open scoped Real

namespace Zeta23Bridge
namespace PoleQuotientBudgetCircularity

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilEvenChannelTaper
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateTail
open Zeta23Bridge.LiteralWeilGammaConeBound
open Zeta23Bridge.LiteralWeilPrimeEvenCone
open Zeta23Bridge.PoleQuotientComplementMargin
open Zeta23Bridge.PoleQuotientClusterMargin

/-! ## 1. The abstract form -/

/-- **The budget sum always dominates the first channel.**  Pure consequence of the
balance and of the correctness of the two budgets.  Hence any estimate obtained
*through* the balance is worthless for the strict comparison. -/
theorem cluster_le_budget_sum {Dcluster Doff Dgamma Boff Bgamma : ℝ}
    (hbal : Dcluster + Doff + Dgamma = 0)
    (hoff : |Doff| ≤ Boff) (hgamma : |Dgamma| ≤ Bgamma) :
    Dcluster ≤ Boff + Bgamma := by
  have h1 := (abs_le.mp hoff).1
  have h2 := (abs_le.mp hgamma).1
  linarith

/-- **The contrapositive of the split-budget compiler.**  Inside any context in
which the balance, correct budgets and a margin below the first channel are all
available, the strict comparison is false — which is exactly why proving it (in
the context of a hypothetical off-line zero) would close the contradiction. -/
theorem not_strict_margin_of_budgets {Dcluster Doff Dgamma Boff Bgamma M : ℝ}
    (hbal : Dcluster + Doff + Dgamma = 0) (hM : M ≤ Dcluster)
    (hoff : |Doff| ≤ Boff) (hgamma : |Dgamma| ≤ Bgamma) :
    ¬ (Boff + Bgamma < M) := by
  intro hlt
  have := cluster_le_budget_sum hbal hoff hgamma
  linarith

/-- **Signed budgets change nothing.**  The compiler only uses the two lower
bounds, and those alone already force the budget sum above the first channel. -/
theorem not_strict_margin_of_signed_budgets {Dcluster Doff Dgamma Boff Bgamma M : ℝ}
    (hbal : Dcluster + Doff + Dgamma = 0) (hM : M ≤ Dcluster)
    (hoff : -Boff ≤ Doff) (hgamma : -Bgamma ≤ Dgamma) :
    ¬ (Boff + Bgamma < M) := by
  intro hlt
  linarith

/-! ## 2. The literal even-cone form -/

/-- The same statement on the literal channels of the pole-quotient lane: pole
channel killed by the parity quotient, prime channel the zero vector. -/
theorem not_strict_margin_of_evenCone_budgets {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) {t r : ℝ}
    (hpole : poleEvenResp g t r = 0) (hprime : primeVec (sampleFam g t r) = 0)
    {Boff Bgamma M : ℝ}
    (hoff : |evenConeFunctional (offOrdVec (sampleFam g t r) t)| ≤ Boff)
    (hgamma : |evenConeFunctional (gammaVec (sampleFam g t r))| ≤ Bgamma)
    (hM : M ≤ evenConeFunctional (clusterVec (sampleFam g t r) t)) :
    ¬ (Boff + Bgamma < M) := by
  intro hlt
  have hbud := clusterValue_le_budget hgs hgc heven hpole hprime hoff hgamma
  linarith

/-- **The cluster margin pins every correct budget sum from below.**  The explicit
second-moment margin of `PoleQuotientClusterMargin` is a lower bound for
`B_off + B_Γ`, so the two channels have to be evaluated to that absolute accuracy
— they cannot merely be bounded. -/
theorem budget_sum_ge_baseline_add_margin {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (hnn : ∀ u, 0 ≤ g u)
    {t r : ℝ} (hr : 0 < r) (hwin : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
    (hpole : poleEvenResp g t r = 0) (hprime : primeVec (sampleFam g t r) = 0)
    {Boff Bgamma : ℝ}
    (hoff : |evenConeFunctional (offOrdVec (sampleFam g t r) t)| ≤ Boff)
    (hgamma : |evenConeFunctional (gammaVec (sampleFam g t r))| ≤ Bgamma)
    (ρstar : SameOrd t) :
    baselineCluster g t r + clusterMargin g (ρstar : Zeros) ≤ Boff + Bgamma :=
  budget_exceeds_baseline_plus_margin hgs hgc heven hnn hr hwin hpole hprime hoff hgamma ρstar

/-- **The sharpest conceivable gamma budget is the exact gamma value**, and the
comparison is still an equality-driven statement there: no budget can be smaller
than `|ℓ(Q_Γ)|`, so §29.4 is a demand for *evaluation*, not for a smaller bound. -/
theorem not_strict_margin_with_exact_gamma {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) {t r : ℝ}
    (hpole : poleEvenResp g t r = 0) (hprime : primeVec (sampleFam g t r) = 0)
    {Boff M : ℝ}
    (hoff : |evenConeFunctional (offOrdVec (sampleFam g t r) t)| ≤ Boff)
    (hM : M ≤ evenConeFunctional (clusterVec (sampleFam g t r) t)) :
    ¬ (Boff + |evenConeFunctional (gammaVec (sampleFam g t r))| < M) :=
  not_strict_margin_of_evenCone_budgets hgs hgc heven hpole hprime hoff le_rfl hM

/-- The same with the exact off-ordinate value in place of a budget. -/
theorem not_strict_margin_with_exact_offOrdinate {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) {t r : ℝ}
    (hpole : poleEvenResp g t r = 0) (hprime : primeVec (sampleFam g t r) = 0)
    {Bgamma M : ℝ}
    (hgamma : |evenConeFunctional (gammaVec (sampleFam g t r))| ≤ Bgamma)
    (hM : M ≤ evenConeFunctional (clusterVec (sampleFam g t r) t)) :
    ¬ (|evenConeFunctional (offOrdVec (sampleFam g t r) t)| + Bgamma < M) :=
  not_strict_margin_of_evenCone_budgets hgs hgc heven hpole hprime le_rfl hgamma hM

end PoleQuotientBudgetCircularity
end Zeta23Bridge
