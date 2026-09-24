import Zeta23Bridge.MultiTaperSchurCore
import Mathlib.Tactic

noncomputable section

namespace Zeta23Bridge
namespace ProjectedTwoZeroCutsetCore

open MultiTaperSchurCore

variable {ι : Type*} [Fintype ι]

/-- Orthogonal projection onto one nuisance complement does not increase squared norm. -/
theorem normSqP_transverseComp_le {n x : ι → ℝ} (hn : n ≠ 0) :
    normSqP (transverseComp n x) ≤ normSqP x := by
  rw [normSqP_transverseComp hn]
  unfold schur
  have hnn : 0 < normSqP n := normSqP_pos_of_ne_zero hn
  have hq : 0 ≤ dotP n x ^ 2 / normSqP n := div_nonneg (sq_nonneg _) (le_of_lt hnn)
  linarith

/-- The exact two-nuisance elimination is a contraction in squared Euclidean norm. -/
theorem normSqP_elim2_le {n₁ n₂ x : ι → ℝ}
    (h₁ : n₁ ≠ 0) (h₂ : perp2 n₁ n₂ ≠ 0) :
    normSqP (elim2 n₁ n₂ x) ≤ normSqP x := by
  unfold elim2
  exact le_trans (normSqP_transverseComp_le h₂)
    (normSqP_transverseComp_le h₁)

/-- Zero is fixed by the exact two-nuisance eliminator. -/
theorem elim2_zero (n₁ n₂ : ι → ℝ) : elim2 n₁ n₂ (0 : ι → ℝ) = 0 := by
  unfold elim2 transverseComp perp2
  simp [dotP, normSqP]

/-- The first selected nuisance is killed exactly. -/
theorem elim2_first_nuisance {n₁ n₂ : ι → ℝ} (h₁ : n₁ ≠ 0) :
    elim2 n₁ n₂ n₁ = 0 := by
  unfold elim2
  rw [transverseComp_self h₁]
  unfold transverseComp
  simp [dotP, normSqP]

/-- The second selected nuisance is killed exactly once its component transverse
    to the first is nonzero. -/
theorem elim2_second_nuisance {n₁ n₂ : ι → ℝ} (h₂ : perp2 n₁ n₂ ≠ 0) :
    elim2 n₁ n₂ n₂ = 0 := by
  unfold elim2
  change transverseComp (perp2 n₁ n₂) (perp2 n₁ n₂) = 0
  exact transverseComp_self h₂

/-- Apply the exact quotient to a literal seven-term balance.  The two selected
nuisance vectors disappear identically; every unselected channel remains on the
same certified carrier.  This is the abstract algebraic content of cutset A. -/
theorem projected_balance
    {n₁ n₂ target zeroTail prime gamma pole : ι → ℝ}
    (h₁ : n₁ ≠ 0) (h₂ : perp2 n₁ n₂ ≠ 0)
    (hbal : target + n₁ + n₂ + zeroTail + prime + gamma + pole = 0) :
    elim2 n₁ n₂ target + elim2 n₁ n₂ zeroTail + elim2 n₁ n₂ prime
      + elim2 n₁ n₂ gamma + elim2 n₁ n₂ pole = 0 := by
  have hq := congrArg (elim2 n₁ n₂) hbal
  rw [elim2_zero] at hq
  repeat' rw [elim2_add] at hq
  rw [elim2_first_nuisance h₁, elim2_second_nuisance h₂] at hq
  simpa [add_assoc] using hq

/-- A scalar observer on the one-dimensional quotient.  Only additivity and zero
preservation are needed for the final margin compiler. -/
structure AdditiveObserver (ι : Type*) [Fintype ι] where
  toFun : (ι → ℝ) → ℝ
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_zero : toFun 0 = 0

instance : CoeFun (AdditiveObserver ι) (fun _ => (ι → ℝ) → ℝ) := ⟨AdditiveObserver.toFun⟩

/-- Scalarize the exact post-elimination balance without changing carriers. -/
theorem observed_projected_balance
    (L : AdditiveObserver ι)
    {n₁ n₂ target zeroTail prime gamma pole : ι → ℝ}
    (h₁ : n₁ ≠ 0) (h₂ : perp2 n₁ n₂ ≠ 0)
    (hbal : target + n₁ + n₂ + zeroTail + prime + gamma + pole = 0) :
    L (elim2 n₁ n₂ target) + L (elim2 n₁ n₂ zeroTail)
      + L (elim2 n₁ n₂ prime) + L (elim2 n₁ n₂ gamma)
      + L (elim2 n₁ n₂ pole) = 0 := by
  have h := projected_balance h₁ h₂ hbal
  have hL := congrArg L h
  rw [L.map_zero] at hL
  repeat' rw [L.map_add] at hL
  simpa [add_assoc] using hL

/-- B/C/D packaged exactly: a strictly positive target margin cannot be cancelled
by a signed projected zero tail plus arithmetic channels whose total absolute
budget lies below that margin. -/
structure ProjectedFarTailMarginData (ι : Type*) [Fintype ι] where
  L : AdditiveObserver ι
  target : ι → ℝ
  zeroTail : ι → ℝ
  prime : ι → ℝ
  gamma : ι → ℝ
  pole : ι → ℝ
  targetMargin : ℝ
  zeroBudget : ℝ
  arithBudget : ℝ
  targetMargin_pos : 0 < targetMargin
  targetMargin_le : targetMargin ≤ L.toFun target
  zeroTail_bound : |L.toFun zeroTail| ≤ zeroBudget
  arithmetic_bound : |L.toFun prime + L.toFun gamma + L.toFun pole| ≤ arithBudget
  budget_lt_margin : zeroBudget + arithBudget < targetMargin

/-- The scalar projected balance is impossible under the certified B/C budgets. -/
theorem no_projected_balance (d : ProjectedFarTailMarginData ι) :
    d.L.toFun d.target + d.L.toFun d.zeroTail + d.L.toFun d.prime + d.L.toFun d.gamma + d.L.toFun d.pole ≠ 0 := by
  intro hzero
  have harith : d.L.toFun d.prime + d.L.toFun d.gamma + d.L.toFun d.pole =
      -(d.L.toFun d.target + d.L.toFun d.zeroTail) := by linarith
  have htri : |d.L.toFun d.target| ≤ |d.L.toFun d.zeroTail| +
      |d.L.toFun d.prime + d.L.toFun d.gamma + d.L.toFun d.pole| := by
    calc
      |d.L.toFun d.target| = |-(d.L.toFun d.zeroTail + (d.L.toFun d.prime + d.L.toFun d.gamma + d.L.toFun d.pole))| := by
        congr 1; linarith
      _ = |d.L.toFun d.zeroTail + (d.L.toFun d.prime + d.L.toFun d.gamma + d.L.toFun d.pole)| := abs_neg _
      _ ≤ |d.L.toFun d.zeroTail| + |d.L.toFun d.prime + d.L.toFun d.gamma + d.L.toFun d.pole| := abs_add_le _ _
  have ht_nonneg : 0 ≤ d.L.toFun d.target := le_trans (le_of_lt d.targetMargin_pos) d.targetMargin_le
  have habs : d.targetMargin ≤ |d.L.toFun d.target| := by simpa [abs_of_nonneg ht_nonneg] using d.targetMargin_le
  have hbud : |d.L.toFun d.zeroTail| + |d.L.toFun d.prime + d.L.toFun d.gamma + d.L.toFun d.pole|
      ≤ d.zeroBudget + d.arithBudget := add_le_add d.zeroTail_bound d.arithmetic_bound
  have hlt := d.budget_lt_margin
  linarith

/-- Bidirectional capstone: once every off-line witness yields an impossible
projected balance, the pre-existing characterization of RH closes the lane.  This
keeps the final logical step separate from the analytic B/C producers. -/
theorem rh_of_no_offline
    {Zero : Type*} (OffLine : Zero → Prop) (RH : Prop)
    (rh_iff_no_offline : RH ↔ ∀ ρ, ¬ OffLine ρ)
    (exclude : ∀ ρ, OffLine ρ → False) : RH := by
  rw [rh_iff_no_offline]
  intro ρ hρ
  exact exclude ρ hρ

end ProjectedTwoZeroCutsetCore
end Zeta23Bridge
