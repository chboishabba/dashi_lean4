import Zeta23Bridge.LiteralWeilParityBalance
import Zeta23Bridge.ProjectedTwoZeroCutsetCore

noncomputable section

namespace Zeta23Bridge
namespace LiteralWeilThreeSampleProjectedCarrier

open LiteralWeilParityBalance
open MultiTaperSchurCore
open ProjectedTwoZeroCutsetCore

/-- Literal target vector on an arbitrary three-test-function carrier. -/
def targetVec3 (kFam : Fin 3 → ℝ → ℂ) (ρstar : Zeros) : Fin 3 → ℝ :=
  fun i => reim (zeroTerm (kFam i) ρstar)

/-- Literal sum of all non-target zeros on the same three-test-function carrier. -/
def otherVec3 (kFam : Fin 3 → ℝ → ℂ) (ρstar : Zeros) : Fin 3 → ℝ :=
  fun i => reim (otherZerosTerm (kFam i) ρstar)

/-- Literal prime vector on the same carrier. -/
def primeVec3 (kFam : Fin 3 → ℝ → ℂ) : Fin 3 → ℝ :=
  fun i => reim (primeTerm (kFam i))

/-- Literal gamma vector, with the sign in which it enters the Weil balance. -/
def gammaVec3 (kFam : Fin 3 → ℝ → ℂ) : Fin 3 → ℝ :=
  fun i => -reim (gammaTerm (kFam i))

/-- Literal pole vector, with the sign in which it enters the Weil balance. -/
def poleVec3 (kFam : Fin 3 → ℝ → ℂ) : Fin 3 → ℝ :=
  fun i => -reim (poleTerm (kFam i))

/-- **Cutset U2, before quotienting.**  The literal zeta Weil formula on any three
admissible test functions is a five-channel vector identity on the exact carrier. -/
theorem literalWeilThreeSampleBalance {kFam : Fin 3 → ℝ → ℂ}
    (hk : ∀ i, ContDiff ℝ 2 (kFam i))
    (hkc : ∀ i, HasCompactSupport (kFam i)) (ρstar : Zeros) :
    targetVec3 kFam ρstar + otherVec3 kFam ρstar + primeVec3 kFam
      + gammaVec3 kFam + poleVec3 kFam = 0 := by
  funext i
  have h := literalWeilFiveTermBalance (hk i) (hkc i) ρstar
  have hr : reim (zeroTerm (kFam i) ρstar + otherZerosTerm (kFam i) ρstar
      + primeTerm (kFam i) + (-gammaTerm (kFam i)) + (-poleTerm (kFam i))) = 0 := by
    rw [h]
    exact reim_zero
  simp only [reim_add, reim_neg] at hr
  simpa [targetVec3, otherVec3, primeVec3, gammaVec3, poleVec3] using hr

/-- **Cutset U2, post deterministic-pole quotient.**  If the literal pole vector
is exactly the sum of the two certified deterministic nuisance directions, exact
Schur elimination removes it with no residual term.  The remaining carrier is
literally target + unselected zeros + prime + gamma. -/
theorem postPoleQuotientLiteralBalance
    {kFam : Fin 3 → ℝ → ℂ} {ρstar : Zeros}
    (hk : ∀ i, ContDiff ℝ 2 (kFam i))
    (hkc : ∀ i, HasCompactSupport (kFam i))
    {pole₁ pole₂ : Fin 3 → ℝ}
    (h₁ : pole₁ ≠ 0) (h₂ : perp2 pole₁ pole₂ ≠ 0)
    (hpole : poleVec3 kFam = pole₁ + pole₂) :
    elim2 pole₁ pole₂ (targetVec3 kFam ρstar)
      + elim2 pole₁ pole₂ (otherVec3 kFam ρstar)
      + elim2 pole₁ pole₂ (primeVec3 kFam)
      + elim2 pole₁ pole₂ (gammaVec3 kFam) = 0 := by
  have h := literalWeilThreeSampleBalance hk hkc ρstar
  rw [hpole] at h
  have hbal : targetVec3 kFam ρstar + pole₁ + pole₂ + otherVec3 kFam ρstar
      + primeVec3 kFam + gammaVec3 kFam + (0 : Fin 3 → ℝ) = 0 := by
    simpa [add_assoc, add_left_comm, add_comm] using h
  have hq := projected_balance h₁ h₂ hbal
  simpa [elim2_zero, add_assoc] using hq

end LiteralWeilThreeSampleProjectedCarrier
end Zeta23Bridge
