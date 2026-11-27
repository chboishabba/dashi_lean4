import Synthesis.NavierStokesPhysicalCoefficientExact

/-! Literal scalar clauses of Alpöge–Buckmaster ExtendedStatement.lean
(ad53419). Symbols: C=coerciveTotal, H=supBoundFactor weight,
X=sizeBound, D=defectMax, P=periodMax/twist,
F=1/weight+2*P*formBound, A=actuatorBound/multiplierWeight.
No claim that physical data attain these inequalities. -/
namespace Synthesis
noncomputable section

def nsCertCap (C H : ℝ) : ℝ := 1/(2*C*H)
def nsCertSecond (C P F A X : ℝ) : ℝ :=
  4*X^2*(F+2*P*A+2*P/C)
def nsCertThirdConstant (P F A X D : ℝ) : ℝ :=
  4*F*X^2+4*P*X*D+8*P*A*X^2
def nsCertThirdLinear (P H X : ℝ) : ℝ := 8*P*H*X^2

theorem nsCertThirdExpansion (P F A X D H U : ℝ) :
    4*F*X^2+4*P*X*(D+2*H*X*U+2*A*X) =
      nsCertThirdConstant P F A X D + nsCertThirdLinear P H X*U := by
  unfold nsCertThirdConstant nsCertThirdLinear
  ring

/-- Construct a strict first-clause witness from the two endpoint margins.
The third polynomial need not be monotone on the whole positive axis. -/
theorem nsCertSmallnessFeasible (cap S a b : ℝ)
    (hc : 0 < cap) (hb : 0 ≤ b) (ha : 0 ≤ a) :
    (∃ U : ℝ, 0 < U ∧ U < cap ∧ S ≤ U^2 ∧ a+b*U ≤ U^2) ↔
    S < cap^2 ∧ a+b*cap < cap^2 := by
  constructor
  · rintro ⟨U,hU,hUc,hS,hT⟩
    have hsq : U^2 < cap^2 := by nlinarith
    have hbU : b ≤ U := by
      by_contra hn
      have hh : 0 < (b-U)*U := mul_pos (lt_of_not_ge hn) hU
      nlinarith
    have hprod : 0 < (cap-U)*(cap+U-b) :=
      mul_pos (sub_pos.mpr hUc) (by linarith)
    exact ⟨hS.trans_lt hsq,by nlinarith only [hprod,hT]⟩
  · rintro ⟨hS,hT⟩
    let ε := min (cap/2) (min ((cap^2-S)/(4*cap)) ((cap^2-a-b*cap)/(4*cap)))
    have hden : 0 < 4*cap := by positivity
    have he : 0 < ε := by
      dsimp [ε]
      exact lt_min (by positivity)
        (lt_min (div_pos (sub_pos.mpr hS) hden)
          (div_pos (by linarith) hden))
    have hec : ε ≤ cap/2 := min_le_left _ _
    have heS : ε ≤ (cap^2-S)/(4*cap) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have heT : ε ≤ (cap^2-a-b*cap)/(4*cap) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have h1 := (le_div_iff₀ hden).mp heS
    have h2 := (le_div_iff₀ hden).mp heT
    have hce : 0 ≤ cap*ε := mul_nonneg hc.le he.le
    have hbe : 0 ≤ b*ε := mul_nonneg hb he.le
    refine ⟨cap-ε,by linarith,by linarith,?_,?_⟩
    · nlinarith only [h1,hce,sq_nonneg ε]
    · nlinarith only [h2,hce,hbe,sq_nonneg ε]

/-- Literal transfer_loss and coerciveTotal_ge: minimal admissible
inverse constant when the transfer gap is strict. -/
theorem nsCertTransferBidi (L R gap total : ℝ)
    (h : (L+R)*gap < 1) :
    L+R ≤ (1-(L+R)*gap)*total ↔
      (L+R)/(1-(L+R)*gap) ≤ total := by
  rw [div_le_iff₀ (sub_pos.mpr h)]
  constructor <;> intro h' <;> simpa [mul_comm] using h'

/-- Exact literal size condition after solving the transfer denominator. -/
theorem nsCertSizeBidi (L R pin defect rows target gap size : ℝ)
    (h : (L+R)*gap < 1) :
    L*defect+rows+pin*target ≤ (1-(L+R)*gap)*size ↔
      (L*defect+rows+pin*target)/(1-(L+R)*gap) ≤ size := by
  rw [div_le_iff₀ (sub_pos.mpr h)]
  constructor <;> intro h' <;> simpa [mul_comm] using h'

end
end Synthesis
