import Integration.Paper9CM163LiteralPacket

/-! SOURCE-WRITTEN, UNCOMPILED. The integer residual is an actual
polynomial equality modulo X^r, not a checksum or a boolean oracle.
Concrete executable-array soundness and J coefficient casts remain
open; this module isolates their exact destination. -/
namespace Integration.Paper9IntegerSectorWeld
open Polynomial
open scoped BigOperators
open Integration.Paper9CyclotomicPacketReflection

noncomputable section
def castPoly (P : Polynomial ℤ) : Polynomial ℂ :=
  P.map (Int.castRingHom ℂ)

def eulerZ (P : Polynomial ℤ) : Polynomial ℤ := Polynomial.X*P.derivative

theorem castEuler (P : Polynomial ℤ) : castPoly (eulerZ P)=euler (castPoly P) := by
  unfold castPoly eulerZ euler
  rw [Polynomial.map_mul,Polynomial.map_X,Polynomial.derivative_map]

theorem castResidual (P Q : Polynomial ℤ) (r : ℕ)
    (h : Polynomial.X^r ∣ eulerZ P-P*Q) :
    Polynomial.X^r ∣ euler (castPoly P)-castPoly P*castPoly Q := by
  obtain ⟨G,hG⟩ := h
  refine ⟨castPoly G,?_⟩
  have he := congrArg castPoly hG
  simpa [castPoly,eulerZ,euler,Polynomial.map_sub,Polynomial.map_mul,
    Polynomial.map_pow,Polynomial.map_X,Polynomial.derivative_map] using he

-- Finite uniqueness of the denominator-cleared Euler recurrence.
-- Compare the antidiagonal sums directly; the i=0 term is killed
-- by V(0)=0, and every other term uses a strictly smaller index.
theorem finiteEulerUnique (D : ℕ) (V A B : Polynomial ℂ)
    (hv : V.coeff 0=0) (h0 : A.coeff 0=B.coeff 0)
    (ha : ∀ n≤D, (n:ℂ)*A.coeff n=(V*A).coeff n)
    (hb : ∀ n≤D, (n:ℂ)*B.coeff n=(V*B).coeff n) :
    ∀ n≤D, A.coeff n=B.coeff n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hzero : n=0
    · simpa [hzero] using h0
    have hs : (V*A).coeff n=(V*B).coeff n := by
      rw [Polynomial.coeff_mul,Polynomial.coeff_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      have hsum := Finset.Nat.mem_antidiagonal.mp hij
      by_cases hi : ij.1=0
      · simp [hi,hv]
      · rw [ih ij.2 (by omega) (by omega)]
    exact mul_left_cancel₀ (by exact_mod_cast hzero)
      ((ha n hn).trans (hs.trans (hb n hn).symm))

theorem normZero (H : Polynomial ℂ) (h : H.coeff 0=1) :
    (Polynomial.contract 41 (cyclicNorm H)).coeff 0=1 := by
  rw [Polynomial.coeff_contract (by decide : 41≠0),zero_mul]
  unfold cyclicNorm
  simp [Polynomial.coeff_zero_eq_eval_zero,scale,Polynomial.eval_comp,
    ← Polynomial.coeff_zero_eq_eval_zero,h]

-- Integer L and N from the original recurrence. All four boundary
-- premises are explicit; no arbitrary equality of analytic functions.
theorem integerNormCast (H L N : Polynomial ℤ) (D : ℕ)
    (hH : H.coeff 0=1) (hL : L.coeff 0=0) (hN : N.coeff 0=1)
    (hlog : Polynomial.X^(41*D+1) ∣ eulerZ H-H*L)
    (hnorm : Polynomial.X^(D+1) ∣ eulerZ N-N*Polynomial.contract 41 L) :
    ∀ n≤D, (Polynomial.contract 41 (cyclicNorm (castPoly H))).coeff n=
      (castPoly N).coeff n := by
  let V := Polynomial.contract 41 (castPoly L)
  have hV : V.coeff 0=0 := by
    simp [V,Polynomial.coeff_contract (by decide : 41≠0),castPoly,hL]
  have h0 : (Polynomial.contract 41 (cyclicNorm (castPoly H))).coeff 0=
      (castPoly N).coeff 0 := by
    rw [normZero _ (by simp [castPoly,hH])]
    simp [castPoly,hN]
  apply finiteEulerUnique D V _ _ hV h0
  · intro n hn
    simpa [V,mul_comm] using normRecurrenceActual (castPoly H) (castPoly L) D n
      (castResidual _ _ _ hlog) hn
  · intro n hn
    have he := castResidual N (Polynomial.contract 41 L) (D+1) hnorm
    have hz := Polynomial.X_pow_dvd_iff.mp he n (by omega)
    rw [Polynomial.coeff_sub,eulerCoeff,sub_eq_zero] at hz
    have hcontract : castPoly (Polynomial.contract 41 L)=V := by
      unfold castPoly V
      exact Polynomial.map_contract (by decide : 41≠0)
    simpa [hcontract,mul_comm] using hz

-- Finite multiplication preserves coefficient equality below the cut.
theorem mulCoeffTransport (D : ℕ) (G A B : Polynomial ℂ)
    (h : ∀ n≤D, A.coeff n=B.coeff n) :
    ∀ n≤D, (G*A).coeff n=(G*B).coeff n := by
  intro n hn
  rw [Polynomial.coeff_mul,Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hs := Finset.Nat.mem_antidiagonal.mp hij
  rw [h ij.2 (by omega)]

-- Map the exact integer residual, not the packet's hash.
theorem integerColumnResidual (D : ℕ) (G N C : Polynomial ℤ)
    (h : Polynomial.X^(D+1) ∣ G*N-C) :
    ∀ n≤D, ((castPoly G)*(castPoly N)-castPoly C).coeff n=0 := by
  intro n hn
  have hz := Polynomial.X_pow_dvd_iff.mp h n (by omega)
  simpa [castPoly,← Polynomial.map_mul,← Polynomial.map_sub,hz]

end
end Integration.Paper9IntegerSectorWeld
