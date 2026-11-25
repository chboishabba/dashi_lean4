import Integration.Paper9ConcreteSectorConsumer

/-! SOURCE-WRITTEN, UNCOMPILED.
A4: original CM point and original literal diagonal only. Use the exact
binomial shift of the signed integer packet and the existing half-unit
isolation consumer. No CM integrality or inverse-j premise. The dyadic
enclosure still needs formal analytic reflection. -/
namespace Integration.Paper9ActualCMRoot
open Complex UpperHalfPlane Polynomial
open scoped BigOperators
open Integration.Paper9ActualCMPoint
open Integration.Paper9Hecke41ChartGeometry
open Integration.Paper9HeckeProductAssembly
open Integration.Paper9CM163LiteralPacket
open Integration.Paper9CM163CertificateConsumer
open Integration.Paper9OriginalEisensteinCoeff
open Integration.Paper9ActualJSourceJet

abbrev K : ℤ := -(640320^3)
def shiftedZ (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range 83, diagonal[k]?.getD 0 *
    K^(82-k-n) * ((82-k).choose n : ℤ)

theorem shiftAbove (n : ℕ) (hn : 82<n) : shiftedZ n=0 := by
  unfold shiftedZ
  apply Finset.sum_eq_zero
  intro k hk
  rw [Nat.choose_eq_zero_of_lt (by omega : 82-k<n)]
  simp

-- All integer coefficients are taken from the original descending packet.
-- Mathlib coeff_X_add_C_pow includes the n>degree zero sector.
noncomputable section
def shifted : Polynomial ℂ := (packet 82 diagCoeff).comp (X+C (K:ℂ))
def complement : Polynomial ℂ :=
  ∑ i ∈ Finset.range 81, C (shiftedZ (i+2):ℂ)*X^i

theorem shiftedCoeff (n : ℕ) : shifted.coeff n=(shiftedZ n:ℂ) := by
  unfold shifted packet shiftedZ
  simp only [Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.pow_comp, Polynomial.X_comp, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow, diagCoeff]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem complementCoeff (n : ℕ) :
    complement.coeff n=(shiftedZ (n+2):ℂ) := by
  unfold complement
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hn : n<81
  · rw [Finset.sum_eq_single n]
    · simp
    · intro i hi hne
      simp [Ne.symm hne]
    · simp [hn]
  · rw [shiftAbove (n+2) (by omega)]
    apply Finset.sum_eq_zero
    intro i hi
    have hlt := Finset.mem_range.mp hi
    simp [show n≠i by omega]

theorem shiftedFactor (h0 : shiftedZ 0=0) (h1 : shiftedZ 1=0) :
    shifted=X^2*complement := by
  ext n
  rw [shiftedCoeff, Polynomial.coeff_X_pow_mul']
  split_ifs with hn
  · rw [complementCoeff, Nat.sub_add_cancel hn]
  · have h : n=0 ∨ n=1 := by omega
    rcases h with rfl|rfl <;> simp [h0,h1]

-- Actual q is negative real. Its reflected point has the same q, so
-- actual j is conjugation-fixed without a new real-slice carrier.
local notation "j" => Integration.MoonshineEisensteinAgdaTarget.jTarget
theorem cmJReal : (j cmTau).im=0 := by
  let σ := Integration.MoonshineEisensteinAgdaTarget.negConj cmTau
  have hq : qExt σ=qExt cmTau := by
    change Periodic.qParam 1 (σ : ℂ)=Periodic.qParam 1 (cmTau : ℂ)
    rw [← qOfTargetPeriodic σ, ← qOfTargetPeriodic cmTau]
    unfold σ
    rw [Integration.MoonshineEisensteinAgdaTarget.qOfTarget_negConj,
      qOfTargetPeriodic cmTau, cmQPhase]
    simp
  have hj : j σ=j cmTau := by rw [jAtQ,jAtQ,hq]
  have hc := Integration.MoonshineEisensteinAgdaTarget.jTarget_negConj cmTau
  have he : j cmTau=conj (j cmTau) := hj.symm.trans hc
  have hi := congrArg Complex.im he
  simp only [Complex.conj_im] at hi
  linarith

-- All four remaining premises are literal: the existing diagonal
-- coefficient gate, two integer shift zeros, integer dominance reflected
-- to the real inequality, and the actual dyadic half-unit enclosure.
theorem cmRootFromDiagonal (hgate : diagonalGate)
    (h0 : shiftedZ 0=0) (h1 : shiftedZ 1=0)
    (hdom : (∑ i ∈ Finset.range 80,
      |(shiftedZ (i+3):ℝ)|*(1/2:ℝ)^(i+1)) < |(shiftedZ 2:ℝ)|)
    (hdyadic : |(j cmTau).re-(K:ℝ)|≤1/2) :
    j cmTau=(K:ℂ) := by
  let u : ℝ := (j cmTau).re-(K:ℝ)
  have hj : j cmTau=(K:ℂ)+(u:ℂ) := by
    apply Complex.ext <;> simp [u,cmJReal]
  have hp : (packet 82 diagCoeff).eval (j cmTau)=0 :=
    (actualDiagonal hgate cmTau).symm.trans cmProductZero
  have hz : shifted.eval (u:ℂ)=0 := by
    unfold shifted
    rw [Polynomial.eval_comp]
    simpa [add_comm,hj] using hp
  rw [shiftedFactor h0 h1, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X] at hz
  have hr : u^2*((shiftedZ 2:ℝ)+∑ i ∈ Finset.range 80,
      (shiftedZ (i+3):ℝ)*u^(i+1))=0 := by
    unfold complement at hz
    simp only [Polynomial.eval_finset_sum,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X] at hz
    rw [Finset.sum_range_succ'] at hz
    have hcast : ((u^2*((shiftedZ 2:ℝ)+∑ i ∈ Finset.range 80,
      (shiftedZ (i+3):ℝ)*u^(i+1)) : ℝ):ℂ)=0 := by
      push_cast
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,add_comm] using hz
    exact_mod_cast hcast
  have hu := isolateHalfUnit u (shiftedZ 2:ℝ)
    (fun i => (shiftedZ (i+3):ℝ)) hdyadic hdom hr
  rw [hj,hu]
  simp
end
end Integration.Paper9ActualCMRoot
