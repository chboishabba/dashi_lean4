import Integration.Paper9ThetaModularTransport
import Integration.Paper9SignedEisensteinCuspTail

/-! SOURCE-WRITTEN, kernel pending. Actual theta cusp normalization
on the original analytic summands. Use signed integer pairing and
the existing geometric norm-tail theorem. No modular uniqueness is
assumed and no first coefficient is inserted as a normalization. -/
namespace Integration.Paper9ThetaCuspNormalization
open Complex Filter Function UpperHalfPlane
open scoped Topology BigOperators
open Integration.Paper9ThetaModularTransport
open Integration.Paper9SignedEisensteinCuspTail
noncomputable section

def t (z : ℂ) := Complex.exp (p*z)
def tQuarter (z : ℂ) := Complex.exp (p*z/4)

theorem tRead (z : ℂ) : t z=Periodic.qParam 2 z := by
  unfold t p Periodic.qParam
  congr 1
  ring

theorem quarterRead (z : ℂ) : tQuarter z=Periodic.qParam 8 z := by
  unfold tQuarter p Periodic.qParam
  congr 1
  ring

theorem tT (z : ℂ) : t (z+1)= -t z := by
  unfold t
  rw [show p*(z+1)=p*z+p by ring,Complex.exp_add]
  rw [show Complex.exp p = -1 from Complex.exp_pi_mul_I]
  ring

theorem tNorm (z : ℍ) : ‖t z‖<1 := by
  unfold t
  rw [Complex.norm_exp]
  have hr : (p*(z:ℂ)).re= -Real.pi*z.im := by simp [p,Complex.mul_re]
  rw [hr,Real.exp_lt_one_iff]
  exact neg_lt_zero.mpr (mul_pos Real.pi_pos z.2)

theorem tLimit : Tendsto (fun z : ℍ => t z) atImInfty (𝓝 0) := by
  simp_rw [tRead]
  exact UpperHalfPlane.qParam_tendsto_atImInfty (h:=2) (by norm_num)

theorem quarterLimit : Tendsto (fun z : ℍ => tQuarter z) atImInfty (𝓝 0) := by
  simp_rw [quarterRead]
  exact UpperHalfPlane.qParam_tendsto_atImInfty (h:=8) (by norm_num)

theorem tPower (z : ℂ) (n : ℕ) :
    t z^n=Complex.exp ((n:ℂ)*p*z) := by
  unfold t
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

-- Positive/negative integer pair, including the original zero term.
theorem squareTerm (z : ℂ) (n : ℕ) :
    jacobiTheta₂_term (n:ℤ) 0 z=t z^(n*n) ∧
    jacobiTheta₂_term (-(n:ℤ)) 0 z=t z^(n*n) := by
  rw [tPower]
  constructor <;> unfold jacobiTheta₂_term p <;> push_cast <;> congr 1 <;> ring

theorem triangularTerm (z : ℂ) (n : ℕ) :
    jacobiTheta₂_term (n:ℤ) (z/2) z=t z^(n*(n+1)) ∧
    jacobiTheta₂_term (-(n:ℤ)-1) (z/2) z=t z^(n*(n+1)) := by
  rw [tPower]
  constructor <;> unfold jacobiTheta₂_term p <;> push_cast <;> congr 1 <;> ring

def sqTail (q : ℂ) (n : ℕ) := q^((n+1)*(n+1))
def triTail (q : ℂ) (n : ℕ) := q^(n*(n+1))

theorem sqSummable (q : ℂ) (hq : ‖q‖<1) : Summable (sqTail q) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_norm_lt_one (r:=‖q‖) (by simpa using hq)).mul_left ‖q‖)
  intro n
  unfold sqTail
  rw [norm_pow,← pow_succ']
  apply pow_le_pow_of_le_one (norm_nonneg _) hq.le
  have h := Nat.mul_le_mul_left (n+1) (show 1≤n+1 by omega)
  omega

theorem triSummable (q : ℂ) (hq : ‖q‖<1) : Summable (triTail q) := by
  apply Summable.of_norm_bounded
    (summable_geometric_of_norm_lt_one (r:=‖q‖) (by simpa using hq))
  intro n
  unfold triTail
  rw [norm_pow]
  apply pow_le_pow_of_le_one (norm_nonneg _) hq.le
  have h := Nat.mul_le_mul_left n (show 1≤n+1 by omega)
  omega

theorem th3Read (z : ℍ) : th3 z=1+2*(∑' n, sqTail (t z) n) := by
  let f : ℤ → ℂ := fun n => jacobiTheta₂_term n 0 z
  have hs : Summable f := (hasSum_jacobiTheta₂_term 0 z.2).summable
  have h := tsum_nat_add_neg hs
  rw [hs.nat_add_neg.tsum_eq_zero_add] at h
  have h0 : f 0=1 := by simp [f,jacobiTheta₂_term]
  have hp : (fun n : ℕ => f (↑(n+1):ℤ)+f (-(↑(n+1):ℤ))) =
      fun n => 2*sqTail (t z) n := by
    funext n
    rw [(squareTerm z (n+1)).1,(squareTerm z (n+1)).2]
    unfold sqTail
    ring
  change f 0+f 0+(∑' n : ℕ, f (↑(n+1):ℤ)+f (-(↑(n+1):ℤ))) =
    (∑' n : ℤ, f n)+f 0 at h
  rw [hp,h0,tsum_mul_left] at h
  change th3 z=_
  unfold th3 jacobiTheta₂
  linear_combination -h

def translated (z : ℍ) : ℍ := ⟨(z:ℂ)+1,by simpa using z.2⟩

theorem th4Read (z : ℍ) : th4 z=1+2*(∑' n, sqTail (-t z) n) := by
  have h := th3Read (translated z)
  change th3 ((z:ℂ)+1)=1+2*(∑' n, sqTail (t ((z:ℂ)+1)) n) at h
  rw [th3T,tT] at h
  exact h

theorem th2Read (z : ℍ) : th2 z=2*tQuarter z*(∑' n, triTail (t z) n) := by
  let f : ℤ → ℂ := fun n => jacobiTheta₂_term n ((z:ℂ)/2) z
  have hs : Summable f := (hasSum_jacobiTheta₂_term ((z:ℂ)/2) z.2).summable
  have h := tsum_nat_add_neg_add_one hs
  have hp : (fun n : ℕ => f (n:ℤ)+f (-((n:ℤ)+1))) =
      fun n => 2*triTail (t z) n := by
    funext n
    change jacobiTheta₂_term (n:ℤ) ((z:ℂ)/2) z +
      jacobiTheta₂_term (-((n:ℤ)+1)) ((z:ℂ)/2) z = _
    rw [show -((n:ℤ)+1)=-(n:ℤ)-1 by ring,
      (triangularTerm z n).1,(triangularTerm z n).2]
    unfold triTail
    ring
  rw [hp,tsum_mul_left] at h
  unfold th2 tQuarter jacobiTheta₂
  rw [← h]
  ring

-- Explicit common geometric tails; the zero mode is kept at 1.
theorem sqBound (q : ℂ) (hq : ‖q‖≤1/2) :
    ‖∑' n, sqTail q n‖≤2*‖q‖ := by
  apply normTail _ ‖q‖ (norm_nonneg _) (sqSummable q (by linarith))
  intro n
  unfold sqTail
  rw [norm_pow]
  calc
    _ ≤ ‖q‖^(n+1) := by
      apply pow_le_pow_of_le_one (norm_nonneg _) (by linarith)
      have h := Nat.mul_le_mul_left (n+1) (show 1≤n+1 by omega)
      omega
    _ = ‖q‖*‖q‖^n := by rw [pow_succ']
    _ ≤ _ := by gcongr

theorem triBound (q : ℂ) (hq : ‖q‖≤1/2) :
    ‖∑' n, triTail q n‖≤2 := by
  have h := normTail (triTail q) 1 (by norm_num) (triSummable q (by linarith))
    (fun n => by
      unfold triTail
      rw [norm_pow,one_mul]
      calc
        _ ≤ ‖q‖^n := by
          apply pow_le_pow_of_le_one (norm_nonneg _) (by linarith)
          have h := Nat.mul_le_mul_left n (show 1≤n+1 by omega)
          omega
        _ ≤ _ := by gcongr)
  norm_num at h
  exact h

theorem cuspSmall : ∀ᶠ z : ℍ in atImInfty, ‖t z‖≤1/2 := by
  filter_upwards [tLimit.eventually (Metric.ball_mem_nhds (0:ℂ)
    (by norm_num : (0:ℝ)<1/2))] with z hz
  exact (Metric.mem_ball_zero_iff.mp hz).le

theorem th3Error (z : ℍ) (h : ‖t z‖≤1/2) : ‖th3 z-1‖≤4*‖t z‖ := by
  rw [th3Read,show (1+2*(∑' n, sqTail (t z) n))-1=2*(∑' n, sqTail (t z) n) by ring,
    norm_mul,norm_ofNat]
  linarith [sqBound (t z) h]

theorem th4Error (z : ℍ) (h : ‖t z‖≤1/2) : ‖th4 z-1‖≤4*‖t z‖ := by
  rw [th4Read,show (1+2*(∑' n, sqTail (-t z) n))-1=2*(∑' n, sqTail (-t z) n) by ring,
    norm_mul,norm_ofNat]
  have hb := sqBound (-t z) (by simpa using h)
  rw [norm_neg] at hb
  linarith

theorem th2Error (z : ℍ) (h : ‖t z‖≤1/2) : ‖th2 z‖≤4*‖tQuarter z‖ := by
  rw [th2Read,norm_mul,norm_mul,norm_ofNat]
  nlinarith [triBound (t z) h,mul_le_mul_of_nonneg_left
    (triBound (t z) h) (norm_nonneg (tQuarter z))]

-- Use the explicit epsilon-neighbourhood version to keep the
-- varying geometric bound and actual positive-height domain.
theorem limitOfError (f : ℍ → ℂ) (c : ℂ) (g : ℍ → ℂ)
    (hg : Tendsto g atImInfty (𝓝 0))
    (h : ∀ᶠ z in atImInfty, ‖f z-c‖≤4*‖g z‖) :
    Tendsto f atImInfty (𝓝 c) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h,hg.eventually (Metric.ball_mem_nhds (0:ℂ)
    (show 0<ε/4 by positivity))] with z hz hw
  rw [dist_eq_norm]
  have hw' := Metric.mem_ball_zero_iff.mp hw
  linarith

theorem th3Limit : Tendsto (fun z : ℍ => th3 z) atImInfty (𝓝 1) :=
  limitOfError _ 1 t tLimit (cuspSmall.mono th3Error)

theorem th4Limit : Tendsto (fun z : ℍ => th4 z) atImInfty (𝓝 1) :=
  limitOfError _ 1 t tLimit (cuspSmall.mono th4Error)

theorem th2Limit : Tendsto (fun z : ℍ => th2 z) atImInfty (𝓝 0) :=
  limitOfError _ 0 tQuarter quarterLimit (cuspSmall.mono (fun z h => by simpa using th2Error z h))

theorem E4Limit : Tendsto at4 atImInfty (𝓝 1) := by
  have ha := th2Limit.pow 4
  have hb := th3Limit.pow 4
  have hc := th4Limit.pow 4
  have h := (((ha.pow 2).add (hb.pow 2)).add (hc.pow 2)).div_const (2:ℂ)
  simpa [at4,thetaE4,A,B,C] using h

theorem E6Limit : Tendsto at6 atImInfty (𝓝 1) := by
  have ha := th2Limit.pow 4
  have hb := th3Limit.pow 4
  have hc := th4Limit.pow 4
  have h := (((ha.add hb).mul (hb.add hc)).mul (hc.sub ha)).div_const (2:ℂ)
  simpa [at6,thetaE6,A,B,C] using h

#print axioms th3Read
#print axioms th2Read
#print axioms E4Limit
#print axioms E6Limit
end
end Integration.Paper9ThetaCuspNormalization
