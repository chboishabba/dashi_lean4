import Synthesis.YMCMP99Path13DexpInverseSeriesExact
import Mathlib.Analysis.Normed.Algebra.QuaternionExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! The actual SU(2) quaternion word angle and commutator operator.
For the link ball measured in principal angle (not chord distance),
the principal logarithm norm of a length L word is at most L e.
The operator is the literal quaternion commutator, not a supplied
matrix named ad. The source differential equality to dexpSeries
and selected H(s(Y0)) attachment still remain.
-/
namespace CMP99Pivot.Path13
open scoped Quaternion RealInnerProductSpace
noncomputable section

abbrev Q := Quaternion ℝ
def qAngle (q : Q) := Real.arccos q.re

theorem qAngle_nonneg (q : Q) : 0≤qAngle q := Real.arccos_nonneg _
theorem qAngle_le_pi (q : Q) : qAngle q≤Real.pi := Real.arccos_le_pi _

theorem unit_quaternion_coordinates (q : Q) (hq : ‖q‖=1) :
    q.re^2+q.imI^2+q.imJ^2+q.imK^2=1 := by
  have h := Quaternion.normSq_eq_norm_mul_self q
  rw [hq,one_mul,Quaternion.normSq_def'] at h
  exact h

theorem qAngle_cos (q : Q) (hq : ‖q‖=1) : Real.cos (qAngle q)=q.re := by
  have h := unit_quaternion_coordinates q hq
  apply Real.cos_arccos <;> nlinarith [sq_nonneg q.imI,sq_nonneg q.imJ,sq_nonneg q.imK]

theorem qAngle_sin_nonnegative (q : Q) : 0≤Real.sin (qAngle q) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (qAngle_nonneg q) (qAngle_le_pi q)

theorem qAngle_sin_eq_im_norm (q : Q) (hq : ‖q‖=1) :
    Real.sin (qAngle q)=‖q.im‖ := by
  have hc := unit_quaternion_coordinates q hq
  have hi := Quaternion.normSq_eq_norm_mul_self q.im
  rw [Quaternion.normSq_def'] at hi
  change 0^2+q.imI^2+q.imJ^2+q.imK^2=‖q.im‖*‖q.im‖ at hi
  have hs := Real.sin_sq_add_cos_sq (qAngle q)
  rw [qAngle_cos q hq] at hs
  have he : Real.sin (qAngle q)^2=‖q.im‖^2 := by nlinarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h|h
  · exact h
  · linarith [qAngle_sin_nonnegative q,norm_nonneg q.im]

/-- The scalar part of the actual quaternion product bounds the cosine
of the sum of principal angles. No commutativity of the word. -/
theorem qAngle_mul_le (q p : Q) (hq : ‖q‖=1) (hp : ‖p‖=1)
    (hsmall : qAngle q+qAngle p≤Real.pi) :
    qAngle (q*p)≤qAngle q+qAngle p := by
  have hinner := real_inner_le_norm q.im p.im
  rw [Quaternion.inner_def] at hinner
  have hd : (q.im*star p.im).re=q.imI*p.imI+q.imJ*p.imJ+q.imK*p.imK := by
    simp [Quaternion.re_mul] <;> ring
  rw [hd,← qAngle_sin_eq_im_norm q hq,← qAngle_sin_eq_im_norm p hp] at hinner
  have hcos : Real.cos (qAngle q+qAngle p)≤(q*p).re := by
    rw [Real.cos_add,qAngle_cos q hq,qAngle_cos p hp,Quaternion.re_mul]
    linarith
  have h := Real.arccos_le_arccos hcos
  rw [Real.arccos_cos (add_nonneg (qAngle_nonneg q) (qAngle_nonneg p)) hsmall] at h
  exact h

theorem qWord_unit (p : List Q) (hp : ∀ q∈p,‖q‖=1) :
    ‖p.prod‖=1 := by
  induction p with
  | nil => simp
  | cons q p ih =>
    rw [List.prod_cons,norm_mul,hp q (List.mem_cons_self),ih (fun r hr=>hp r (List.mem_cons_of_mem _ hr)),one_mul]

theorem qWord_angle (p : List Q) (e : ℝ) (he : 0≤e)
    (hp : ∀ q∈p,‖q‖=1 ∧ qAngle q≤e)
    (hsmall : (p.length:ℝ)*e≤Real.pi) :
    qAngle p.prod≤(p.length:ℝ)*e := by
  induction p with
  | nil => simp [qAngle]
  | cons q p ih =>
    have hq := hp q List.mem_cons_self
    have hrest := fun r hr=>hp r (List.mem_cons_of_mem _ hr)
    have hh : (p.length:ℝ)*e≤Real.pi := by
      simp only [List.length_cons,Nat.cast_succ] at hsmall
      nlinarith
    have htail := ih hrest hh
    have hs : qAngle q+qAngle p.prod≤Real.pi := by
      simp only [List.length_cons,Nat.cast_succ] at hsmall
      nlinarith [hq.2,htail]
    rw [List.prod_cons,List.length_cons,Nat.cast_succ]
    have h := qAngle_mul_le q p.prod hq.1 (qWord_unit p (fun r hr=>(hrest r hr).1)) hs
    linarith [hq.2,htail]

def qPrincipalVector (q : Q) : Q :=
  (qAngle q/‖q.im‖) • q.im

theorem qPrincipalVector_norm_le (q : Q) : ‖qPrincipalVector q‖≤qAngle q := by
  unfold qPrincipalVector
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (qAngle_nonneg q) (norm_nonneg _))]
  by_cases h : ‖q.im‖=0
  · simp [h,qAngle_nonneg]
  · rw [div_mul_cancel₀ _ h]

theorem qPrincipalVector_re (q : Q) : (qPrincipalVector q).re=0 := by
  simp [qPrincipalVector]

/-- The actual pure quaternion commutator and its operator bound. -/
def qAdLinear (X : Q) : Q →ₗ[ℝ] Q where
  toFun H := X*H-H*X
  map_add' H K := by noncomm_ring
  map_smul' r H := by simp [mul_smul_comm,smul_mul_assoc,smul_sub]

theorem qAdLinear_bound (X H : Q) :
    ‖qAdLinear X H‖≤(2*‖X‖)*‖H‖ := by
  change ‖X*H-H*X‖≤_
  calc
    _ ≤ ‖X*H‖+‖H*X‖ := norm_sub_le _ _
    _ = _ := by rw [norm_mul,norm_mul]; ring

def qAd (X : Q) : Q →L[ℝ] Q :=
  (qAdLinear X).mkContinuous (2*‖X‖) (qAdLinear_bound X)

theorem qAd_norm (X : Q) : ‖qAd X‖≤2*‖X‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (qAdLinear_bound X)

/-- The length-74 source word pays the exact commutator radius on
the angle-defined link ball. If the source uses a chord radius,
a separate conversion is required; they are not interchangeable. -/
theorem qPath74_ad_radius (p : List Q) (e : ℝ) (he : 0≤e)
    (hp : ∀ q∈p,‖q‖=1 ∧ qAngle q≤e) (hL : p.length≤74)
    (hsmall : 74*e≤Real.pi) :
    ‖qAd (qPrincipalVector p.prod)‖≤148*e := by
  have hlen : (p.length:ℝ)≤74 := by exact_mod_cast hL
  have hs := mul_le_mul_of_nonneg_right hlen he
  have ha := qWord_angle p e he hp (hs.trans hsmall)
  have hn := qPrincipalVector_norm_le p.prod
  have h := qAd_norm (qPrincipalVector p.prod)
  linarith

/-- The quaternion principal vector exponentiates back to the same
unit word whenever its imaginary part is nonzero. This selects the
principal angle rather than a separate logarithm branch. Identity
is handled separately; the antipodal point is excluded. -/
theorem qPrincipalVector_exp (q : Q) (hq : ‖q‖=1) (hi : ‖q.im‖≠0) :
    NormedSpace.exp (qPrincipalVector q)=q := by
  have hnorm : ‖qPrincipalVector q‖=qAngle q := by
    unfold qPrincipalVector
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg
      (div_nonneg (qAngle_nonneg q) (norm_nonneg _)),div_mul_cancel₀ _ hi]
  have ht : qAngle q≠0 := by
    intro h
    have hs := qAngle_sin_eq_im_norm q hq
    rw [h,Real.sin_zero] at hs
    exact hi hs.symm
  rw [Quaternion.exp_of_re_eq_zero _ (qPrincipalVector_re q),hnorm,
    qAngle_cos q hq,qAngle_sin_eq_im_norm q hq]
  unfold qPrincipalVector
  rw [smul_smul]
  have h : ‖q.im‖/qAngle q*(qAngle q/‖q.im‖)=1 := by field_simp [hi,ht]
  rw [h,one_smul]
  exact Quaternion.re_add_im q

theorem qPrincipalVector_one : qPrincipalVector (1:Q)=0 := by
  simp [qPrincipalVector,qAngle]

/-- Populate D/J's previous quantitative analytic-series slots using
the actual quaternion word, in the full continuous operator algebra.
Identifying the left-trivialized derivative with D, restricting to
the Lie carrier, and the selected CMP102 operator remain separate. -/
theorem qPath74_series_inverse (p : List Q) (e : ℝ) (he : 0≤e)
    (hp : ∀ q∈p,‖q‖=1 ∧ qAngle q≤e) (hL : p.length≤74)
    (hangle : 74*e≤Real.pi) (hsmall : 148*e≤1/2) :
    let D := dexpSeries (qAd (qPrincipalVector p.prod))
    ∃ J : Q →L[ℝ] Q,D*J=1 ∧ J*D=1 ∧
      ‖D-1‖≤148*e ∧ ‖J‖≤2 ∧ ‖J-1‖≤296*e := by
  exact dexpSeries_logInverse_enclosure _ e he
    (qPath74_ad_radius p e he hp hL hangle) hsmall

end
end CMP99Pivot.Path13
