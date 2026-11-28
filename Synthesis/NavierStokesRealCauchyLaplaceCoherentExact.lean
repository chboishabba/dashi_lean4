import Synthesis.NavierStokesRealCauchyTraceFTCExact
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
R490/R491 actual scalar Laplace realization and coherent finite Cauchy
positivity on the ORIGINAL R291 factor-two normalization. Signed
off-diagonal terms remain present. The centered difference need not be
positive: it is the difference of two nonnegative coherent forms.
Classical Laplace/Gram identity, DASHI attachment to the finite trace.
-/
namespace DASHI.NavierStokes.RealCauchyTrace
open MeasureTheory
noncomputable section
open scoped BigOperators

variable {I : Type*} [Fintype I]

def heatFold (r : I → ℝ) (m : I → Coord → ℝ → ℝ)
    (t s : ℝ) (c : Coord) : ℝ :=
  ∑ i, Real.exp (-r i*s)*m i c t

def heatGram (r : I → ℝ) (m : I → Coord → ℝ → ℝ) (t s : ℝ) :=
  ∑ c : Coord, (heatFold r m t s c)^2

theorem heatGram_nonnegative (r : I → ℝ) (m : I → Coord → ℝ → ℝ)
    (t s : ℝ) : 0 ≤ heatGram r m t s :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem heatGram_expand (r : I → ℝ) (m : I → Coord → ℝ → ℝ) (t s : ℝ) :
    heatGram r m t s =
      ∑ p : PairCoord I,
        Real.exp (-(r p.1.1+r p.1.2)*s)*cellProduct m p t := by
  classical
  unfold heatGram heatFold cellProduct
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Fintype.sum_prod_type,pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show -(r i+r j)*s = -r i*s + -r j*s by ring,Real.exp_add]
  ring

/-- The actual standard analytic authority missing from R490:
positive-rate exponential has its literal inverse as integral. -/
theorem scalar_laplace_inverse (a : ℝ) (ha : 0 < a) :
    (∫ s : ℝ in Set.Ioi 0, Real.exp (-a*s))=1/a := by
  rw [integral_exp_mul_Ioi (neg_neg_of_pos ha)]
  simp
  ring

theorem heatGram_integrable (r : I → ℝ) (m : I → Coord → ℝ → ℝ)
    (hr : ∀ i,0 < r i) (t : ℝ) :
    IntegrableOn (heatGram r m t) (Set.Ioi 0) := by
  have he : heatGram r m t = fun s => ∑ p : PairCoord I,
      Real.exp (-(r p.1.1+r p.1.2)*s)*cellProduct m p t :=
    funext fun s => heatGram_expand r m t s
  rw [he]
  apply integrable_finset_sum
  intro p _
  exact (integrableOn_exp_mul_Ioi
    (neg_neg_of_pos (add_pos (hr _) (hr _))) 0).mul_const _

/-- The signed ordered-pair trace is literally twice the integrated
square of the same coherent heat fold. No pairwise absolute values. -/
theorem Q_eq_heatGram_integral (r : I → ℝ) (m : I → Coord → ℝ → ℝ)
    (hr : ∀ i,0 < r i) (t : ℝ) :
    Q r m t=2*(∫ s : ℝ in Set.Ioi 0,heatGram r m t s) := by
  classical
  simp_rw [heatGram_expand]
  rw [integral_finset_sum Finset.univ (fun p _ =>
    (integrableOn_exp_mul_Ioi
      (neg_neg_of_pos (add_pos (hr p.1.1) (hr p.1.2))) 0).mul_const
        (cellProduct m p t)),Finset.mul_sum]
  unfold Q
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_mul_const,scalar_laplace_inverse _ (add_pos (hr _) (hr _))]
  unfold cauchyPair
  ring

theorem Q_nonnegative (r : I → ℝ) (m : I → Coord → ℝ → ℝ)
    (hr : ∀ i,0 < r i) (t : ℝ) : 0 ≤ Q r m t := by
  rw [Q_eq_heatGram_integral r m hr t]
  exact mul_nonneg (by norm_num)
    (integral_nonneg (heatGram_nonnegative r m t))

/-- Original centered resolvent as coherent output form minus the
positive Cauchy form. The cancellation is signed, not absolute. -/
def centeredTrace (a : ℝ) (r : I → ℝ)
    (m : I → Coord → ℝ → ℝ) (t : ℝ) :=
  ∑ p : PairCoord I,
    (1/a-1/(r p.1.1+r p.1.2)) * (2*cellProduct m p t)

theorem centeredTrace_eq (a : ℝ) (r : I → ℝ)
    (m : I → Coord → ℝ → ℝ) (t : ℝ) :
    centeredTrace a r m t = 2/a*H m t-Q r m t := by
  classical
  unfold centeredTrace H Q cauchyPair
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem centeredTrace_signed_upper (a : ℝ) (r : I → ℝ)
    (m : I → Coord → ℝ → ℝ) (hr : ∀ i,0 < r i) (t : ℝ) :
    centeredTrace a r m t ≤ 2/a*H m t := by
  rw [centeredTrace_eq]
  linarith [Q_nonnegative r m hr t]

/-- At a coherent zero, every remaining centered contribution is
nonpositive, regardless of individual pair signs. -/
theorem centeredTrace_coherent_zero (a : ℝ) (r : I → ℝ)
    (m : I → Coord → ℝ → ℝ) (hr : ∀ i,0 < r i) (t : ℝ)
    (h : H m t=0) : centeredTrace a r m t ≤ 0 := by
  simpa [h] using centeredTrace_signed_upper a r m hr t

end
end DASHI.NavierStokes.RealCauchyTrace
