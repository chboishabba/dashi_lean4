import Synthesis.YMCMP99Path13SignedWordNormExact

/-!
CMP98 Path13 source Eq119/120 nonflat selected row budget, using the
actual 13^4 offset average, 24+13 word lengths and the signed
correction. The D/J log/exp operator bounds below must still be
realized on the original common CMP102 source ball.
-/
namespace CMP99Pivot.Path13
open scoped BigOperators
noncomputable section
variable {R : Type*} [NormedRing R] [NormOneClass R] [NormedAlgebra ℝ R]

abbrev Offset := Fin (13^4)
def pathMean (f : Offset → R) : R := (1/(28561:ℝ)) • ∑ i,f i

theorem pathMean_bound (f : Offset → R) (B : ℝ)
    (h : ∀ i,‖f i‖≤B) : ‖pathMean f‖≤B := by
  unfold pathMean
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : 0≤(1/(28561:ℝ)))]
  calc
    _ ≤ (1/(28561:ℝ)) * ∑ i,‖f i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
    _ ≤ (1/(28561:ℝ)) * ∑ _ : Offset,B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _=>h i) (by norm_num)
    _ = B := by simp [Offset] <;> ring

theorem pathMean_sub (f g : Offset → R) :
    pathMean f-pathMean g=pathMean (fun i=>f i-g i) := by
  simp [pathMean,Finset.sum_sub_distrib,smul_sub]

def relativeTangent (M P Rot : Offset → R) : Offset → R :=
  fun i=>M i-Rot i*P i

def sourceRow (D : R) (J Rot M P : Offset → R)
    (A C rc : R) (plus minus : Offset → R) : R :=
  (1/(13:ℝ)) •
    (D*pathMean (fun i=>J i*relativeTangent M P Rot i)+
      A*rc+pathMean (fun i=>C*plus i-minus i))

def flatRow (M P : Offset → R) (rc : R) (plus minus : Offset → R) : R :=
  (1/(13:ℝ)) •
    (pathMean (fun i=>M i-P i)+rc+pathMean (fun i=>plus i-minus i))

/-- Full literal source-row estimate, not a separately assigned
Jacobian. M/P are left-trivialized derivatives of the two 37-link
words, R their relative adjoint, J inverse log differential and D
the outer exponential differential. A,C are the outer and center
adjoints. Flat terms have precisely the same signed paths. -/
theorem sourceRow_nonflat_bound
    (e : ℝ) (he : 0≤e)
    (D : R) (J Rot M P M₀ P₀ : Offset → R)
    (A C rc rc₀ : R) (plus minus plus₀ minus₀ : Offset → R)
    (hD : ‖D-1‖≤148*e)
    (hJ : ∀ i,‖J i‖≤2 ∧ ‖J i-1‖≤296*e)
    (hRot : ∀ i,‖Rot i‖≤1 ∧ ‖Rot i-1‖≤148*e)
    (hM : ∀ i,‖M i‖≤37 ∧ ‖M i-M₀ i‖≤2738*e)
    (hP : ∀ i,‖P i‖≤37 ∧ ‖P i-P₀ i‖≤2738*e)
    (hA : ‖A-1‖≤296*e) (hC : ‖C-1‖≤26*e)
    (hc : ‖rc‖≤13 ∧ ‖rc-rc₀‖≤338*e)
    (hp : ∀ i,‖plus i‖≤24 ∧ ‖plus i-plus₀ i‖≤1152*e)
    (hm : ∀ i,‖minus i-minus₀ i‖≤1152*e) :
    ‖sourceRow D J Rot M P A C rc plus minus-
      flatRow M₀ P₀ rc₀ plus₀ minus₀‖≤(61874/13)*e := by
  let T := relativeTangent M P Rot
  let T₀ : Offset → R := fun i=>M₀ i-P₀ i
  have hT (i : Offset) : ‖T i‖≤74 := by
    unfold T relativeTangent
    calc
      _ ≤ ‖M i‖+‖Rot i*P i‖ := norm_sub_le _ _
      _ ≤ 74 := by
        have h := (norm_mul_le (Rot i) (P i)).trans
          (mul_le_mul (hRot i).1 (hP i).1 (norm_nonneg _) (by norm_num))
        linarith [(hM i).1]
  have hPd (i : Offset) : ‖Rot i*P i-P₀ i‖≤8214*e := by
    have h := norm_mul_change (Rot i) (P i) (P₀ i)
    have h' := mul_le_mul (hRot i).2 (hP i).1 (norm_nonneg _) (by positivity : 0≤148*e)
    linarith [(hP i).2]
  have hTd (i : Offset) : ‖T i-T₀ i‖≤10952*e := by
    have hd : T i-T₀ i=(M i-M₀ i)-(Rot i*P i-P₀ i) := by
      unfold T T₀ relativeTangent
      abel
    rw [hd]
    exact (norm_sub_le _ _).trans (by linarith [(hM i).2,hPd i])
  let U := pathMean (fun i=>J i*T i)
  let U₀ := pathMean T₀
  have hU : ‖U‖≤148 := by
    apply pathMean_bound
    intro i
    exact (norm_mul_le _ _).trans
      (by have h := mul_le_mul (hJ i).1 (hT i) (norm_nonneg _) (by norm_num : 0≤(2:ℝ))
          norm_num at h
          exact h)
  have hUd : ‖U-U₀‖≤32856*e := by
    dsimp [U,U₀]
    rw [pathMean_sub]
    apply pathMean_bound
    intro i
    have h := norm_mul_change (J i) (T i) (T₀ i)
    have h' := mul_le_mul (hJ i).2 (hT i) (norm_nonneg _) (by positivity : 0≤296*e)
    linarith [hTd i]
  have hOuter : ‖D*U-U₀‖≤54760*e := by
    have h := norm_mul_change D U U₀
    have h' := mul_le_mul hD hU (norm_nonneg _) (by positivity : 0≤148*e)
    linarith
  have hCenter : ‖A*rc-rc₀‖≤4186*e := by
    have h := norm_mul_change A rc rc₀
    have h' := mul_le_mul hA hc.1 (norm_nonneg _) (by positivity : 0≤296*e)
    linarith [hc.2]
  let W := pathMean (fun i=>C*plus i-minus i)
  let W₀ := pathMean (fun i=>plus₀ i-minus₀ i)
  have hW : ‖W-W₀‖≤2928*e := by
    dsimp [W,W₀]
    rw [pathMean_sub]
    apply pathMean_bound
    intro i
    have h := norm_mul_change C (plus i) (plus₀ i)
    have h' := mul_le_mul hC (hp i).1 (norm_nonneg _) (by positivity : 0≤26*e)
    have hs : ‖C*plus i-plus₀ i‖≤1776*e := by linarith [(hp i).2]
    have hd : C*plus i-minus i-(plus₀ i-minus₀ i)=
        (C*plus i-plus₀ i)-(minus i-minus₀ i) := by abel
    rw [hd]
    exact (norm_sub_le _ _).trans (by linarith [hm i])
  change ‖(1/(13:ℝ)) • (D*U+A*rc+W)-
      (1/(13:ℝ)) • (U₀+rc₀+W₀)‖≤_
  rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : 0≤(1/(13:ℝ)))]
  have h : D*U+A*rc+W-(U₀+rc₀+W₀)=(D*U-U₀)+(A*rc-rc₀)+(W-W₀) := by abel
  rw [h]
  have h' := (norm_add_le ((D*U-U₀)+(A*rc-rc₀)) (W-W₀)).trans
    (add_le_add_right (norm_add_le _ _) _)
  linarith

/-- Four input-direction blocks in a block row give a conservative
20000-e bound in a row-sum norm. This scalar threshold is sufficient
for the prior 12-coordinate selected inverse lemma. -/
theorem selected_radius_payment (e p : ℝ) (he : 0≤e)
    (hp : p≤4*(61874/13)*e) (hsmall : e≤1/1142440000) :
    p≤1/57122 := by
  have h : 4*(61874/13:ℝ)≤20000 := by norm_num
  have h' := mul_le_mul_of_nonneg_right h he
  linarith

end
end CMP99Pivot.Path13
