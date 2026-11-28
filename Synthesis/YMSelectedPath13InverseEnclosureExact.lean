import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

/-! A quantitative, two-sided inverse enclosure for the actual selected
pivot once represented in a submultiplicative operator norm. The source
bound on its nonflat remainder is still a hypothesis, not a certificate. -/
namespace DASHI.YM.SelectedInverseEnclosure
noncomputable section
variable {R : Type*} [NormedRing R] [NormOneClass R] [HasSummableGeomSeries R]

theorem selected_inverse_ball (P₀ : Rˣ) (P : R) (M : ℝ)
    (hM : 0 < M) (hG : ‖(↑P₀⁻¹ : R)‖ ≤ M)
    (hP : ‖P-(P₀:R)‖ ≤ 1/(2*M)) :
    ∃ G : R, P*G=1 ∧ G*P=1 ∧ ‖G‖ ≤ 2*M ∧
      ‖G-(↑P₀⁻¹:R)‖ ≤ 2*M^2*‖P-(P₀:R)‖ := by
  let E := P-(P₀:R)
  let G₀ : R := ↑P₀⁻¹
  have hE : ‖E‖ ≤ 1/(2*M) := hP
  have hprod : ‖G₀‖*‖E‖ ≤ 1/2 := by
    calc
      _ ≤ M*(1/(2*M)) :=
        mul_le_mul hG hE (norm_nonneg _) hM.le
      _ = _ := by field_simp
  have hn : ‖-(G₀*E)‖ < 1 := by
    rw [norm_neg]
    exact lt_of_le_of_lt ((norm_mul_le _ _).trans hprod) (by norm_num)
  let U := Units.oneSub (-(G₀*E)) hn
  have hu : (↑U:R) = 1+G₀*E := by
    simp [U,Units.val_oneSub]
  have hbase : (P₀:R)*(↑U:R)=P := by
    rw [hu,mul_add,← mul_assoc]
    simp [G₀,E]
  let V := P₀*U
  have hv : (↑V:R)=P := hbase
  let G : R := ↑V⁻¹
  have hright : P*G=1 := by rw [← hv]; simp [G]
  have hleft : G*P=1 := by rw [← hv]; simp [G]
  have hid : G-G₀ = -(G₀*E*G) := by
    have h0 : G₀*(P₀:R)=1 := by simp [G₀]
    have h : G₀*E*G=G₀-G := by
      rw [E,mul_sub,sub_mul,mul_assoc,hright,mul_one,h0,one_mul]
    rw [h]
    abel
  have hd : ‖G-G₀‖ ≤ ‖G₀‖*‖E‖*‖G‖ := by
    rw [hid,norm_neg]
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have ht : ‖G‖ ≤ ‖G-G₀‖+‖G₀‖ := by
    simpa only [sub_add_cancel] using norm_add_le (G-G₀) G₀
  have hh := mul_le_mul_of_nonneg_right hprod (norm_nonneg G)
  have hbound : ‖G‖ ≤ 2*M := by linarith
  refine ⟨G,hright,hleft,hbound,?_⟩
  calc
    _ ≤ ‖G₀‖*‖E‖*‖G‖ := hd
    _ ≤ M*‖E‖*(2*M) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hG (norm_nonneg _))
        hbound (norm_nonneg _) (mul_nonneg hM.le (norm_nonneg _))
    _ = _ := by ring

/-- Source-shaped radius for the Path13 flat inverse norm 28561. -/
theorem path13_inverse_ball (P₀ : Rˣ) (P : R)
    (hG : ‖(↑P₀⁻¹:R)‖ ≤ 28561)
    (hP : ‖P-(P₀:R)‖ ≤ 1/57122) :
    ∃ G : R, P*G=1 ∧ G*P=1 ∧ ‖G‖ ≤ 57122 ∧
      ‖G-(↑P₀⁻¹:R)‖ ≤ 1631461442*‖P-(P₀:R)‖ := by
  simpa only [show (2:ℝ)*28561=57122 by norm_num,
    show (2:ℝ)*28561^2=1631461442 by norm_num] using
    selected_inverse_ball P₀ P 28561 (by norm_num) hG (by norm_num at *; exact hP)

end
end DASHI.YM.SelectedInverseEnclosure
