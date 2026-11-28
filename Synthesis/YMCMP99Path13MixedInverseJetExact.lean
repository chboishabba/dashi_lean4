import Synthesis.YMCMP99Path13ActualPivotBlockExact

/-!
Path13 original full Q coefficients at orders 1,s,t,st.
Work in the square-zero bivariate jet (s²=t²=0). Both orders of
noncommuting mixed terms must be retained. No identification of
a finite jet with a uniform nonflat inverse on the CMP102 ball.
-/
namespace CMP99Pivot.Path13
open Matrix
noncomputable section

abbrev Pivot := Matrix Row Row ℝ

def invS (G Ps : Pivot) := -(G*Ps*G)
def invST (G Ps Pt Pst : Pivot) :=
  G*Ps*G*Pt*G+G*Pt*G*Ps*G-G*Pst*G

theorem inverse_s_left (P G Ps : Pivot) (h : G*P=1) :
    G*Ps+invS G Ps*P=0 := by
  unfold invS
  rw [neg_mul,Matrix.mul_assoc (G*Ps) G P,h,mul_one,add_neg_cancel]

theorem inverse_s_right (P G Ps : Pivot) (h : P*G=1) :
    P*invS G Ps+Ps*G=0 := by
  unfold invS
  rw [mul_neg,← Matrix.mul_assoc P (G*Ps) G,
    ← Matrix.mul_assoc P G Ps,h,one_mul,neg_add_cancel]

theorem inverse_st_left (P G Ps Pt Pst : Pivot) (h : G*P=1) :
    G*Pst+invS G Ps*Pt+invS G Pt*Ps+invST G Ps Pt Pst*P=0 := by
  unfold invST invS
  simp only [Matrix.add_mul,Matrix.sub_mul,neg_mul]
  simp only [Matrix.mul_assoc,h,mul_one]
  abel

theorem inverse_st_right (P G Ps Pt Pst : Pivot) (h : P*G=1) :
    P*invST G Ps Pt Pst+Ps*invS G Pt+Pt*invS G Ps+Pst*G=0 := by
  unfold invST invS
  simp only [Matrix.mul_add,Matrix.mul_sub,mul_neg]
  simp only [← Matrix.mul_assoc,h,one_mul]
  abel

abbrev Free := {s : Site // s≠0} × Row
abbrev FreeBlock := Matrix Row Free ℝ
abbrev FreeVector := Matrix Free (Fin 1) ℝ

/-- Literal source mixed derivative of c=-P⁻¹Bb. All Q(s,t) jets
are taken from the same source and b is fixed. -/
def eliminatedST (G Ps Pt Pst : Pivot)
    (B Bs Bt Bst : FreeBlock) (b : FreeVector) :=
  -(invST G Ps Pt Pst*(B*b)+invS G Ps*(Bt*b)+
    invS G Pt*(Bs*b)+G*(Bst*b))

theorem eliminatedST_expanded (G Ps Pt Pst : Pivot)
    (B Bs Bt Bst : FreeBlock) (b : FreeVector) :
    eliminatedST G Ps Pt Pst B Bs Bt Bst b =
      G*Pst*G*(B*b)-G*Ps*G*Pt*G*(B*b)-G*Pt*G*Ps*G*(B*b)+
      G*Ps*G*(Bt*b)+G*Pt*G*(Bs*b)-G*(Bst*b) := by
  unfold eliminatedST invST invS
  simp only [Matrix.add_mul,Matrix.sub_mul,neg_mul]
  abel

/-- For the literal Path13 flat pivot, there is no independent
choice of inverse jet normalization. -/
theorem origin_inverse_st_left (Ps Pt Pst : Pivot) :
    originPivotInv*Pst+invS originPivotInv Ps*Pt+
      invS originPivotInv Pt*Ps+
      invST originPivotInv Ps Pt Pst*pivot originQ=0 :=
  inverse_st_left _ _ _ _ _ originPivotInverse.1

theorem origin_inverse_st_right (Ps Pt Pst : Pivot) :
    pivot originQ*invST originPivotInv Ps Pt Pst+
      Ps*invS originPivotInv Pt+Pt*invS originPivotInv Ps+
      Pst*originPivotInv=0 :=
  inverse_st_right _ _ _ _ _ originPivotInverse.2

end
end CMP99Pivot.Path13
