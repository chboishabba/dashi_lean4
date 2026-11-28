import Synthesis.MillenniumBSDShorKummerFibreExact

/-! Actual Mathlib affine point group on the original split cubic.
The earlier reverse-half coordinate flip now equals translation by
the actual root point (e0,0), with the nonsingularity witnesses derived
from W.IsElliptic. The same theorem is valid for every choice of the
distinguished root by reindexing e0,e1,e2. -/
namespace DASHI.BSD.SplitTangent
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [CharZero F]
variable (W : WeierstrassCurve F) [W.IsElliptic]
variable (e0 e1 e2 : F)

structure SplitCoefficients : Prop where
  a1_zero : W.a₁=0
  a3_zero : W.a₃=0
  a2_eq : W.a₂= -(e0+e1+e2)
  a4_eq : W.a₄=e0*e1+e1*e2+e2*e0
  a6_eq : W.a₆= -(e0*e1*e2)

theorem split_nonsingular (h : SplitCoefficients W e0 e1 e2)
    (X Y : F) (hcurve : Y^2=(X-e0)*(X-e1)*(X-e2)) :
    W.toAffine.Nonsingular X Y := by
  apply W.equation_iff_nonsingular.mp
  apply (W.toAffine.equation_iff X Y).mpr
  change Y^2+W.a₁*X*Y+W.a₃*Y=X^3+W.a₂*X^2+W.a₄*X+W.a₆
  rw [h.a1_zero,h.a3_zero,h.a2_eq,h.a4_eq,h.a6_eq]
  linear_combination hcurve

def splitRootPoint (h : SplitCoefficients W e0 e1 e2) : W.toAffine.Point :=
  .some (split_nonsingular W e0 e1 e2 h e0 0 (by ring))

theorem splitRootPoint_two (h : SplitCoefficients W e0 e1 e2) :
    (2:ℕ) • splitRootPoint W e0 e1 e2 h=0 := by
  classical
  rw [two_nsmul]
  unfold splitRootPoint
  apply WeierstrassCurve.Affine.Point.add_of_Y_eq rfl
  change (0:F)= -0-W.a₁*e0-W.a₃
  rw [h.a1_zero,h.a3_zero]
  ring

theorem splitRoot_add_coordinates (h : SplitCoefficients W e0 e1 e2)
    (X Y : F) (hu : X-e0≠0)
    (hc : Y^2=(X-e0)*(X-e1)*(X-e2)) :
    let m := W.toAffine.slope X e0 Y 0
    W.toAffine.addX X e0 m=e0+torsionU (e0-e1) (e0-e2) (X-e0) ∧
    W.toAffine.addY X e0 Y m=torsionV (e0-e1) (e0-e2) (X-e0) Y := by
  classical
  have hm : W.toAffine.slope X e0 Y 0=Y/(X-e0) := by
    rw [W.toAffine.slope_of_X_ne (sub_ne_zero.mp hu),sub_zero]
  dsimp
  rw [hm]
  have hmsq : (Y/(X-e0))^2=(X-e1)*(X-e2)/(X-e0) := by
    rw [div_pow,hc]
    field_simp [hu] <;> ring
  have hx : W.toAffine.addX X e0 (Y/(X-e0))=
      e0+torsionU (e0-e1) (e0-e2) (X-e0) := by
    unfold WeierstrassCurve.Affine.addX torsionU
    change (Y/(X-e0))^2+W.a₁*(Y/(X-e0))-W.a₂-X-e0=_
    rw [hmsq,h.a1_zero,h.a2_eq]
    field_simp [hu] <;> ring
  refine ⟨hx,?_⟩
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negY
    WeierstrassCurve.Affine.negAddY torsionV
  rw [hx]
  change -(Y/(X-e0)*(e0+torsionU (e0-e1) (e0-e2) (X-e0)-X)+Y)-
    W.a₁*(e0+torsionU (e0-e1) (e0-e2) (X-e0))-W.a₃=_
  rw [h.a1_zero,h.a3_zero]
  unfold torsionU
  field_simp [hu] <;> ring

def reverseHalfPoint (h : SplitCoefficients W e0 e1 e2)
    (x r s t : F) (hr : r^2=x-e0) (hs : s^2=x-e1) (ht : t^2=x-e2) :
    W.toAffine.Point :=
  .some (split_nonsingular W e0 e1 e2 h _ _
    (reverseHalf_curve x r s t e0 e1 e2 hr hs ht))

/-- Actual point-level even sign action. The proof uses Mathlib's
secant addition, not a separately declared group law on sign rows. -/
theorem reverseHalf_evenFlip_actual_add (h : SplitCoefficients W e0 e1 e2)
    (x r s t : F) (hr : r^2=x-e0) (hs : s^2=x-e1) (ht : t^2=x-e2)
    (h01 : e0≠e1) (h02 : e0≠e2) :
    reverseHalfPoint W e0 e1 e2 h x r (-s) (-t) hr
      (by simpa using hs) (by simpa using ht) =
    reverseHalfPoint W e0 e1 e2 h x r s t hr hs ht+
      splitRootPoint W e0 e1 e2 h := by
  classical
  have hfac := (reverseHalf_factors x r s t e0 e1 e2 hr hs ht).1
  have hrs := reverseHalf_pair_nonzero r s e0 e1 x hr hs h01
  have hrt := reverseHalf_pair_nonzero r t e0 e2 x hr ht h02
  have hu : reverseHalfX x r s t-e0≠0 := by
    rw [hfac]
    exact mul_ne_zero hrs hrt
  obtain ⟨hx,hy⟩ := splitRoot_add_coordinates W e0 e1 e2 h
    (reverseHalfX x r s t) (reverseHalfY r s t) hu
    (reverseHalf_curve x r s t e0 e1 e2 hr hs ht)
  obtain ⟨hfx,hfy⟩ := reverseHalf_evenFlip_torsion x r s t e0 e1 e2 hr hs ht h01 h02
  unfold reverseHalfPoint splitRootPoint
  rw [WeierstrassCurve.Affine.Point.add_some (fun h=>hu (sub_eq_zero.mpr h.1))]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨by rw [hx]; linear_combination hfx,by rw [hy,hfy]⟩

end
end DASHI.BSD.SplitTangent
