import Synthesis.MillenniumHodgeDicksonActualAffineBaseExact
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Localization.Away.Basic

/-! Actual punctured point of the previous universal coupled algebra.
This proves the open-chart localization is nontrivial, not that its
projective closure is the required primitive algebraic cycle.
The point has a=1, v=2, x=5/2, y=128 and discriminant -16113/16.
-/
namespace DASHI.Hodge.DicksonCoupled
open scoped BigOperators
noncomputable section

variable {F : Type*} [Field F] [CharZero F]

def surfaceSample (d : F) : SurfaceCoord → F
  | .a _ => 1
  | .x _ => 5/2
  | .s _ => (1-d)/4
  | .eta => 2^6
  | .delta => d^6

def sampleEval (d : F) : SurfacePoly →+* F :=
  MvPolynomial.eval₂Hom (algebraMap ℚ F) (surfaceSample d)

theorem sampleEval_surface (d : F) (hd : d^2= -16113/16) (i : Address) :
    sampleEval d (surfaceRelation i)=0 := by
  simp [sampleEval,surfaceRelation,surfaceA,surfaceX,surfaceS,surfaceSample,
    map_sub,map_add,map_mul,map_pow]
  linear_combination (1/8 : F)*hd

theorem sampleEval_derivative (d : F) (i : Address) :
    sampleEval d (surfaceDerivative i)=d := by
  simp [sampleEval,surfaceDerivative,surfaceA,surfaceS,surfaceSample]
  ring

theorem sampleEval_kills (d : F) (hd : d^2= -16113/16) :
    ∀ p∈coupledSurfaceIdeal,sampleEval d p=0 := by
  have h : coupledSurfaceIdeal ≤ RingHom.ker (sampleEval d) := by
    apply Ideal.span_le.mpr
    rintro p (⟨i,rfl⟩|hp)
    · exact sampleEval_surface d hd i
    · rw [Set.mem_singleton_iff] at hp
      subst p
      change sampleEval d ((∏ i : Address,surfaceDerivative i)-MvPolynomial.X .delta)=0
      rw [map_sub,map_prod]
      simp [sampleEval_derivative,sampleEval,surfaceSample,Address]
  intro p hp
  exact h hp

def baseSample (d : F) (hd : d^2= -16113/16) : CoupledSurfaceBase →+* F :=
  Ideal.Quotient.lift _ (sampleEval d) (sampleEval_kills d hd)

theorem baseSample_A (d : F) (hd : d^2= -16113/16) (i : Address) :
    baseSample d hd (baseA i)=1 := by
  simp [baseSample,baseA,sampleEval,surfaceA,surfaceSample]

theorem baseSample_X (d : F) (hd : d^2= -16113/16) (i : Address) :
    baseSample d hd (baseX i)=5/2 := by
  simp [baseSample,baseX,sampleEval,surfaceX,surfaceSample]

theorem baseSample_eta (d : F) (hd : d^2= -16113/16) :
    baseSample d hd baseEta=2^6 := by
  simp [baseSample,baseEta,sampleEval,surfaceSample]

theorem baseSample_delta (d : F) (hd : d^2= -16113/16) :
    baseSample d hd baseDelta=d^6 := by
  simp [baseSample,baseDelta,sampleEval,surfaceSample]

def foldedSampleEval (d : F) (hd : d^2= -16113/16) :
    MvPolynomial Address CoupledSurfaceBase →+* F :=
  MvPolynomial.eval₂Hom (baseSample d hd) (fun _=>2)

theorem foldedSample_kills (d : F) (hd : d^2= -16113/16) :
    ∀ p∈coupledFoldIdeal baseA baseX baseEta,foldedSampleEval d hd p=0 := by
  have h : coupledFoldIdeal baseA baseX baseEta ≤ RingHom.ker (foldedSampleEval d hd) := by
    apply Ideal.span_le.mpr
    rintro p (⟨i,rfl⟩|hp)
    · change foldedSampleEval d hd (foldRelation baseA baseX i)=0
      simp [foldedSampleEval,foldRelation,baseSample_A,baseSample_X]
      norm_num
    · rw [Set.mem_singleton_iff] at hp
      subst p
      change foldedSampleEval d hd ((∏ i : Address,MvPolynomial.X i)-MvPolynomial.C baseEta)=0
      simp [foldedSampleEval,baseSample_eta,Address]
  intro p hp
  exact h hp

def actualFoldSample (d : F) (hd : d^2= -16113/16) : ActualCoupledFoldAlgebra →+* F :=
  Ideal.Quotient.lift _ (foldedSampleEval d hd) (foldedSample_kills d hd)

def chartDenominator : ActualCoupledFoldAlgebra :=
  let R := CoupledSurfaceBase
  let A := ActualCoupledFoldAlgebra
  let v := foldCoord baseA baseX baseEta
  (algebraMap R A baseEta)*(algebraMap R A baseDelta)*
    ∏ i : Address,(algebraMap R A (baseA i))*v i*
      ((v i)^2-algebraMap R A (baseA i))

theorem actualFoldSample_denominator (d : F) (hd : d^2= -16113/16) :
    actualFoldSample d hd chartDenominator≠0 := by
  have hn : d≠0 := by intro hz; rw [hz] at hd; norm_num at hd
  simp [chartDenominator,actualFoldSample,foldedSampleEval,foldCoord,
    Ideal.Quotient.algebraMap_eq,baseSample_A,baseSample_eta,baseSample_delta,Address]
  all_goals simp [mul_ne_zero,hn] <;> norm_num

/-- The actual principal open is nonempty in the algebraically closed
extension: the universal localized ring maps into a nontrivial field. -/
theorem actual_punctured_chart_inhabited [IsAlgClosed F] :
    Nonempty (Localization.Away chartDenominator →+* F) := by
  obtain ⟨d,hd⟩ := IsAlgClosed.exists_pow_nat_eq (-16113/16:F) (by decide : 0<2)
  exact ⟨IsLocalization.Away.lift chartDenominator
    (g:=actualFoldSample d hd) (isUnit_iff_ne_zero.mpr (actualFoldSample_denominator d hd))⟩

end
end DASHI.Hodge.DicksonCoupled
