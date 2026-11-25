import Integration.Paper9SymmetricTauJet

/-! SOURCE-WRITTEN, UNCOMPILED. Reuse original arbitrary-y sliceSectorConsumer,
JZero, descended cyclic norm and normalized columns. Only triangular existence
is added; no bivariate coefficient table or new analytic carrier. -/
namespace Integration.Paper9UniversalMonicSlice
open Complex Polynomial UpperHalfPlane
open scoped BigOperators
open Integration.Paper9DiscriminantUnitReflection
open Integration.Paper9HeckeProductAssembly
open Integration.Paper9CyclotomicPacketReflection
open Integration.Paper9SymmetricTauJet
open Integration.Paper9Hecke41ChartGeometry

noncomputable section
local notation "j" => Integration.MoonshineEisensteinAgdaTarget.jTarget

theorem jPolyZero (m : ℕ) : (jPoly m).coeff 0=1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero,jPolyEval]
  unfold Integration.Paper9HeckeFiniteRemainder.truncJ
  rw [Finset.sum_eq_single 0]
  · simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using JZero
  · intro b hb hne
    simp [zero_pow hne]
  · simp

def pivot (A : Polynomial ℂ) (d n k : ℕ) : ℂ :=
  if k≤n then (A^(d-k)).coeff (n-k) else 0

theorem columnQCoeff (m d n : ℕ) (c : ℕ → ℂ) (hn : n≤d) :
    (columnQ m d c).coeff n =
      ∑ k ∈ Finset.range (n+1), c k*pivot (jPoly m) d n k := by
  unfold columnQ
  rw [Polynomial.finset_sum_coeff]
  simp only [mul_assoc,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow_mul',pivot]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hkn
  have h : ¬ k≤n := by simpa using hkn
  simp [h]

theorem pivotOne (A : Polynomial ℂ) (hA : A.coeff 0=1) (d n : ℕ) :
    pivot A d n n=1 := by
  simp [pivot,Polynomial.coeff_zero_eq_eval_zero,
    ← Polynomial.coeff_zero_eq_eval_zero A,hA]

-- Finite extension of an already paid prefix. The new coordinate has
-- a unit pivot and has no effect on any earlier row.
theorem triangularExist (A : Polynomial ℂ) (hA : A.coeff 0=1)
    (d : ℕ) (B : ℕ → ℂ) (n : ℕ) :
    ∃ c : ℕ → ℂ, ∀ i≤n,
      (∑ k ∈ Finset.range (i+1), c k*pivot A d i k)=B i := by
  classical
  induction n with
  | zero =>
    refine ⟨fun _ => B 0,?_⟩
    intro i hi
    have he : i=0 := by omega
    subst i
    simp [pivotOne A hA]
  | succ n ih =>
    obtain ⟨c,hc⟩ := ih
    let z := B (n+1)-∑ k ∈ Finset.range (n+1), c k*pivot A d (n+1) k
    let e : ℕ → ℂ := fun k => if k=n+1 then z else c k
    refine ⟨e,?_⟩
    intro i hi
    by_cases he : i=n+1
    · subst i
      rw [Finset.sum_range_succ,pivotOne A hA]
      have hs : (∑ k ∈ Finset.range (n+1), e k*pivot A d (n+1) k)=
          ∑ k ∈ Finset.range (n+1), c k*pivot A d (n+1) k := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        simp [e,show k≠n+1 by omega]
      rw [hs]
      simp [e,z]
    · rw [← hc i (by omega)]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      simp [e,show k≠n+1 by omega]

def target (y : ℂ) : Polynomial ℂ :=
  sliceInfinityQ 1722 y*Polynomial.contract 41 (cyclicNorm (sliceH 1722 y))

theorem targetZero (y : ℂ) : (target y).coeff 0=1 := by
  have hs : (sliceH 1722 y).coeff 0=1 := by
    simp [sliceH,jPolyZero,Polynomial.coeff_C_mul_X]
  have hg : (sliceInfinityQ 1722 y).coeff 0=1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [sliceInfinityQ,qPoly,Polynomial.eval_comp,
      ← Polynomial.coeff_zero_eq_eval_zero (jPoly 1722),jPolyZero]
  have hn := Integration.Paper9IntegerSectorWeld.normZero _ hs
  rw [target,Polynomial.coeff_zero_eq_eval_zero,Polynomial.eval_mul,
    ← Polynomial.coeff_zero_eq_eval_zero,← Polynomial.coeff_zero_eq_eval_zero]
  rw [hg,hn,mul_one]

theorem existsSliceCoefficients (y : ℂ) :
    ∃ c : ℕ → ℂ, ∀ n≤42,
      (target y-columnQ 1722 42 c).coeff n=0 := by
  obtain ⟨c,hc⟩ := triangularExist (jPoly 1722) (jPolyZero 1722) 42 (target y).coeff 42
  refine ⟨c,?_⟩
  intro n hn
  rw [Polynomial.coeff_sub,columnQCoeff _ _ _ _ hn,hc n hn,sub_self]

def sliceC (y : ℂ) : ℕ → ℂ := Classical.choose (existsSliceCoefficients y)

theorem sliceResidual (y : ℂ) (n : ℕ) (hn : n≤42) :
    (target y-columnQ 1722 42 (sliceC y)).coeff n=0 :=
  Classical.choose_spec (existsSliceCoefficients y) n hn

theorem sliceCZero (y : ℂ) : sliceC y 0=1 := by
  have h := sliceResidual y 0 (by omega)
  rw [Polynomial.coeff_sub,targetZero,columnQCoeff _ _ _ _ (by omega)] at h
  simpa [pivotOne _ (jPolyZero 1722),sub_eq_zero,eq_comm] using h

def universalSlice (y : ℂ) : Polynomial ℂ := packet 42 (sliceC y)

theorem universalSliceEval (y : ℂ) (τ : ℍ) :
    (universalSlice y).eval (j τ)=actualProduct τ y := by
  symm
  exact sliceSectorConsumer y (sliceC y) (sliceResidual y) τ

theorem universalSliceDegree (y : ℂ) : (universalSlice y).natDegree≤42 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  unfold universalSlice packet
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  simp [Polynomial.coeff_C_mul_X_pow,show n≠42-k by omega,
    show 42-k≠n by omega]

theorem universalSliceLead (y : ℂ) : (universalSlice y).coeff 42=1 := by
  unfold universalSlice packet
  rw [Polynomial.finset_sum_coeff,Finset.sum_eq_single 0]
  · simp [Polynomial.coeff_C_mul_X_pow,sliceCZero]
  · intro k hk hne
    simp [Polynomial.coeff_C_mul_X_pow,show 42≠42-k by omega,
      show 42-k≠42 by omega]
  · simp

theorem symmetryFromSeparatedImage
    (hinf : Set.Infinite {x : ℂ | ∃ τ : ℍ,
      x=j τ ∧ Function.Injective (fun i : Chart => chartValue i τ)}) :
    ∀ τ σ : ℍ, actualProduct τ (j σ)=actualProduct σ (j τ) :=
  actualTwoPointSymmetry universalSlice universalSliceEval universalSliceDegree
    universalSliceLead hinf

end
end Integration.Paper9UniversalMonicSlice
