import Integration.Paper9ScalarCross

/-! SOURCE-WRITTEN, UNCOMPILED. Pointwise actual-source cross identity
and zero-mode identification. No division by the centered j value,
no distinctness of the remaining forty roots. Local analytic disk
normalization remains separate. -/
namespace Integration.Paper9ActualCross
open Complex Filter Polynomial UpperHalfPlane
open scoped BigOperators Topology
open Integration.Paper9CM163LiteralPacket
open Integration.Paper9HeckeProductAssembly
open Integration.Paper9ActualCMRoot
open Integration.Paper9ExecutableCM163
open Integration.Paper9ActualCMPoint
open Integration.Paper9ActualJSourceJet
open Integration.Paper9Hecke41ChartGeometry
open Integration.Paper9ScalarReciprocal
open Integration.Paper9ScalarCross
open Integration.Paper9SymmetricTauJet
open Integration.Paper9SeparatedCusp
open Integration.Paper9MobiusDiskPeriod

noncomputable section
local notation "j" => Integration.MoonshineEisensteinAgdaTarget.jTarget

def restPoly (τ : ℍ) : Polynomial ℂ :=
  ∏ i ∈ remaining, (X+C ((K:ℂ)-chartValue i τ))

theorem restPolyEval (τ : ℍ) (Y : ℂ) :
    (restPoly τ).eval Y=restProduct τ ((K:ℂ)+Y) := by
  simp only [restPoly,restProduct,Polynomial.eval_prod,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_C]
  apply Finset.prod_congr rfl
  intro i hi
  ring

theorem restPolyDegree (τ : ℍ) : (restPoly τ).natDegree=40 := by
  classical
  have h (s : Finset Chart) :
      (∏ i ∈ s, (X-C (chartValue i τ-(K:ℂ)))).natDegree=s.card := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Polynomial.natDegree_mul
        (Polynomial.monic_X_sub_C _).ne_zero
        (Polynomial.monic_prod_X_sub_C (fun i => chartValue i τ-(K:ℂ)) s).ne_zero,
        Polynomial.natDegree_X_sub_C,ih,Finset.card_insert_of_notMem hi]
      omega
  have he : restPoly τ=∏ i ∈ remaining, (X-C (chartValue i τ-(K:ℂ))) := by
    unfold restPoly
    apply Finset.prod_congr rfl
    intro i hi
    rw [map_sub]
    ring
  rw [he,h,remainingCard]

def restSlope (τ : ℍ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range 40, C ((restPoly τ).coeff (i+1))*X^i

theorem restSlopeCoeff (τ : ℍ) (n : ℕ) :
    (restSlope τ).coeff n=(restPoly τ).coeff (n+1) := by
  unfold restSlope
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hn : n<40
  · rw [Finset.sum_eq_single n]
    · simp
    · intro i hi hne
      simp [Ne.symm hne]
    · simp [hn]
  · have hz := Polynomial.natDegree_le_iff_coeff_eq_zero.mp
      (show (restPoly τ).natDegree≤40 by rw [restPolyDegree]) (n+1) (by omega)
    rw [hz]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp [show n≠i by omega]

theorem restSlopeFactor (τ : ℍ) :
    restPoly τ-C ((restPoly τ).coeff 0)=X^1*restSlope τ := by
  ext n
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul']
  split_ifs with hn
  · rw [restSlopeCoeff,Nat.sub_add_cancel hn]
    have hn' : n≠0 := by omega
    simp [Polynomial.coeff_C,hn']
  · have h : n=0 := by omega
    subst n
    simp

theorem restDifference (τ : ℍ) (Y : ℂ) :
    restProduct τ ((K:ℂ)+Y)-restProduct τ (K:ℂ)=Y*(restSlope τ).eval Y := by
  have h := congrArg (fun p : Polynomial ℂ => p.eval Y) (restSlopeFactor τ)
  simpa [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.coeff_zero_eq_eval_zero,restPolyEval] using h

theorem chart0CM (hj : j cmTau=(K:ℂ)) : chartValue 0 cmTau=(K:ℂ) := by
  have h := reverseForward cmPoint cmApart
  rw [fixedPoint] at h
  rw [reverseChartValue]
  change jExt (reverseHecke cmPoint)=(K:ℂ)
  rw [h]
  exact (jExtAt cmTau).trans hj

-- Original fixed slice is the ORIGINAL CM root polynomial by symmetry
-- and infinite j-image, with no inverse j chart or new bivariate table.
theorem sliceIsCMRootPoly (hu : unitOK=true) (hs : sliceOK=true)
    (hj : j cmTau=(K:ℂ)) :
    packet 42 sliceCoeff=rootPoly cmTau := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply separatedImageInfinite.mono
  intro x hx
  obtain ⟨τ,rfl,_⟩ := hx
  rw [rootEval,← actualSymmetry τ cmTau,hj]
  exact (actualSlice (sliceOfCheck hu hs) τ).symm

theorem sliceShiftIsRest (hu : unitOK=true) (hs : sliceOK=true)
    (hc : jetOK=true) (hj : j cmTau=(K:ℂ)) :
    sliceComplement=restPoly cmTau := by
  obtain ⟨_,_,s0,s1,_,_,_⟩ := jetFacts hc
  have hfac := sliceShiftFactor s0 s1
  have hactual : sliceShift=X^2*restPoly cmTau := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_univ : (Set.univ : Set ℂ).Infinite).mono
    intro Y _
    unfold sliceShift
    rw [Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_X,
      Polynomial.eval_C,sliceIsCMRootPoly hu hs hj,rootEval,
      productSplit,chart0CM hj,cmChartValue,hj]
    simp [Polynomial.eval_mul,Polynomial.eval_pow,restPolyEval]
    ring
  exact (mul_left_cancel₀ (pow_ne_zero 2 (Polynomial.X_ne_zero : (X : Polynomial ℂ)≠0)))
    (hfac.symm.trans hactual)

theorem actualTZero (hu : unitOK=true) (hs : sliceOK=true)
    (hc : jetOK=true) (hj : j cmTau=(K:ℂ)) :
    (restSlope cmTau).eval 0=(sliceShiftZ 3:ℂ) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero,restSlopeCoeff,
    ← sliceShiftIsRest hu hs hc hj,sliceComplementCoeff]

-- Exact cross identity on the actual original Hecke product, before
-- the reciprocal disk is introduced. All raw factors retain sign.
theorem actualRawCross (hu : unitOK=true) (hd : diagOK=true)
    (hs : sliceOK=true) (hc : jetOK=true) (τ : ℍ) :
    let x := j τ-(K:ℂ)
    let xp := chartValue 1 τ-(K:ℂ)
    let xm := chartValue 0 τ-(K:ℂ)
    let N := xp*xm
    let M := (x-xp)*(x-xm)
    (N*complement.eval x-M*sliceComplement.eval x)*x^2 =
      N*M*x*(restSlope τ).eval x := by
  dsimp
  obtain ⟨hp,ha⟩ := actualShiftedProducts hu hd hs hc τ
  rw [productSplit] at hp ha
  have hT := restDifference τ (j τ-(K:ℂ))
  have hY : (K:ℂ)+(j τ-(K:ℂ))=j τ := by ring
  rw [hY] at hT
  linear_combination
    -((chartValue 1 τ-(K:ℂ))*(chartValue 0 τ-(K:ℂ)))*hp +
    ((j τ-chartValue 1 τ)*(j τ-chartValue 0 τ))*ha +
    ((chartValue 1 τ-(K:ℂ))*(chartValue 0 τ-(K:ℂ)))*
      ((j τ-chartValue 1 τ)*(j τ-chartValue 0 τ))*hT

-- Local disk normalization: the three original branch values must
-- supply their genuine scalar normalized germs. No division at w=0.
-- At zero the literal quadratic relation pays the cross; elsewhere
-- cancel only the coordinate power w^4, not any Hecke factor.
theorem normalizedActualCross (hu : unitOK=true) (hd : diagOK=true)
    (hs : sliceOK=true) (hc : jetOK=true)
    (τ : ℂ → ℍ) (X Xp Xm : ℂ → ℂ) (A : ℂ)
    (hx : ∀ᶠ w in 𝓝 (0:ℂ), j (τ w)-(K:ℂ)=w*X w)
    (hp : ∀ᶠ w in 𝓝 (0:ℂ), chartValue 1 (τ w)-(K:ℂ)=w*Xp w)
    (hm : ∀ᶠ w in 𝓝 (0:ℂ), chartValue 0 (τ w)-(K:ℂ)=w*Xm w)
    (hN : Xp 0*Xm 0=A^2)
    (hM : (X 0-Xp 0)*(X 0-Xm 0)=(163/41)*A^2) :
    ∀ᶠ w in 𝓝 (0:ℂ),
      let N := Xp w*Xm w
      let M := (X w-Xp w)*(X w-Xm w)
      (N*complement.eval (w*X w)-M*sliceComplement.eval (w*X w))*(X w)^2 =
        N*M*X w*(w*(restSlope (τ w)).eval (w*X w)) := by
  obtain ⟨_,_,_,_,_,hq,_⟩ := jetFacts hc
  filter_upwards [hx,hp,hm] with w hx' hp' hm'
  dsimp
  by_cases hw : w=0
  · subst w
    rw [hN,hM,zero_mul,← Polynomial.coeff_zero_eq_eval_zero,
      ← Polynomial.coeff_zero_eq_eval_zero,complementCoeff,sliceComplementCoeff]
    simp only [zero_mul,mul_zero]
    linear_combination (A^2*(X 0)^2/41)*hq
  · have h := actualRawCross hu hd hs hc (τ w)
    dsimp at h
    rw [hx',hp',hm'] at h
    apply (mul_left_cancel₀ (pow_ne_zero 4 hw))
    linear_combination h

end
end Integration.Paper9ActualCross
