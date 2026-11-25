import Integration.Paper9ActualTaylorUnit
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Complex.Exponential

/-! SOURCE-WRITTEN, UNCOMPILED.
Actual normalized product, sharp finite remainder and concrete polynomial
divisibility consumer. No claim that the original integer packet has yet
been reflected. No new Hecke carrier. -/
namespace Integration.Paper9HeckeProductAssembly
open Complex Filter Function UpperHalfPlane
open scoped Topology BigOperators
open Integration.Paper9ActualJSourceJet
open Integration.Paper9ActualTaylorUnit
open Integration.Paper9HeckeFiniteRemainder
open Integration.Paper9Hecke41ChartGeometry
open Integration.Paper9HeckePoleRemoval
open Integration.Paper9EulerMobiusTransport
open Integration.Paper9DiscriminantUnitReflection

noncomputable section
local notation "j" => Integration.MoonshineEisensteinAgdaTarget.jTarget

theorem phaseNe (a : Fin 41) : phase a ≠ 0 := by
  unfold phase
  exact Complex.exp_ne_zero _

theorem phaseProduct : (∏ a : Fin 41, phase a)=1 := by
  have hs : (∑ a : Fin 41, a.val)=820 := by decide
  have hc : (∑ a : Fin 41, (a.val : ℂ))=820 := by exact_mod_cast hs
  have he : (∑ a : Fin 41, 2*Real.pi*Complex.I*(a.val:ℂ)/41) =
      (820:ℂ)*(2*Real.pi*Complex.I/41) := by
    calc
      _ = ∑ a : Fin 41, (2*Real.pi*Complex.I/41)*(a.val:ℂ) := by
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = _ := by rw [← Finset.mul_sum,hc]; ring
  unfold phase
  rw [← Complex.exp_sum,he]
  have h := phasePower (1 : Fin 41)
  have h' : Complex.exp (2*Real.pi*Complex.I/41)^41=1 := by
    simpa [phase] using h
  -- 820 = 41*20, and no phase is discarded.
  rw [Complex.exp_nat_mul]
  change Complex.exp (2*Real.pi*Complex.I/41)^820=1
  rw [show (820:ℕ)=41*20 by decide,pow_mul,h',one_pow]

theorem jChartFinite (a : Fin 41) (τ : ℍ) :
    chartValue a.castSucc τ=jQ (phase a*tParam τ) := by
  unfold chartValue
  rw [← jExtAt (chartPoint a.castSucc τ)]
  unfold jExt
  rw [finiteChartQ]

theorem jChartInfinity (τ : ℍ) :
    chartValue (Fin.last 41) τ=jQ (qExt τ^41) := by
  unfold chartValue
  rw [← jExtAt (chartPoint (Fin.last 41) τ)]
  unfold jExt
  exact congrArg jQ (infinityChartQ τ)

theorem jAtQ (τ : ℍ) : j τ=jQ (qExt τ) := (jExtAt τ).symm

-- Split exactly the 41 finite charts and one infinity chart.
theorem diagonalProduct (τ : ℍ) :
    tParam τ^3362*actualProduct τ (j τ)=
      diagonalNormalized jUnit (tParam τ) := by
  let q := qExt τ
  let z := tParam τ
  have hq : q≠0 := Periodic.qParam_ne_zero 1 τ
  have ht : z≠0 := tNonzero τ
  have hqt : z^41=q := tPower τ
  have hfin (a : Fin 41) :
      q*(j τ-chartValue a.castSucc τ)=
        jUnit q-(phase a*z)^40*jUnit (phase a*z) := by
    rw [jAtQ,jChartFinite]
    apply diagonalFiniteFactor q (phase a*z) hq (mul_ne_zero (phaseNe a) ht)
    rw [mul_pow,phasePower,one_mul,hqt]
  have hinf : q^41*(j τ-chartValue (Fin.last 41) τ)=
      q^40*jUnit q-jUnit (q^41) := by
    rw [jAtQ,jChartInfinity]
    exact diagonalInfinityFactor q hq
  have hp : (∏ a : Fin 41, q*(j τ-chartValue a.castSucc τ)) =
      q^41*(∏ a : Fin 41, (j τ-chartValue a.castSucc τ)) := by
    rw [Finset.prod_mul_distrib]
    simp
  unfold actualProduct diagonalNormalized
  rw [Fin.prod_univ_castSucc]
  change z^3362*((∏ a : Fin 41, (j τ-chartValue a.castSucc τ))*
      (j τ-chartValue (Fin.last 41) τ)) = _
  rw [hqt]
  calc
    _ = (q^41*(j τ-chartValue (Fin.last 41) τ)) *
        (q^41*(∏ a : Fin 41, (j τ-chartValue a.castSucc τ))) := by
          rw [← hqt]
          ring
    _ = _ := by
      rw [hinf,← hp]
      simp_rw [hfin]

theorem sliceProduct (K : ℂ) (τ : ℍ) :
    tParam τ^1722*actualProduct τ K=
      sliceNormalized jUnit K (tParam τ) := by
  let q := qExt τ
  let z := tParam τ
  have hq : q≠0 := Periodic.qParam_ne_zero 1 τ
  have ht : z≠0 := tNonzero τ
  have hqt : z^41=q := tPower τ
  have hfin (a : Fin 41) :
      -(phase a*z)*(K-chartValue a.castSucc τ)=
        jUnit (phase a*z)-K*(phase a*z) := by
    rw [jChartFinite]
    exact fixedFiniteFactor K _ (mul_ne_zero (phaseNe a) ht)
  have hinf : -(q^41)*(K-chartValue (Fin.last 41) τ)=
      jUnit (q^41)-K*q^41 := by
    rw [jChartInfinity]
    exact fixedInfinityFactor K q hq
  have hphase : (∏ a : Fin 41, -(phase a*z))= -q := by
    rw [show (∏ a : Fin 41, -(phase a*z)) =
      ∏ a : Fin 41, phase a*(-z) by
        apply Finset.prod_congr rfl
        intro a ha
        ring]
    rw [Finset.prod_mul_distrib,phaseProduct,one_mul]
    simp [hqt,neg_pow]
  have hp : (∏ a : Fin 41, -(phase a*z)*(K-chartValue a.castSucc τ)) =
      -q*(∏ a : Fin 41, (K-chartValue a.castSucc τ)) := by
    rw [Finset.prod_mul_distrib,hphase]
  unfold actualProduct sliceNormalized
  rw [Fin.prod_univ_castSucc]
  change z^1722*((∏ a : Fin 41, (K-chartValue a.castSucc τ))*
      (K-chartValue (Fin.last 41) τ)) = _
  rw [hqt]
  calc
    _ = (-(q^41)*(K-chartValue (Fin.last 41) τ)) *
        (-q*(∏ a : Fin 41, (K-chartValue a.castSucc τ))) := by
          rw [← hqt]
          ring
    _ = _ := by
      rw [hinf,← hp]
      simp_rw [hfin]

def packet (d : ℕ) (c : ℕ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (d+1), Polynomial.C (c k)*Polynomial.X^(d-k)

theorem columnProduct (d : ℕ) (c : ℕ → ℂ) (τ : ℍ) :
    tParam τ^(41*d)*(packet d c).eval (j τ)=
      normalizedColumnEval jUnit d c (tParam τ) := by
  unfold packet normalizedColumnEval
  rw [pow_mul,tPower,Polynomial.eval_finset_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k≤d := by simpa using hk
  rw [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,
    actualJUnit,mul_pow,show (qExt τ)^d=(qExt τ)^k*(qExt τ)^(d-k) by
      rw [← pow_add,Nat.add_sub_of_le hk']]
  ring

theorem remTrans (n : ℕ) (f g h : ℂ → ℂ)
    (a : Rem n f g) (b : Rem n g h) : Rem n f h := by
  obtain ⟨r,hr,he⟩ := a
  obtain ⟨s,hs,hf⟩ := b
  refine ⟨fun z => r z+s z,hr.add hs,?_⟩
  filter_upwards [he,hf] with z h1 h2
  linear_combination h1+h2

theorem remSum {ι : Type*} (s : Finset ι) (n : ℕ) (f g : ι → ℂ → ℂ)
    (h : ∀ i ∈ s, Rem n (f i) (g i)) :
    Rem n (fun z => ∑ i ∈ s, f i z) (fun z => ∑ i ∈ s, g i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using remRefl n (fun _ => 0)
  | @insert i s hi ih =>
    obtain ⟨r,hr,he⟩ := h i (Finset.mem_insert_self _ _)
    obtain ⟨u,hu,hf⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    refine ⟨fun z => r z+u z,hr.add hu,?_⟩
    filter_upwards [he,hf] with z h1 h2
    simp only [Finset.sum_insert hi]
    linear_combination h1+h2

theorem remPow (n k : ℕ) (f g : ℂ → ℂ)
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0) (h : Rem n f g) :
    Rem n (fun z => f z^k) (fun z => g z^k) := by
  induction k with
  | zero => simpa using remRefl n (fun _ => 1)
  | succ k ih =>
    simpa only [pow_succ] using
      remMul n (fun z => f z^k) (fun z => g z^k) f g (hg.pow k) hf ih h

theorem truncContinuous (m : ℕ) : ContinuousAt (truncJ m) 0 := by
  unfold truncJ
  fun_prop

theorem monomialContinuous (V : ℂ → ℂ) (a : ℂ) (k : ℕ)
    (hk : 0<k) (h : ContinuousAt V 0) :
    ContinuousAt (fun z => V (a*z^k)) 0 := by
  have hc : ContinuousAt (fun z : ℂ => a*z^k) 0 :=
    continuousAt_const.mul (continuousAt_id.pow k)
  exact h.comp_of_eq hc (by simp [zero_pow (Nat.ne_of_gt hk)])

theorem jContinuous : ContinuousAt jUnit 0 :=
  (jUnitAnalytic 0 (by norm_num)).continuousAt

theorem unitMonomialTail (m k n : ℕ) (a : ℂ) (hk : 0<k)
    (hn : n≤k*(m+1)) :
    Rem n (fun z => jUnit (a*z^k)) (fun z => truncJ m (a*z^k)) :=
  remWeaken _ _ _ _ hn (remMonomial _ _ _ _ _ hk (actualJTruncation m))

-- A single finite product assembly with an explicit shift ledger.
theorem diagonalFiniteRemainder :
    Rem 3363 (diagonalNormalized jUnit) (diagonalNormalized (truncJ 3322)) := by
  have hq : Rem 3363 (fun z => jUnit (z^41))
      (fun z => truncJ 3322 (z^41)) := by
    simpa using unitMonomialTail 3322 41 3363 1 (by decide) (by decide)
  have hqq : Rem 3363 (fun z => jUnit ((z^41)^41))
      (fun z => truncJ 3322 ((z^41)^41)) := by
    simpa [pow_mul] using unitMonomialTail 3322 1681 3363 1 (by decide) (by decide)
  have hi := remSub 3363 _ _ _ _
    (remMul 3363 (fun z : ℂ => (z^41)^40) (fun z => (z^41)^40)
      _ _ (by fun_prop) (by simpa using monomialContinuous jUnit 1 41 (by decide) jContinuous)
      (remRefl _ _) hq) hqq
  have hf (a : Fin 41) := remSub 3363 _ _ _ _ hq (diagonalShiftedTail a)
  have hc (V : ℂ → ℂ) (hv : ContinuousAt V 0) (a : Fin 41) :
      ContinuousAt (fun z => V (z^41)-(phase a*z)^40*V (phase a*z)) 0 := by
    have h1 := monomialContinuous V 1 41 (by decide) hv
    have h2 := monomialContinuous V (phase a) 1 (by decide) hv
    simp only [one_mul,pow_one] at h1 h2
    exact h1.sub ((continuousAt_const.mul continuousAt_id).pow 40 |>.mul h2)
  have hp := remProd 3363 Finset.univ _ _
    (fun a _ => hc jUnit jContinuous a)
    (fun a _ => hc (truncJ 3322) (truncContinuous _) a) (fun a _ => hf a)
  unfold diagonalNormalized
  apply remMul 3363 _ _ _ _ ?_ ?_ hi hp
  · have h1 := monomialContinuous (truncJ 3322) 1 41 (by decide) (truncContinuous _)
    have h2 := monomialContinuous (truncJ 3322) 1 1681 (by decide) (truncContinuous _)
    simp only [one_mul] at h1 h2
    simpa [pow_mul] using ((continuousAt_id.pow 41).pow 40 |>.mul h1).sub h2
  · exact continuousAt_finset_prod _ (fun a _ => hc jUnit jContinuous a)

theorem sliceFiniteRemainder (K : ℂ) :
    Rem 1723 (sliceNormalized jUnit K) (sliceNormalized (truncJ 1722) K) := by
  have hi : Rem 1723 (fun z => jUnit ((z^41)^41)-K*(z^41)^41)
      (fun z => truncJ 1722 ((z^41)^41)-K*(z^41)^41) := by
    apply remSub 1723 _ _ _ _ ?_ (remRefl _ _)
    simpa [pow_mul] using unitMonomialTail 1722 1681 1723 1 (by decide) (by decide)
  have hc (V : ℂ → ℂ) (hv : ContinuousAt V 0) (a : Fin 41) :
      ContinuousAt (fun z => V (phase a*z)-K*(phase a*z)) 0 := by
    have h := monomialContinuous V (phase a) 1 (by decide) hv
    simp only [pow_one] at h
    exact h.sub (continuousAt_const.mul (continuousAt_const.mul continuousAt_id))
  have hp := remProd 1723 Finset.univ _ _
    (fun a _ => hc jUnit jContinuous a)
    (fun a _ => hc (truncJ 1722) (truncContinuous _) a)
    (fun a _ => remSub 1723 _ _ _ _ (sliceFiniteTail a) (remRefl _ _))
  unfold sliceNormalized
  apply remMul 1723 _ _ _ _ ?_ ?_ hi hp
  · have h := monomialContinuous (truncJ 1722) 1 1681 (by decide) (truncContinuous _)
    simpa [pow_mul] using h.sub (continuousAt_const.mul (continuousAt_id.pow 1681))
  · exact continuousAt_finset_prod _ (fun a _ => hc jUnit jContinuous a)

theorem columnFiniteRemainder (d m n : ℕ) (c : ℕ → ℂ)
    (hn : n≤41*(m+1)) :
    Rem n (normalizedColumnEval jUnit d c) (normalizedColumnEval (truncJ m) d c) := by
  have h : Rem n (fun z => jUnit (z^41)) (fun z => truncJ m (z^41)) := by
    simpa using unitMonomialTail m 41 n 1 (by decide) hn
  have hf : ContinuousAt (fun z => jUnit (z^41)) 0 := by
    simpa using monomialContinuous jUnit 1 41 (by decide) jContinuous
  have hg : ContinuousAt (fun z => truncJ m (z^41)) 0 := by
    simpa using monomialContinuous (truncJ m) 1 41 (by decide) (truncContinuous m)
  unfold normalizedColumnEval
  apply remSum
  intro k hk
  exact remMul n _ _ _ _ (by fun_prop) (hf.pow (d-k))
    (remRefl _ _) (remPow n (d-k) _ _ hf hg h)

-- Finite polynomials, built from the very same truncation and chart factors.
def jPoly (m : ℕ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (m+1), Polynomial.C (J.coeff i)*Polynomial.X^i

def qPoly : Polynomial ℂ := Polynomial.X^41
def phasePoly (a : Fin 41) : Polynomial ℂ := Polynomial.C (phase a)*Polynomial.X

def diagonalPoly (m : ℕ) : Polynomial ℂ :=
  (qPoly^40*(jPoly m).comp qPoly-(jPoly m).comp (qPoly^41)) *
    ∏ a : Fin 41, ((jPoly m).comp qPoly-(phasePoly a)^40*(jPoly m).comp (phasePoly a))

def slicePoly (m : ℕ) (K : ℂ) : Polynomial ℂ :=
  ((jPoly m).comp (qPoly^41)-Polynomial.C K*qPoly^41) *
    ∏ a : Fin 41, ((jPoly m).comp (phasePoly a)-Polynomial.C K*phasePoly a)

def columnPoly (m d : ℕ) (c : ℕ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (d+1), Polynomial.C (c k)*qPoly^k*((jPoly m).comp qPoly)^(d-k)

theorem jPolyEval (m : ℕ) (z : ℂ) : (jPoly m).eval z=truncJ m z := by
  simp [jPoly,truncJ,Polynomial.eval_finset_sum]

theorem diagonalPolyEval (m : ℕ) (z : ℂ) :
    (diagonalPoly m).eval z=diagonalNormalized (truncJ m) z := by
  simp [diagonalPoly,diagonalNormalized,qPoly,phasePoly,Polynomial.eval_prod,jPolyEval]

theorem slicePolyEval (m : ℕ) (K z : ℂ) :
    (slicePoly m K).eval z=sliceNormalized (truncJ m) K z := by
  simp [slicePoly,sliceNormalized,qPoly,phasePoly,Polynomial.eval_prod,jPolyEval]

theorem columnPolyEval (m d : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    (columnPoly m d c).eval z=normalizedColumnEval (truncJ m) d c z := by
  simp [columnPoly,normalizedColumnEval,qPoly,Polynomial.eval_finset_sum,jPolyEval]

-- The sole finite coefficient premise is literal zero of the original
-- polynomial residual through the specified degree, not a hash receipt.
theorem polynomialRem (n : ℕ) (P Q : Polynomial ℂ)
    (h : ∀ k<n, (P-Q).coeff k=0) : Rem n P.eval Q.eval := by
  obtain ⟨G,hG⟩ := Polynomial.X_pow_dvd_iff.mpr h
  refine ⟨G.eval,G.continuous.continuousAt,Filter.Eventually.of_forall ?_⟩
  intro z
  have he := congrArg (fun A : Polynomial ℂ => A.eval z) hG
  simpa using he

theorem remReverse (n : ℕ) (f g : ℂ → ℂ) (h : Rem n f g) : Rem n g f := by
  obtain ⟨r,hr,he⟩ := h
  refine ⟨fun z => -r z,hr.neg,?_⟩
  filter_upwards [he] with z hz
  linear_combination -hz

theorem diagonalFromCoefficients (c : ℕ → ℂ)
    (h : ∀ k<3363, (diagonalPoly 3322-columnPoly 3322 82 c).coeff k=0) :
    ∀ τ, actualProduct τ (j τ)=(packet 82 c).eval (j τ) := by
  have hp := polynomialRem 3363 _ _ h
  simp_rw [diagonalPolyEval,columnPolyEval] at hp
  have hc := columnFiniteRemainder 82 3322 3363 c (by decide)
  have hr := remTrans 3363 _ _ _ (remTrans 3363 _ _ _ diagonalFiniteRemainder hp)
    (remReverse 3363 _ _ hc)
  apply diagonalIdentity
  apply residualGermToCusp 3362 _ _ _ hr
  exact Filter.Eventually.of_forall (fun τ => by
    unfold diagonalResidual
    rw [mul_sub,diagonalProduct,show (3362:ℕ)=41*82 by decide,columnProduct])

theorem sliceFromCoefficients (K : ℂ) (c : ℕ → ℂ)
    (h : ∀ k<1723, (slicePoly 1722 K-columnPoly 1722 42 c).coeff k=0) :
    ∀ τ, actualProduct τ K=(packet 42 c).eval (j τ) := by
  have hp := polynomialRem 1723 _ _ h
  simp_rw [slicePolyEval,columnPolyEval] at hp
  have hc := columnFiniteRemainder 42 1722 1723 c (by decide)
  have hr := remTrans 1723 _ _ _ (remTrans 1723 _ _ _ (sliceFiniteRemainder K) hp)
    (remReverse 1723 _ _ hc)
  apply sliceIdentity
  apply residualGermToCusp 1722 _ _ _ hr
  exact Filter.Eventually.of_forall (fun τ => by
    unfold sliceResidual
    rw [mul_sub,sliceProduct,show (1722:ℕ)=41*42 by decide,columnProduct])

end
end Integration.Paper9HeckeProductAssembly
