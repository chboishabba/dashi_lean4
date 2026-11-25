import Integration.Paper9ActualJSourceJet

/-! SOURCE-WRITTEN, UNCOMPILED.
The original 42 index-41 cyclic charts. S/T forward and inverse
permutations retain the integral correction matrices. The selected
actual product has a zero factor. This is not the analytic Laurent
coefficient or bivariate polynomial reflection theorem. -/
namespace Integration.Paper9Hecke41ChartGeometry

open Complex Function UpperHalfPlane
open scoped BigOperators Matrix
open Integration.Paper9ActualCMPoint
open Integration.Paper9ActualJSourceJet
open Integration.Paper9EulerMobiusTransport

abbrev Mat := Matrix (Fin 2) (Fin 2) ℤ
abbrev Chart := Fin 42

def a (i : Chart) : Mat :=
  if i.val=41 then !![41,0;0,1] else !![1,(i.val : ℤ);0,41]

def s : Mat := !![0,-1;1,0]
def t : Mat := !![1,1;0,1]

def sTable : List ℕ :=
  [0,40,20,27,10,8,34,35,5,9,4,26,17,22,38,30,23,12,25,28,2,
   39,13,16,29,18,11,3,19,24,15,37,32,36,6,7,33,31,14,21,1]

def sIndex (i : Chart) : Chart :=
  if i.val=41 then 0 else if i.val=0 then 41
  else ⟨(sTable[i.val]?.getD 0)%42,Nat.mod_lt _ (by decide)⟩

def tIndex (i : Chart) : Chart :=
  if i.val=41 then 41 else ⟨(i.val+1)%41,by omega⟩

def tBack (i : Chart) : Chart :=
  if i.val=41 then 41 else ⟨(i.val+40)%41,by omega⟩

def sCorrection (i : Chart) : Mat :=
  if i.val=0 ∨ i.val=41 then s else
  let k : ℤ := i.val
  let m : ℤ := (sIndex i).val
  !![k,(-k*m-1)/41;41,-m]

def tCorrection (i : Chart) : Mat :=
  if i.val=41 then !![1,41;0,1] else if i.val=40 then t else 1

def dualIndex (i : Chart) : Chart := if i.val=41 then 0 else 41
def dualCorrection (i : Chart) : Mat :=
  if i.val=41 then 1 else !![1,-(i.val : ℤ);0,1]

def adj2 (m : Mat) : Mat := !![m 1 1,-m 0 1;-m 1 0,m 0 0]

-- Closed finite kernel targets, not claims of execution of decide.
theorem allDet : ∀ i : Chart, (a i).det=41 := by decide
theorem allSDet : ∀ i : Chart, (sCorrection i).det=1 := by decide
theorem allTDet : ∀ i : Chart, (tCorrection i).det=1 := by decide
theorem allDualDet : ∀ i : Chart, (dualCorrection i).det=1 := by decide
theorem allS : ∀ i : Chart, a i*s=sCorrection i*a (sIndex i) := by decide
theorem allT : ∀ i : Chart, a i*t=tCorrection i*a (tIndex i) := by decide
theorem allDual : ∀ i : Chart, adj2 (a i)=dualCorrection i*a (dualIndex i) := by decide
theorem allDualBack : ∀ i : Chart, adj2 (a i)*a i=(41 : ℤ) • (1 : Mat) := by decide
theorem sRoundTrip : ∀ i : Chart, sIndex (sIndex i)=i := by decide
theorem tRoundTrip : ∀ i : Chart, tBack (tIndex i)=i ∧ tIndex (tBack i)=i := by decide

def sPerm : Equiv.Perm Chart where
  toFun := sIndex
  invFun := sIndex
  left_inv := sRoundTrip
  right_inv := sRoundTrip

def tPerm : Equiv.Perm Chart where
  toFun := tIndex
  invFun := tBack
  left_inv i := (tRoundTrip i).1
  right_inv i := (tRoundTrip i).2

-- Original H points for the cyclic row-lattice representatives.
noncomputable def chartPoint (i : Chart) (τ : ℍ) : ℍ :=
  if h : i.val=41 then
    ⟨41*(τ : ℂ),by simpa using (mul_pos (by norm_num : (0:ℝ)<41) τ.im_pos)⟩
  else
    ⟨((τ : ℂ)+(i.val : ℂ))/41,by
      simp [Complex.div_im]
      positivity⟩

noncomputable def chartValue (i : Chart) (τ : ℍ) : ℂ :=
  Integration.MoonshineEisensteinAgdaTarget.jTarget (chartPoint i τ)

noncomputable def actualProduct (τ : ℍ) (Y : ℂ) : ℂ :=
  ∏ i : Chart, (Y-chartValue i τ)

-- Direct self-isogeny on the original chart; no Hilbert polynomial.
theorem cmChartFixed : ModularGroup.S • chartPoint 1 cmTau = cmTau := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul]
  change -(((cmPoint+1)/41))⁻¹=cmPoint
  have h := fixedPoint
  unfold hecke at h
  field_simp [cmApart] at h ⊢
  linear_combination h

theorem cmChartValue : chartValue 1 cmTau =
    Integration.MoonshineEisensteinAgdaTarget.jTarget cmTau := by
  unfold chartValue
  rw [← Integration.MoonshineEisensteinAgdaTarget.jTarget_S_invariant
    (chartPoint 1 cmTau),cmChartFixed]

theorem cmProductZero :
    actualProduct cmTau (Integration.MoonshineEisensteinAgdaTarget.jTarget cmTau)=0 := by
  unfold actualProduct
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : Chart))
  rw [cmChartValue,sub_self]

-- If two chart lists are related by actual chart transport, the product
-- itself is invariant; no bivariate modular polynomial has been assumed.
theorem productTransport (τ σ : ℍ) (e : Equiv.Perm Chart)
    (h : ∀ i, chartValue i σ=chartValue (e i) τ) (Y : ℂ) :
    actualProduct σ Y=actualProduct τ Y := by
  unfold actualProduct
  simp only [h]
  exact e.prod_comp (fun i => Y-chartValue i τ)

-- Explicit analytic transport of the original chart coordinates.
-- Matrix multiplication is paid by a cleared-denominator identity.
def denom (m : Mat) (z : ℂ) : ℂ := (m 1 0 : ℂ)*z+(m 1 1 : ℂ)
def numer (m : Mat) (z : ℂ) : ℂ := (m 0 0 : ℂ)*z+(m 0 1 : ℂ)
def eval (m : Mat) (z : ℂ) : ℂ := numer m z/denom m z

theorem evalMul (m n : Mat) (z : ℂ)
    (hn : denom n z ≠ 0) (hm : denom m (eval n z) ≠ 0) :
    eval (m*n) z = eval m (eval n z) := by
  have hd : denom (m*n) z=denom m (eval n z)*denom n z := by
    unfold denom eval numer
    simp only [Matrix.mul_apply,Fin.sum_univ_two,Int.cast_add,Int.cast_mul]
    field_simp [hn] <;> ring
  have hv : numer (m*n) z=numer m (eval n z)*denom n z := by
    unfold denom eval numer
    simp only [Matrix.mul_apply,Fin.sum_univ_two,Int.cast_add,Int.cast_mul]
    field_simp [hn] <;> ring
  unfold eval at *
  rw [hd,hv]
  field_simp [hn,hm] <;> ring

theorem chartEval (i : Chart) (τ : ℍ) :
    eval (a i) τ = (chartPoint i τ : ℂ) := by
  by_cases h : i.val=41
  · simp [eval,numer,denom,a,chartPoint,h]
  · simp [eval,numer,denom,a,chartPoint,h]

theorem chartDenom (i : Chart) (τ : ℍ) : denom (a i) τ ≠ 0 := by
  by_cases h : i.val=41 <;> simp [denom,a,h]

theorem slEval (g : SL(2, ℤ)) (τ : ℍ) :
    eval (g : Mat) τ = ((g • τ : ℍ) : ℂ) := mobiusAt g τ

theorem slDenom (g : SL(2, ℤ)) (τ : ℍ) :
    denom (g : Mat) τ ≠ 0 := linear_ne_zero g τ

def sSL (i : Chart) : SL(2, ℤ) := ⟨sCorrection i,allSDet i⟩
def tSL (i : Chart) : SL(2, ℤ) := ⟨tCorrection i,allTDet i⟩
def dualSL (i : Chart) : SL(2, ℤ) := ⟨dualCorrection i,allDualDet i⟩

-- Consume a specific exact correction edge in the actual H action.
theorem chartCovariance (i k : Chart) (g c : SL(2, ℤ)) (τ : ℍ)
    (he : a i*(g : Mat)=(c : Mat)*a k) :
    chartPoint i (g • τ)=c • chartPoint k τ := by
  apply UpperHalfPlane.ext
  rw [← chartEval,← slEval]
  have h1 := evalMul (a i) (g : Mat) (τ : ℂ) (slDenom g τ)
    (by rw [slEval]; exact chartDenom i _)
  have h2 := evalMul (c : Mat) (a k) (τ : ℂ) (chartDenom k τ)
    (by rw [chartEval]; exact slDenom c _)
  rw [he] at h1
  rw [slEval] at h1
  rw [chartEval] at h2
  exact h1.symm.trans h2

theorem chartSTransport (i : Chart) (τ : ℍ) :
    chartPoint i (ModularGroup.S • τ)=sSL i • chartPoint (sIndex i) τ := by
  apply chartCovariance
  change a i*s=sCorrection i*a (sIndex i)
  exact allS i

theorem chartTTransport (i : Chart) (τ : ℍ) :
    chartPoint i (ModularGroup.T • τ)=tSL i • chartPoint (tIndex i) τ := by
  apply chartCovariance
  change a i*t=tCorrection i*a (tIndex i)
  exact allT i

theorem productSInvariant (τ : ℍ) (Y : ℂ) :
    actualProduct (ModularGroup.S • τ) Y=actualProduct τ Y := by
  apply productTransport τ _ sPerm
  intro i
  unfold chartValue
  rw [chartSTransport,jInvariant]

theorem productTInvariant (τ : ℍ) (Y : ℂ) :
    actualProduct (ModularGroup.T • τ) Y=actualProduct τ Y := by
  apply productTransport τ _ tPerm
  intro i
  unfold chartValue
  rw [chartTTransport,jInvariant]

-- Actual reverse chart, retaining the dual correction; this gives the
-- opposite root independently of any presumed symmetry of Phi.
theorem reverseChart (i : Chart) (τ : ℍ) :
    dualSL i • chartPoint (dualIndex i) (chartPoint i τ)=τ := by
  apply UpperHalfPlane.ext
  rw [← slEval,← chartEval]
  have h1 := evalMul (dualCorrection i) (a (dualIndex i))
    (chartPoint i τ : ℂ) (chartDenom _ _) (by
      rw [chartEval]; exact slDenom (dualSL i) _)
  rw [← allDual i] at h1
  have h2 := evalMul (adj2 (a i)) (a i) (τ : ℂ) (chartDenom i τ) (by
    rw [chartEval,allDual i]
    have h := evalMul (dualCorrection i) (a (dualIndex i))
      (chartPoint i τ : ℂ) (chartDenom _ _) (by
        rw [chartEval]; exact slDenom (dualSL i) _)
    -- direct denominator product (the two known positive chart scales)
    by_cases hi : i.val=41 <;>
      simp [denom,adj2,a,dualIndex,dualCorrection,hi])
  rw [allDualBack i] at h2
  rw [chartEval] at h2
  rw [← h1,← h2]
  simp [eval,numer,denom,Matrix.smul_apply]
  ring

theorem reverseRoot (i : Chart) (τ : ℍ) :
    actualProduct (chartPoint i τ)
      (Integration.MoonshineEisensteinAgdaTarget.jTarget τ)=0 := by
  unfold actualProduct
  apply Finset.prod_eq_zero (Finset.mem_univ (dualIndex i))
  unfold chartValue
  rw [← jInvariant (dualSL i),reverseChart,sub_self]


end Integration.Paper9Hecke41ChartGeometry
