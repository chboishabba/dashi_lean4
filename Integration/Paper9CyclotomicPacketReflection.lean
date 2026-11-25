import Integration.Paper9HeckeProductAssembly
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Polynomial.Expand

/-! SOURCE-WRITTEN, UNCOMPILED.
Use the pinned Mathlib polynomial expand/contract (Kenny Lau) and
complex primitive root owners. Exact finite polynomial carrier; no new
analytic j, no independent Hecke carrier, no floating phases.
The concrete integer recurrence/cast packet is still a separate gate. -/
namespace Integration.Paper9CyclotomicPacketReflection
open Complex Polynomial
open scoped BigOperators
open Integration.Paper9HeckeFiniteRemainder
open Integration.Paper9HeckeProductAssembly
open Integration.Paper9ActualTaylorUnit

noncomputable section
abbrev P := Polynomial ℂ
def ζ : ℂ := Complex.exp (2*Real.pi*Complex.I/41)

theorem primitive : IsPrimitiveRoot ζ 41 := by
  simpa [ζ] using Complex.isPrimitiveRoot_exp 41 (by decide)

theorem phaseEq (a : Fin 41) : phase a=ζ^a.val := by
  unfold phase ζ
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem phaseSucc (a : Fin 41) : phase (a+1)=phase a*ζ := by
  rw [phaseEq,phaseEq,← pow_succ]
  have hv : (a+1).val=(a.val+1)%41 := by simp [Fin.val_add]
  rw [hv]
  by_cases ha : a.val+1<41
  · rw [Nat.mod_eq_of_lt ha]
  · have h : a.val+1=41 := by omega
    rw [h, Nat.mod_self, pow_zero, primitive.pow_eq_one]

-- Scaling the variable is a ring homomorphism, not an arbitrary
-- coordinate permutation on the coefficient vector.
def scale (a : ℂ) : P →+* P :=
  Polynomial.compRingHom (Polynomial.C a*Polynomial.X)

theorem scaleCoeff (a : ℂ) (f : P) (n : ℕ) :
    (scale a f).coeff n=a^n*f.coeff n := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add,Polynomial.coeff_add,hf,hg,Polynomial.coeff_add,mul_add]
  | monomial k c =>
    change ((Polynomial.monomial k c).comp (Polynomial.C a*Polynomial.X)).coeff n=_
    rw [Polynomial.monomial_comp,mul_pow,← map_pow,← mul_assoc,← map_mul,
      Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_monomial]
    split_ifs with h
    · subst k; ring
    · simp

theorem scaleScale (a b : ℂ) (f : P) :
    scale a (scale b f)=scale (a*b) f := by
  ext n
  simp only [scaleCoeff,mul_pow]
  ring

theorem scaleQ (a : Fin 41) : scale (phase a) qPoly=qPoly := by
  change (Polynomial.C (phase a)*Polynomial.X)^41=Polynomial.X^41
  rw [mul_pow,← map_pow,phasePower,map_one,one_mul]

def cyclicNorm (H : P) : P := ∏ a : Fin 41, scale (phase a) H

theorem normRotate (H : P) : scale ζ (cyclicNorm H)=cyclicNorm H := by
  unfold cyclicNorm
  rw [map_prod]
  apply Fintype.prod_equiv (Equiv.addRight (1 : Fin 41))
  intro a
  rw [scaleScale,phaseSucc,mul_comm ζ]

theorem normCovariance (H : P) (n : ℕ) :
    ζ^n*(cyclicNorm H).coeff n=(cyclicNorm H).coeff n := by
  rw [← scaleCoeff,normRotate]

theorem phaseSum (n : ℕ) :
    (∑ a : Fin 41, (phase a)^n)=if 41 ∣ n then 41 else 0 := by
  classical
  by_cases h : 41 ∣ n
  · rw [if_pos h]
    obtain ⟨k,hk⟩ := h
    simp_rw [hk,pow_mul,phasePower,one_pow]
    simp
  · rw [if_neg h]
    have hs : ζ^n*(∑ a : Fin 41, (phase a)^n)=
        ∑ a : Fin 41, (phase a)^n := by
      rw [Finset.mul_sum]
      apply Fintype.sum_equiv (Equiv.addRight (1 : Fin 41))
      intro a
      rw [phaseSucc,mul_pow]
      ring
    exact offSectorZero ζ 41 n _ primitive hs h

def phaseTrace (L : P) : P := ∑ a : Fin 41, scale (phase a) L

theorem phaseTraceCoeff (L : P) (n : ℕ) :
    (phaseTrace L).coeff n=(if 41 ∣ n then 41 else 0)*L.coeff n := by
  unfold phaseTrace
  simp only [map_sum,scaleCoeff,← Finset.sum_mul,phaseSum]

-- The geometric inverse exists exactly on the rotation-invariant sector.
theorem expandContractSector (A : P)
    (h : ∀ n, ¬ 41 ∣ n → A.coeff n=0) :
    Polynomial.expand ℂ 41 (Polynomial.contract 41 A)=A := by
  ext n
  rw [Polynomial.coeff_expand (by decide : 0<41),
    Polynomial.coeff_contract (by decide : 41≠0)]
  split_ifs with hn
  · rw [Nat.div_mul_cancel hn]
  · exact (h n hn).symm

theorem normDescent (H : P) :
    Polynomial.expand ℂ 41 (Polynomial.contract 41 (cyclicNorm H))=cyclicNorm H :=
  expandContractSector _ (fun n hn => offSectorZero ζ 41 n _ primitive (normCovariance H n) hn)

theorem traceDescent (L : P) :
    phaseTrace L=Polynomial.expand ℂ 41 (Polynomial.C 41*Polynomial.contract 41 L) := by
  ext n
  rw [phaseTraceCoeff,Polynomial.coeff_expand (by decide : 0<41)]
  split_ifs with h
  · rw [Polynomial.coeff_C_mul,Polynomial.coeff_contract (by decide : 41≠0),
      Nat.div_mul_cancel h]
  · simp

-- Denominator-cleared Euler identity.  No analytic logarithm, and no
-- division by H; the finite residual is retained in the original ideal.
def euler (H : P) : P := Polynomial.X*H.derivative

theorem eulerMul (H G : P) : euler (H*G)=euler H*G+H*euler G := by
  unfold euler
  rw [Polynomial.derivative_mul]
  ring

theorem scaleEuler (a : ℂ) (H : P) : scale a (euler H)=euler (scale a H) := by
  unfold euler scale
  change (Polynomial.X*H.derivative).comp (Polynomial.C a*Polynomial.X)=
    Polynomial.X*(H.comp (Polynomial.C a*Polynomial.X)).derivative
  rw [Polynomial.mul_comp,Polynomial.X_comp,Polynomial.derivative_comp]
  simp
  ring

theorem eulerCoeff (H : P) (n : ℕ) : (euler H).coeff n=(n:ℂ)*H.coeff n := by
  cases n with
  | zero => simp [euler]
  | succ n =>
    rw [euler,Polynomial.coeff_X_mul,Polynomial.coeff_derivative]
    push_cast
    ring

theorem scaleError (a : ℂ) (H L G : P) (r : ℕ)
    (h : euler H-H*L=Polynomial.X^r*G) :
    euler (scale a H)-scale a H*scale a L=
      Polynomial.X^r*(Polynomial.C (a^r)*scale a G) := by
  have he := congrArg (scale a) h
  simp only [map_sub,map_mul,map_pow,scaleEuler] at he
  change _ = (Polynomial.C a*Polynomial.X)^r*scale a G at he
  rw [mul_pow,← map_pow] at he
  linear_combination he

-- Signed product residual: exact witness via finite product induction.
theorem productEulerError {ι : Type*} (s : Finset ι) (F T : ι → P) (r : ℕ)
    (h : ∀ i ∈ s, Polynomial.X^r ∣ euler (F i)-F i*T i) :
    Polynomial.X^r ∣
      euler (∏ i ∈ s,F i)-(∏ i ∈ s,F i)*(∑ i ∈ s,T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [euler]
  | @insert i s hi ih =>
    obtain ⟨A,hA⟩ := h i (Finset.mem_insert_self _ _)
    obtain ⟨B,hB⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    refine ⟨A*(∏ j ∈ s,F j)+F i*B,?_⟩
    rw [Finset.prod_insert hi,Finset.sum_insert hi,eulerMul]
    linear_combination (∏ j ∈ s,F j)*hA+F i*hB

theorem normEulerError (H L : P) (r : ℕ)
    (h : Polynomial.X^r ∣ euler H-H*L) :
    Polynomial.X^r ∣ euler (cyclicNorm H)-cyclicNorm H*phaseTrace L := by
  obtain ⟨G,hG⟩ := h
  unfold cyclicNorm phaseTrace
  apply productEulerError
  intro a ha
  exact ⟨_,scaleError (phase a) H L G r hG⟩

-- Contract the actual Euler residual at n*41, using exact expansion.
-- The product coefficient is descended before cancelling the integer 41.
theorem normRecurrenceActual (H L : P) (d n : ℕ)
    (h : Polynomial.X^(41*d+1) ∣ euler H-H*L) (hn : n≤d) :
    let N := Polynomial.contract 41 (cyclicNorm H)
    let V := Polynomial.contract 41 L
    (n:ℂ)*N.coeff n=(N*V).coeff n := by
  dsimp
  have hz := Polynomial.X_pow_dvd_iff.mp (normEulerError H L _ h) (41*n) (by omega)
  rw [Polynomial.coeff_sub,eulerCoeff] at hz
  have hm : cyclicNorm H*phaseTrace L =
      Polynomial.expand ℂ 41
        (Polynomial.C 41*(Polynomial.contract 41 (cyclicNorm H)*Polynomial.contract 41 L)) := by
    rw [traceDescent,← normDescent H,← map_mul,← mul_assoc,mul_comm (Polynomial.contract 41 (cyclicNorm H)) (Polynomial.C 41),mul_assoc]
  rw [hm,Polynomial.coeff_expand_mul' (by decide : 0<41),
    Polynomial.coeff_C_mul,show (41*n:ℕ)=n*41 by omega,
    ← Polynomial.coeff_contract (by decide : 41≠0),Nat.cast_mul] at hz
  apply mul_left_cancel₀ (show (41:ℂ)≠0 by norm_num)
  push_cast at hz
  linear_combination hz

-- The literal H used by the original scalar producer; the infinity
-- factor and columns are already polynomials in q=t^41.
def diagH (m : ℕ) : P :=
  (jPoly m).comp qPoly-Polynomial.X^40*jPoly m
def sliceH (m : ℕ) (K : ℂ) : P := jPoly m-Polynomial.C K*Polynomial.X

theorem diagFactor (m : ℕ) (a : Fin 41) :
    scale (phase a) (diagH m)=
      (jPoly m).comp qPoly-(phasePoly a)^40*(jPoly m).comp (phasePoly a) := by
  unfold diagH
  rw [map_sub,map_mul,map_pow]
  have he : scale (phase a) ((jPoly m).comp qPoly)=(jPoly m).comp qPoly := by
    change ((jPoly m).comp qPoly).comp (phasePoly a)=_
    rw [Polynomial.comp_assoc]
    exact congrArg (fun Q => (jPoly m).comp Q) (scaleQ a)
  rw [he]
  rfl

theorem sliceFactor (m : ℕ) (K : ℂ) (a : Fin 41) :
    scale (phase a) (sliceH m K)=
      (jPoly m).comp (phasePoly a)-Polynomial.C K*phasePoly a := by
  unfold sliceH
  rw [map_sub,map_mul]
  change _ - (Polynomial.C K).comp (phasePoly a)*Polynomial.X.comp (phasePoly a)=_
  rw [Polynomial.C_comp,Polynomial.X_comp]
  rfl

theorem diagNormAttached (m : ℕ) :
    diagonalPoly m =
      (qPoly^40*(jPoly m).comp qPoly-(jPoly m).comp (qPoly^41))*
        cyclicNorm (diagH m) := by
  unfold diagonalPoly cyclicNorm
  simp_rw [diagFactor]

theorem sliceNormAttached (m : ℕ) (K : ℂ) :
    slicePoly m K =
      ((jPoly m).comp (qPoly^41)-Polynomial.C K*qPoly^41)*
        cyclicNorm (sliceH m K) := by
  unfold slicePoly cyclicNorm
  simp_rw [sliceFactor]

def diagInfinityQ (m : ℕ) : P :=
  Polynomial.X^40*jPoly m-(jPoly m).comp qPoly
def sliceInfinityQ (m : ℕ) (K : ℂ) : P :=
  (jPoly m).comp qPoly-Polynomial.C K*Polynomial.X^41
def columnQ (m d : ℕ) (c : ℕ → ℂ) : P :=
  ∑ k ∈ Finset.range (d+1), Polynomial.C (c k)*Polynomial.X^k*(jPoly m)^(d-k)

theorem diagExpand (m : ℕ) :
    diagonalPoly m=Polynomial.expand ℂ 41
      (diagInfinityQ m*Polynomial.contract 41 (cyclicNorm (diagH m))) := by
  rw [diagNormAttached,map_mul,normDescent]
  congr 1
  unfold diagInfinityQ
  rw [map_sub,map_mul,map_pow,Polynomial.expand_X]
  change _ = qPoly^40*(jPoly m).comp qPoly-
    Polynomial.expand ℂ 41 ((jPoly m).comp qPoly)
  rw [Polynomial.expand_eq_comp_X_pow,Polynomial.comp_assoc]
  rfl

theorem sliceExpand (m : ℕ) (K : ℂ) :
    slicePoly m K=Polynomial.expand ℂ 41
      (sliceInfinityQ m K*Polynomial.contract 41 (cyclicNorm (sliceH m K))) := by
  rw [sliceNormAttached,map_mul,normDescent]
  congr 1
  unfold sliceInfinityQ
  rw [map_sub,map_mul,map_pow,Polynomial.expand_X,Polynomial.expand_C,
    Polynomial.expand_eq_comp_X_pow,Polynomial.comp_assoc]
  rfl

theorem columnExpand (m d : ℕ) (c : ℕ → ℂ) :
    columnPoly m d c=Polynomial.expand ℂ 41 (columnQ m d c) := by
  unfold columnPoly columnQ
  simp only [map_sum,map_mul,map_pow,Polynomial.expand_C,Polynomial.expand_X]
  simp only [Polynomial.expand_eq_comp_X_pow,qPoly]

-- Exact bridge to original analytic consumers: 83 and 43 coefficients
-- on the descended polynomials, not a 5086-position certificate.
theorem diagonalSectorConsumer (c : ℕ → ℂ)
    (h : ∀ n≤82, (diagInfinityQ 3322*
      Polynomial.contract 41 (cyclicNorm (diagH 3322))-columnQ 3322 82 c).coeff n=0) :
    ∀ τ, Integration.Paper9Hecke41ChartGeometry.actualProduct τ
      (Integration.MoonshineEisensteinAgdaTarget.jTarget τ)=
      (packet 82 c).eval (Integration.MoonshineEisensteinAgdaTarget.jTarget τ) := by
  apply diagonalFromCoefficients
  intro k hk
  rw [diagExpand,columnExpand,← map_sub,Polynomial.coeff_expand (by decide : 0<41)]
  split_ifs with he
  · apply h
    omega
  · rfl

theorem sliceSectorConsumer (K : ℂ) (c : ℕ → ℂ)
    (h : ∀ n≤42, (sliceInfinityQ 1722 K*
      Polynomial.contract 41 (cyclicNorm (sliceH 1722 K))-columnQ 1722 42 c).coeff n=0) :
    ∀ τ, Integration.Paper9Hecke41ChartGeometry.actualProduct τ K=
      (packet 42 c).eval (Integration.MoonshineEisensteinAgdaTarget.jTarget τ) := by
  apply sliceFromCoefficients
  intro k hk
  rw [sliceExpand,columnExpand,← map_sub,Polynomial.coeff_expand (by decide : 0<41)]
  split_ifs with he
  · apply h
    omega
  · rfl

end
end Integration.Paper9CyclotomicPacketReflection
