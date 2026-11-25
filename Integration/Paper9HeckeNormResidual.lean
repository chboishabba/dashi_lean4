import Integration.Paper9HeckeSectorRotation
import Mathlib.Algebra.Polynomial.Derivative

/-! SOURCE-WRITTEN, UNCOMPILED. The finite log-derivative recurrence
is transported through the actual cyclic norm by a signed residual
identity. No division of formal power series or unbounded product.
The integer packet's original H,L and N coefficients still need
literal finite reflection at the 3362/1722 frontiers. -/
namespace Integration.Paper9HeckeNormResidual
open Polynomial
open scoped BigOperators
open Integration.Paper9HeckeFiniteRemainder
open Integration.Paper9HeckeSectorRotation

noncomputable section

def E (H : Polynomial ℂ) : Polynomial ℂ := X*H.derivative
def rot (a : Fin 41) (H : Polynomial ℂ) : Polynomial ℂ :=
  H.comp (C (phase a)*X)
def normT (H : Polynomial ℂ) : Polynomial ℂ := ∏ a : Fin 41, rot a H
def traceT (L : Polynomial ℂ) : Polynomial ℂ := ∑ a : Fin 41, rot a L

theorem EProd (H L : Polynomial ℂ) :
    E (H*L)=E H*L+H*E L := by
  unfold E
  rw [Polynomial.derivative_mul]
  ring

theorem ERot (a : Fin 41) (H : Polynomial ℂ) :
    E (rot a H)=rot a (E H) := by
  unfold E rot
  rw [Polynomial.derivative_comp,Polynomial.derivative_C_mul_X,
    Polynomial.mul_comp,Polynomial.X_comp]
  ring

theorem rotateResidual (H L R : Polynomial ℂ) (m : ℕ)
    (h : E H-H*L=X^m*R) (a : Fin 41) :
    E (rot a H)-rot a H*rot a L =
      X^m*(C ((phase a)^m)*rot a R) := by
  have he := congrArg (rot a) h
  unfold rot at he
  rw [Polynomial.sub_comp,Polynomial.mul_comp,Polynomial.mul_comp,
    Polynomial.pow_comp,Polynomial.X_comp,mul_pow,← Polynomial.C_pow] at he
  rw [ERot]
  unfold rot
  rw [he]
  ring

-- Product residual is a sum of terms retaining the omitted chart.
-- A factor X^m is never divided out at t=0.
theorem productResidual {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f l r : ι → Polynomial ℂ) (m : ℕ)
    (h : ∀ i ∈ s, E (f i)-f i*l i=X^m*r i) :
    ∃ R : Polynomial ℂ,
      E (∏ i ∈ s, f i)-(∏ i ∈ s, f i)*(∑ i ∈ s, l i)=X^m*R := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0,by simp [E]⟩
  | @insert i s hi ih =>
    obtain ⟨R,hR⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    refine ⟨r i*(∏ j ∈ s, f j)+f i*R,?_⟩
    rw [Finset.prod_insert hi,Finset.sum_insert hi,EProd]
    calc
      _ = (E (f i)-f i*l i)*(∏ j ∈ s, f j)+
          f i*(E (∏ j ∈ s, f j)-(∏ j ∈ s, f j)*(∑ j ∈ s, l j)) := by ring
      _ = _ := by rw [h i (Finset.mem_insert_self _ _),hR]; ring

theorem normResidual (H L R : Polynomial ℂ) (m : ℕ)
    (h : E H-H*L=X^m*R) :
    ∃ R' : Polynomial ℂ, E (normT H)-normT H*traceT L=X^m*R' := by
  exact productResidual Finset.univ (fun a => rot a H) (fun a => rot a L)
    (fun a => C ((phase a)^m)*rot a R) m (fun a _ => rotateResidual H L R m h a)

theorem EPolyCoeff (H : Polynomial ℂ) (n : ℕ) :
    (E H).coeff n=(n:ℂ)*H.coeff n := by
  cases n with
  | zero => simp [E]
  | succ n =>
    rw [E,Polynomial.coeff_X_mul,Polynomial.coeff_derivative]
    push_cast
    ring

theorem traceCoeff (L : Polynomial ℂ) (n : ℕ) :
    (traceT L).coeff n=(∑ a : Fin 41, (phase a)^n)*L.coeff n := by
  unfold traceT
  rw [Polynomial.coeff_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  exact scaleCoeff L (phase a) n

-- The exact root-of-unity character sum. Cyclic relabelling is the
-- same original chart permutation as the polynomial sector rotation.
theorem phaseSum (n : ℕ) :
    (∑ a : Fin 41, (phase a)^n)=if 41∣n then 41 else 0 := by
  by_cases hn : 41∣n
  · rw [if_pos hn]
    have h (a : Fin 41) : (phase a)^n=1 := by
      obtain ⟨k,hk⟩ := hn
      rw [hk,pow_mul,phasePower,one_pow]
    simp [h]
  · rw [if_neg hn]
    let s := ∑ a : Fin 41, (phase a)^n
    have hs : ζ^n*s=s := by
      unfold s
      rw [Finset.mul_sum]
      calc
        _ = ∑ a : Fin 41, (phase (cycle a))^n := by
          apply Finset.sum_congr rfl
          intro a _
          rw [← phaseNext,mul_pow,mul_comm]
        _ = _ := cycle.sum_comp (fun a => (phase a)^n)
    exact Integration.Paper9HeckeProductAssembly.offSectorZero ζ 41 n s zetaPrimitive hs hn

theorem traceSector (L : Polynomial ℂ) (n : ℕ) :
    (traceT L).coeff n=if 41∣n then 41*L.coeff n else 0 := by
  rw [traceCoeff,phaseSum]
  split <;> simp_all

-- This is the direct finite polynomial analogue of the existing
-- Laurent normRecurrence; it retains EVERY coefficient up to m-1.
theorem normCoefficientEquation (H L R : Polynomial ℂ) (m n : ℕ)
    (h : E H-H*L=X^m*R) (hn : n<m) :
    (n:ℂ)*(normT H).coeff n=(normT H*traceT L).coeff n := by
  obtain ⟨S,hS⟩ := normResidual H L R m h
  have hc := congrArg (fun P : Polynomial ℂ => P.coeff n) hS
  rw [Polynomial.coeff_sub,EPolyCoeff] at hc
  have hz : (X^m*S).coeff n=0 := by
    rw [Polynomial.coeff_X_pow_mul']
    simp [not_le.mpr hn]
  rw [hz] at hc
  exact sub_eq_zero.mp hc


-- The norm itself has the same exact cyclic permutation symmetry.
theorem normRotation (H : Polynomial ℂ) (z : ℂ) :
    (normT H).eval (ζ*z)=(normT H).eval z := by
  unfold normT
  simp only [Polynomial.eval_prod,rot,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  calc
    _ = ∏ a : Fin 41, H.eval (phase (cycle a)*z) := by
      apply Finset.prod_congr rfl
      intro a _
      rw [← mul_assoc,phaseNext]
    _ = _ := cycle.prod_comp (fun a => H.eval (phase a*z))

theorem normOffSector (H : Polynomial ℂ) (n : ℕ) (hn : ¬ 41∣n) :
    (normT H).coeff n=0 :=
  Integration.Paper9HeckeProductAssembly.offSectorZero ζ 41 n _
    zetaPrimitive (coeffCovariance _ (normRotation H) n) hn

theorem normConstant (H : Polynomial ℂ) (h : H.coeff 0=1) :
    (normT H).coeff 0=1 := by
  rw [← Polynomial.eval_zero]
  unfold normT
  simp [Polynomial.eval_prod,rot,Polynomial.eval_comp,Polynomial.eval_zero,h]

-- Scaling both indices of the original antidiagonal is injective.
def scalePair : (ℕ × ℕ) ↪ (ℕ × ℕ) where
  toFun p := (41*p.1,41*p.2)
  inj' := by
    intro a b h
    apply Prod.ext
    · have he := congrArg Prod.fst h
      change 41*a.1=41*b.1 at he
      omega
    · have he := congrArg Prod.snd h
      change 41*a.2=41*b.2 at he
      omega

theorem scaledAntidiagonal (n : ℕ) :
    (Finset.Nat.antidiagonal n).map scalePair ⊆ Finset.Nat.antidiagonal (41*n) := by
  intro a ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp ha
  have h := Finset.Nat.mem_antidiagonal.mp hb
  apply Finset.Nat.mem_antidiagonal.mpr
  change 41*b.1+41*b.2=41*n
  omega

theorem scaledAntidiagonalComplete (n : ℕ) (a : ℕ × ℕ)
    (ha : a ∈ Finset.Nat.antidiagonal (41*n)) (hd : 41∣a.2) :
    a ∈ (Finset.Nat.antidiagonal n).map scalePair := by
  obtain ⟨j,hj⟩ := hd
  have h := Finset.Nat.mem_antidiagonal.mp ha
  have hjn : j≤n := by omega
  apply Finset.mem_map.mpr
  refine ⟨(n-j,j),Finset.Nat.mem_antidiagonal.mpr (by omega),?_⟩
  apply Prod.ext
  · change 41*(n-j)=a.1
    omega
  · exact hj.symm

-- Only the original invariant-sector convolution survives. This is
-- a finite exact reindexing, not an asymptotic estimate.
theorem sectorConvolution (H L : Polynomial ℂ) (n : ℕ) :
    (normT H*traceT L).coeff (41*n)=
      (41:ℂ)*(∑ a ∈ Finset.Nat.antidiagonal n,
        (normT H).coeff (41*a.1)*L.coeff (41*a.2)) := by
  rw [Polynomial.coeff_mul]
  have he : (∑ a ∈ (Finset.Nat.antidiagonal n).map scalePair,
        (normT H).coeff a.1*(traceT L).coeff a.2)=
      ∑ a ∈ Finset.Nat.antidiagonal (41*n),
        (normT H).coeff a.1*(traceT L).coeff a.2 := by
    apply Finset.sum_subset (scaledAntidiagonal n)
    intro a ha hnot
    have hn : ¬41∣a.2 := fun hd => hnot (scaledAntidiagonalComplete n a ha hd)
    rw [traceSector,if_neg hn,mul_zero]
  rw [← he,Finset.sum_map,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change (normT H).coeff (41*a.1)*(traceT L).coeff (41*a.2)=_
  rw [traceSector,if_pos (dvd_mul_right 41 a.2)]
  ring

theorem descendedEquation (H L R : Polynomial ℂ) (m n : ℕ)
    (h : E H-H*L=X^m*R) (hn : 41*n<m) :
    (n:ℂ)*(normT H).coeff (41*n)=
      ∑ a ∈ Finset.Nat.antidiagonal n,
        (normT H).coeff (41*a.1)*L.coeff (41*a.2) := by
  have he := normCoefficientEquation H L R m (41*n) h hn
  rw [sectorConvolution] at he
  push_cast at he
  apply mul_left_cancel₀ (show (41:ℂ)≠0 by norm_num)
  linear_combination he

-- Same range-oriented recurrence as the original unit_norm, with
-- L_0=0 and N_0=1, including the first positive index.
theorem descendedRecurrence (H L R : Polynomial ℂ) (m n : ℕ)
    (h : E H-H*L=X^m*R) (hL : L.coeff 0=0)
    (hn : 41*n<m) :
    (n:ℂ)*(normT H).coeff (41*n)=
      ∑ i ∈ Finset.range n, L.coeff (41*(i+1))*(normT H).coeff (41*(n-(i+1))) := by
  rw [descendedEquation H L R m n h hn,Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ]
  cases n with
  | zero => simp [hL]
  | succ n =>
    rw [Finset.sum_range_succ']
    simp only [mul_zero,hL,zero_mul,mul_zero,zero_add,add_zero]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem packetNormAgreement (H L R : Polynomial ℂ) (m d : ℕ)
    (h : E H-H*L=X^m*R) (hH : H.coeff 0=1) (hL : L.coeff 0=0)
    (hm : 41*d<m) (b : ℕ → ℂ) (hb0 : b 0=1)
    (hb : ∀ n, 0<n → n≤d →
      (n:ℂ)*b n=∑ i ∈ Finset.range n, L.coeff (41*(i+1))*b (n-(i+1))) :
    ∀ n≤d, (normT H).coeff (41*n)=b n := by
  apply Integration.Paper9HeckeProductAssembly.finiteNormUnique d
    (fun i => L.coeff (41*i)) (fun i => (normT H).coeff (41*i)) b
  · simpa [hb0] using normConstant H hH
  · intro n hp hn
    exact descendedRecurrence H L R m n h hL (by omega)
  · exact hb

end
end Integration.Paper9HeckeNormResidual
