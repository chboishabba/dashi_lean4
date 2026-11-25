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

end
end Integration.Paper9HeckeNormResidual
