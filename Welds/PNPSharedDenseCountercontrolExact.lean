import Mathlib

namespace PNPSharedDenseCountercontrol
open scoped BigOperators

-- Classical parity mask on an even-dimensional Boolean carrier.
def mask {n : Nat} (x : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => x i + ∑ j, x j

theorem parity_preserved {n : Nat} (hn : (n : ZMod 2) = 0)
    (x : Fin n → ZMod 2) :
    (∑ i, mask x i) = ∑ i, x i := by
  simp [mask, Finset.sum_add_distrib, nsmul_eq_mul, hn]

theorem mask_involution {n : Nat} (hn : (n : ZMod 2) = 0)
    (x : Fin n → ZMod 2) : mask (mask x) = x := by
  funext i
  change (x i + ∑ j, x j) + (∑ j, mask x j) = x i
  rw [parity_preserved hn]
  have h : (2 : ZMod 2) = 0 := by decide
  calc
    _ = x i + 2 * (∑ j, x j) := by ring
    _ = x i := by rw [h, zero_mul, add_zero]

def impulse {n : Nat} (j : Fin n) : Fin n → ZMod 2 :=
  fun i => if i=j then 1 else 0

theorem impulse_mask {n : Nat} (i j : Fin n) (h : i≠j) :
    mask (impulse j) i = 1 := by
  classical
  simp [mask, impulse, h]

-- Reversible nonlinear local donor. At zero and every single-coordinate
-- perturbation its quadratic term is zero; composing disjoint triples
-- BEFORE the shared mask preserves the dense sensitivity at zero.
def toffoli (x : ZMod 2 × ZMod 2 × ZMod 2) :
    ZMod 2 × ZMod 2 × ZMod 2 :=
  (x.1,x.2.1,x.2.2+x.1*x.2.1)

theorem toffoli_involution (x : ZMod 2 × ZMod 2 × ZMod 2) :
    toffoli (toffoli x) = x := by
  rcases x with ⟨a,b,c⟩
  change (a,b,c+a*b+a*b) = (a,b,c)
  have h : (2 : ZMod 2)=0 := by decide
  have e : c+a*b+a*b=c := by
    calc
      _ = c+2*(a*b) := by ring
      _ = c := by rw [h,zero_mul,add_zero]
  rw [e]

theorem toffoli_impulse (a b c : ZMod 2) (h : a*b=0) :
    toffoli (a,b,c) = (a,b,c) := by simp [toffoli,h]

theorem composition_injective {A B C : Type*}
    (f : A → B) (g : B → C) (u : B → A) (v : C → B)
    (hf : ∀ x, u (f x)=x) (hg : ∀ y, v (g y)=y) :
    Function.Injective (g ∘ f) := by
  intro x y h
  have e := congrArg (u ∘ v) h
  simpa only [Function.comp_apply,hg,hf] using e

-- Executable companion explicitly builds a shared XOR chain and bounded
-- degree copy tree, with disjoint Toffoli triples, <=5n gates.
-- Neither exponential injectivity nor dense local sensitivity entails
-- an unrestricted superlinear cost. A true lower bound must exclude
-- this kind of shared computation, not charge identical information twice.
end PNPSharedDenseCountercontrol
