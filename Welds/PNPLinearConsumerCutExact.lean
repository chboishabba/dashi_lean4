import Mathlib
import Welds.PNPF3SyndromeBoundaryExact
import Welds.PNPEpochChargeExact

namespace PNPLinearConsumerCut
open PNPF3SyndromeBoundary

-- A ternary kernel displacement is a difference of TWO Boolean lifts,
-- not necessarily a legal move from a specified Boolean lift.
def boolEmbed {n : Nat} (x : Fin n → Bool) : Syndrome n :=
  fun i => if x i then 1 else 0

def positive {n : Nat} (d : Syndrome n) : Fin n → Bool :=
  fun i => decide (d i=1)

def negative {n : Nat} (d : Syndrome n) : Fin n → Bool :=
  fun i => decide (d i=2)

theorem trit_difference (a : ZMod 3) :
    (if a=1 then 1 else 0) - (if a=2 then 1 else 0) = a := by
  revert a
  decide

theorem binary_difference {n : Nat} (d : Syndrome n) :
    boolEmbed (positive d)-boolEmbed (negative d)=d := by
  funext i
  simpa [boolEmbed,positive,negative] using trit_difference (d i)

-- Reverse-solve a fixed read-set consumer. A linear state A and the
-- selected coordinates R must jointly kill every consumer direction.
-- This is NOT a theorem for arbitrary nonlinear stored state or for
-- a read set selected differently on each input.
theorem necessary_kernel {n w m : Nat}
    (A : Syndrome n →ₗ[ZMod 3] Syndrome w)
    (B : Syndrome n →ₗ[ZMod 3] Syndrome m)
    (R : Finset (Fin n))
    (correct : ∀ x y : Fin n → Bool,
      A (boolEmbed x)=A (boolEmbed y) →
      (∀ i∈R,x i=y i) → B (boolEmbed x)=B (boolEmbed y))
    (d : Syndrome n) (ha : A d=0)
    (hr : ∀ i∈R,d i=0) : B d=0 := by
  have hA : A (boolEmbed (positive d))=A (boolEmbed (negative d)) := by
    apply sub_eq_zero.mp
    rw [← map_sub,binary_difference,ha]
  have hR : ∀ i∈R,positive d i=negative d i := by
    intro i hi
    simp [positive,negative,hr i hi]
  rw [← binary_difference d,map_sub,correct _ _ hA hR,sub_self]

-- Converse: for every pair on the original Boolean carrier, the
-- kernel condition is sufficient. No loss from ternary relaxation.
theorem sufficient_kernel {n w m : Nat}
    (A : Syndrome n →ₗ[ZMod 3] Syndrome w)
    (B : Syndrome n →ₗ[ZMod 3] Syndrome m)
    (R : Finset (Fin n))
    (hk : ∀ d : Syndrome n, A d=0 →
      (∀ i∈R,d i=0) → B d=0)
    (x y : Fin n → Bool)
    (ha : A (boolEmbed x)=A (boolEmbed y))
    (hr : ∀ i∈R,x i=y i) :
    B (boolEmbed x)=B (boolEmbed y) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply hk
  · rw [map_sub,ha,sub_self]
  · intro i hi
    simp [boolEmbed,hr i hi]

-- Concrete firewall for adaptive/specified-input inference:
-- the rank-one sum syndrome isolates 00 on the two-bit Boolean cube,
-- although its ternary kernel is nonzero.
theorem zero_fibre_two_bits (x y : Bool) :
    ((if x then 1 else 0) : ZMod 3)+(if y then 1 else 0)=0 ↔
      x=false ∧ y=false := by
  cases x <;> cases y <;> decide

-- Rank-nullity turns the exact kernel criterion into a capacity
-- inequality on the ORIGINAL Boolean lifts, not an F3 volume count.
def readsMap {n : Nat} (R : Finset (Fin n)) :
    Syndrome n →ₗ[ZMod 3] (↥R → ZMod 3) where
  toFun x := fun i => x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rank_capacity {n w m : Nat}
    (A : Syndrome n →ₗ[ZMod 3] Syndrome w)
    (B : Syndrome n →ₗ[ZMod 3] Syndrome m)
    (R : Finset (Fin n))
    (correct : ∀ x y : Fin n → Bool,
      A (boolEmbed x)=A (boolEmbed y) →
      (∀ i∈R,x i=y i) → B (boolEmbed x)=B (boolEmbed y)) :
    Module.finrank (ZMod 3) B.range ≤
      Module.finrank (ZMod 3) A.range + R.card := by
  classical
  let M := A.rangeRestrict.prod (readsMap R)
  have hker : M.ker ≤ B.ker := by
    intro d hd
    have hz : M d=0 := LinearMap.mem_ker.mp hd
    have ha : A d=0 := by
      have h := congrArg (fun p : ↥A.range × (↥R → ZMod 3) => p.1.val) hz
      exact h
    have hr : ∀ i∈R,d i=0 := by
      intro i hi
      exact congrFun (congrArg Prod.snd hz) ⟨i,hi⟩
    exact LinearMap.mem_ker.mpr (necessary_kernel A B R correct d ha hr)
  have hdim := Submodule.finrank_mono hker
  have hm := M.finrank_range_add_finrank_ker
  have hb := B.finrank_range_add_finrank_ker
  have hle : Module.finrank (ZMod 3) B.range ≤ Module.finrank (ZMod 3) M.range := by omega
  have hcap := M.range.finrank_le
  have htarget :
      Module.finrank (ZMod 3) (↥A.range × (↥R → ZMod 3)) =
        Module.finrank (ZMod 3) A.range + R.card := by simp
  exact hle.trans (by simpa only [htarget] using hcap)

end PNPLinearConsumerCut
