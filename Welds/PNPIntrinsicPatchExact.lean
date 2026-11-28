import Mathlib
import Welds.PNPConditionalAutarkyExact
import Welds.PNPF3SyndromeBoundaryExact

namespace PNPIntrinsicPatch
open PNPF3SyndromeBoundary
open scoped BigOperators

-- Systematic image coordinates. The executable owner constructs these
-- by RREF on the actual interior columns, not by counting ambient trits.
def decode {m r : Nat} (B : Fin r → Syndrome m) (k : Syndrome r) : Syndrome m :=
  fun j => ∑ i, k i * B i j

def encode {m r : Nat} (p : Fin r → Fin m) (y : Syndrome m) : Syndrome r :=
  fun i => y (p i)

theorem encode_decode {m r : Nat} (B : Fin r → Syndrome m)
    (p : Fin r → Fin m) (sys : ∀ i j, B i (p j) = if i=j then 1 else 0)
    (k : Syndrome r) : encode p (decode B k)=k := by
  classical
  funext j
  simp [encode,decode,sys, mul_ite, Finset.sum_ite_eq']

theorem decode_injective {m r : Nat} (B : Fin r → Syndrome m)
    (p : Fin r → Fin m) (sys : ∀ i j, B i (p j) = if i=j then 1 else 0) :
    Function.Injective (decode B) := by
  intro x y h
  simpa only [encode_decode B p sys] using congrArg (encode p) h

theorem member_exact {m r : Nat} (B : Fin r → Syndrome m)
    (p : Fin r → Fin m) (sys : ∀ i j, B i (p j) = if i=j then 1 else 0)
    (y : Syndrome m) :
    (∃ k, decode B k=y) ↔ decode B (encode p y)=y := by
  constructor
  · rintro ⟨k,rfl⟩
    rw [encode_decode B p sys]
  · intro h
    exact ⟨encode p y,h⟩

theorem key_match {m r : Nat} (B : Fin r → Syndrome m)
    (p : Fin r → Fin m) (sys : ∀ i j, B i (p j) = if i=j then 1 else 0)
    (k : Syndrome r) (y : Syndrome m) :
    decode B k=y ↔ encode p y=k ∧ decode B (encode p y)=y := by
  constructor
  · rintro rfl
    simp [encode_decode B p sys]
  · rintro ⟨h,e⟩
    rwa [h] at e

-- The same original lift subtype, not a replacement uniform F3 mass.
def fibreEquiv {A : Type*} {m r : Nat} (B : Fin r → Syndrome m)
    (p : Fin r → Fin m) (sys : ∀ i j, B i (p j) = if i=j then 1 else 0)
    (f : A → Syndrome m) (hf : ∀ x, decode B (encode p (f x))=f x)
    (k : Syndrome r) :
    {x : A // f x=decode B k} ≃ {x : A // encode p (f x)=k} where
  toFun x := ⟨x.val, by rw [x.property,encode_decode B p sys]⟩
  invFun x := ⟨x.val, by rw [← x.property,hf]⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

theorem fibreCard {A : Type*} [Fintype A] {m r : Nat}
    (B : Fin r → Syndrome m) (p : Fin r → Fin m)
    (sys : ∀ i j, B i (p j) = if i=j then 1 else 0)
    (f : A → Syndrome m) (hf : ∀ x, decode B (encode p (f x))=f x)
    (k : Syndrome r) :
    Fintype.card {x : A // f x=decode B k} =
      Fintype.card {x : A // encode p (f x)=k} :=
  Fintype.card_congr (fibreEquiv B p sys f hf k)

-- State merge in the Boolean fold: two partial witnesses with the
-- same additive key and unresolved clauses have identical future
-- admissibility, but BOTH multiplicities must be retained.
def nextKey {r : Nat} (a : Syndrome r) (hit : Finset Nat)
    (s : Syndrome r × Finset Nat) (b : Bool) :
    Syndrome r × Finset Nat :=
  (s.1 + (if b then a else 0), s.2 \ hit)

theorem merge_future {r : Nat} (a : Syndrome r) (hit : Finset Nat)
    (s t : Syndrome r × Finset Nat) (h : s=t) (b : Bool) :
    nextKey a hit s b=nextKey a hit t b := congrArg (fun u => nextKey a hit u b) h

theorem two_branch_mass (L R : Nat) : (L+R)=R+L := Nat.add_comm _ _

end PNPIntrinsicPatch
