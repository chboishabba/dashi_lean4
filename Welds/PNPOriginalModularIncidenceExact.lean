import Welds.PNPFrontierResolutionExact
import Welds.PNPSameRunReadFootprintExact

namespace PNPOriginalModularIncidence
open PNPFrontierResolution
open scoped BigOperators

-- Work over the original integer incidence rows reduced into any
-- modulus. ZMod (p^e) need not be a field; only ring operations used.
def emb (R : Type*) [CommRing R] (b : Bool) : R := if b then 1 else 0

def positive {n : Nat} (row : Finset (Fin n)) : Clause n :=
  row.image (fun i => (i,true))

def negativePair {n : Nat} (i j : Fin n) : Clause n :=
  {(i,false),(j,false)}

theorem exactOneFromClauses {n : Nat} (F : List (Clause n))
    (x : Assignment n) (row : Finset (Fin n)) (hx : SatAll x F)
    (pos : positive row ∈ F)
    (neg : ∀ i ∈ row, ∀ j ∈ row, i≠j → negativePair i j ∈ F) :
    ∃ i ∈ row, x i=true ∧ ∀ j ∈ row, x j=true → j=i := by
  obtain ⟨p,hp,he⟩ := hx _ pos
  obtain ⟨i,hi,ei⟩ := Finset.mem_image.mp hp
  subst p
  refine ⟨i,hi,he,?_⟩
  intro j hj hval
  by_contra hne
  obtain ⟨p,hp,hs⟩ := hx _ (neg j hj i hi hne)
  simp only [negativePair,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with h|h
  · subst p
    simp [hval] at hs
  · subst p
    simp [he] at hs

theorem exactOne_sum {R : Type*} [CommRing R] {n : Nat}
    (x : Assignment n) (row : Finset (Fin n))
    (h : ∃ i ∈ row, x i=true ∧ ∀ j ∈ row, x j=true → j=i) :
    (∑ j : Fin n, (if j∈row then 1 else 0 : R)*emb R (x j))=1 := by
  classical
  obtain ⟨i,hi,hxi,uniq⟩ := h
  rw [Finset.sum_eq_single i]
  · simp [hi,hxi,emb]
  · intro j _ hji
    by_cases hj : j∈row
    · cases hval : x j
      · simp [hj,hval,emb]
      · exact False.elim (hji (uniq j hj hval))
    · simp [hj]
  · simp

-- The actual short certificate: row combination annihilates all
-- columns but not the target. No claim of Boolean feasibility from
-- absence of a modular obstruction.
theorem modular_conflict {R : Type*} [CommRing R] {n m : Nat}
    (A : Fin m → Fin n → R) (b y : Fin m → R) (x : Fin n → R)
    (source : ∀ i, (∑ j, A i j*x j)=b i)
    (annihilate : ∀ j, (∑ i, y i*A i j)=0)
    (nonzero : (∑ i,y i*b i)≠0) : False := by
  classical
  apply nonzero
  calc
    (∑ i,y i*b i) = ∑ i,y i*(∑ j,A i j*x j) := by simp_rw [source]
    _ = ∑ i,∑ j,y i*A i j*x j := by simp [Finset.mul_sum,mul_assoc]
    _ = ∑ j,∑ i,y i*A i j*x j := Finset.sum_comm
    _ = ∑ j,(∑ i,y i*A i j)*x j := by simp [Finset.sum_mul]
    _ = 0 := by simp [annihilate]

theorem original_incidence_refutes {n m modulus : Nat}
    (F : List (Clause n)) (rows : Fin m → Finset (Fin n))
    (pos : ∀ i, positive (rows i)∈F)
    (neg : ∀ i j, j∈rows i → ∀ k, k∈rows i → j≠k → negativePair j k∈F)
    (y : Fin m → ZMod modulus)
    (annihilate : ∀ j, (∑ i, y i*(if j∈rows i then 1 else 0))=0)
    (nonzero : (∑ i,y i)≠0) : ¬ ∃ x : Assignment n, SatAll x F := by
  rintro ⟨x,hx⟩
  exact modular_conflict (fun i j => if j∈rows i then 1 else 0)
    (fun _ => (1 : ZMod modulus)) y (fun j => emb (ZMod modulus) (x j))
    (fun i => exactOne_sum x (rows i) (exactOneFromClauses F x (rows i) hx
      (pos i) (neg i))) annihilate (by simpa using nonzero)

def blocking {n : Nat} (scope : Finset (Fin n)) (z : Assignment n) : Clause n :=
  scope.image (fun i => (i,!z i))

theorem blocking_excludes {n : Nat} (scope : Finset (Fin n)) (x : Assignment n) :
    ¬ SatClause x (blocking scope x) := by
  rintro ⟨p,hp,he⟩
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hp
  subst p
  cases h : x i <;> simp [h] at he

-- Complete local forbidden parity assignments are original clauses.
-- The bounded arity extractor checks their finite list, not a promise
-- that an arbitrary CNF is XOR.
theorem parityFromClauses {n : Nat} (F : List (Clause n)) (x : Assignment n)
    (scope : Finset (Fin n)) (b : ZMod 2)
    (hx : SatAll x F)
    (covered : ∀ z : Assignment n, (∑ j∈scope,emb (ZMod 2) (z j))≠b →
      blocking scope z ∈ F) :
    (∑ j∈scope,emb (ZMod 2) (x j))=b := by
  by_contra h
  exact blocking_excludes scope x (hx _ (covered x h))

-- Exact output semantics for a bounded producer. Refusal preserves the
-- original source, not an asserted lower bound on all representations.
inductive Outcome {n : Nat} (F : List (Clause n)) where
  | witness (x : Assignment n) (valid : SatAll x F)
  | empty (refutes : ¬ ∃ x : Assignment n, SatAll x F)
  | unresolved

def residual {n : Nat} (F : List (Clause n)) (_ : Outcome F) : List (Clause n) := F

theorem unresolved_retains_source {n : Nat} (F : List (Clause n)) :
    residual F (.unresolved : Outcome F)=F := rfl

-- Reuse existing exact shared reservation telescope, separate from
-- any physical machine clock theorem.
theorem declared_allowance_exact (cap left : Nat) (charges : List Nat)
    (h : PNPSameRunReadFootprint.Allowance.consume cap charges=some left) :
    charges.sum+left=cap :=
  PNPSameRunReadFootprint.Allowance.total_exact cap charges left h

end PNPOriginalModularIncidence
