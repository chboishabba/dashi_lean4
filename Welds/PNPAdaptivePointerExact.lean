import Mathlib
import Welds.PNPPaidCutCapacityExact

namespace PNPAdaptivePointer

-- A deterministic data-dependent schedule is a functional orbit.
def walk {A : Type*} (f : A → A) : Nat → A → A
  | 0, p => p
  | k+1, p => f (walk f k p)

theorem walk_front {A : Type*} (f : A → A) (k : Nat) (p : A) :
    walk f k (f p) = walk f (k+1) p := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [walk]; rw [ih]

def chase {A : Type*} [DecidableEq A] (f : A → A) (target : A) :
    Nat → A → Bool
  | 0, p => decide (p=target)
  | k+1, p => if p=target then true else chase f target k (f p)

theorem chase_exact {A : Type*} [DecidableEq A]
    (f : A → A) (target : A) (k : Nat) (p : A) :
    chase f target k p = true ↔ ∃ i≤k, walk f i p=target := by
  induction k generalizing p with
  | zero =>
    simp [chase,walk]
  | succ k ih =>
    by_cases h : p=target
    · simp only [chase,h,if_true,true_iff]
      exact ⟨0,by omega,h⟩
    · simp only [chase,h,if_false]
      rw [ih]
      constructor
      · rintro ⟨i,hi,he⟩
        exact ⟨i+1,by omega,(walk_front f i p).symm.trans he⟩
      · rintro ⟨i,hi,he⟩
        cases i with
        | zero => exact False.elim (h he)
        | succ i => exact ⟨i,by omega,(walk_front f i p).trans he⟩

-- Relabel the vertices by ANY permutation. The schedule is now
-- data-dependent, but it still uses only the current vertex and fuel.
theorem walk_relabel {A B : Type*} (e : A ≃ B)
    (f : A → A) (g : B → B) (h : ∀ p, g (e p)=e (f p))
    (k : Nat) (p : A) :
    walk g k (e p)=e (walk f k p) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [walk]; rw [ih,h]

theorem chase_relabel {A B : Type*} [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (f : A → A) (g : B → B)
    (h : ∀ p, g (e p)=e (f p)) (k : Nat) (p q : A) :
    chase g (e q) k (e p)=chase f q k p := by
  induction k generalizing p with
  | zero => simp [chase,e.injective.eq_iff]
  | succ k ih =>
    by_cases he : p=q
    · simp [chase,he]
    · have hne : e p≠e q := fun h => he (e.injective h)
      simp [chase,he,hne,h,ih]

theorem equal_state_equal_future {A : Type*} (f : A → A)
    (i j d : Nat) (p : A) (h : walk f i p=walk f j p) :
    walk f (i+d) p=walk f (j+d) p := by
  induction d with
  | zero => simpa using h
  | succ d ih => simpa only [Nat.add_succ,walk] using congrArg f ih

def broken (j : Nat) (p : Nat) : Nat := if p=j then p else p+1

theorem chain_walk (k : Nat) : walk (fun i : Nat => i+1) k 0=k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [walk,ih]

theorem broken_walk (j k : Nat) : walk (broken j) k 0≤j := by
  induction k with
  | zero => exact Nat.zero_le j
  | succ k ih =>
    simp only [walk,broken]
    split <;> omega

theorem every_pointer_sensitive (n j : Nat) (hj : j<n) :
    chase (fun i : Nat => i+1) n n 0=true ∧ chase (broken j) n n 0=false := by
  constructor
  · apply (chase_exact _ _ _ _).mpr
    exact ⟨n,le_rfl,chain_walk n⟩
  · cases h : chase (broken j) n n 0 with
    | false => rfl
    | true =>
      obtain ⟨i,_,hi⟩ := (chase_exact _ _ _ _).mp h
      have hle := broken_walk j i
      omega

-- Data-dependent access and simultaneous sensitivity are not by
-- themselves a superlinear same-run charge. The capacity theorem must
-- still be supplied with actual non-reusable charges per event.
end PNPAdaptivePointer
