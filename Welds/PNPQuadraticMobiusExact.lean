import Mathlib
import Welds.PNPDualFourierAlternatingTraceExact

open scoped BigOperators

namespace PNPQuadraticPhase

-- Completion of the square over F3 uses 4 = 1 and a⁻¹ = a.
-- The finite proof is exhaustive on the actual field, not a numerical test.
theorem complete_square (a b x : ZMod 3) :
    a ≠ 0 → a*x^2+b*x = a*(x-a*b)^2-a*b^2 := by
  fin_cases a <;> fin_cases b <;> fin_cases x <;> decide

def translate (a : ZMod 3) : ZMod 3 ≃ ZMod 3 where
  toFun x := x-a
  invFun x := x+a
  left_inv x := sub_add_cancel x a
  right_inv x := add_sub_cancel_right x a

-- This is the exact scalar Gauss elimination, with an explicit character
-- law. It never assumes that an arbitrary source admits a quadratic phase.
theorem gauss_axis {R : Type*} [CommRing R]
    (chi : ZMod 3 → R) (hchi : ∀ x y, chi (x+y) = chi x * chi y)
    (a b c : ZMod 3) (ha : a ≠ 0) :
    (∑ x : ZMod 3, chi (a*x^2+b*x+c)) =
      chi (c-a*b^2) * ∑ x : ZMod 3, chi (a*x^2) := by
  calc
    _ = ∑ x : ZMod 3, chi (c-a*b^2) * chi (a*(x-a*b)^2) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [complete_square a b x ha, ← hchi]
      congr 1
      ring
    _ = chi (c-a*b^2) * ∑ x : ZMod 3, chi (a*(x-a*b)^2) := by
      rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      exact Equiv.sum_comp (translate (a*b)) (fun x => chi (a*x^2))

end PNPQuadraticPhase

namespace PNPSignedCubeIntersection

inductive Pin where
  | any | off | on | impossible
  deriving DecidableEq

def allows : Pin → Bool → Prop
  | .any, _ => True
  | .off, b => b = false
  | .on, b => b = true
  | .impossible, _ => False

def meet : Pin → Pin → Pin
  | .any, q => q
  | .off, .any => .off
  | .off, .off => .off
  | .off, .on => .impossible
  | .off, .impossible => .impossible
  | .on, .any => .on
  | .on, .off => .impossible
  | .on, .on => .on
  | .on, .impossible => .impossible
  | .impossible, _ => .impossible

theorem meet_exact (p q : Pin) (b : Bool) :
    allows (meet p q) b ↔ allows p b ∧ allows q b := by
  cases p <;> cases q <;> cases b <;> simp [allows, meet]

abbrev Cube (n : Nat) := Fin n → Pin

def intersection {n : Nat} (p q : Cube n) : Cube n := fun i => meet (p i) (q i)

def holds {n : Nat} (p : Cube n) (x : Fin n → Bool) : Prop :=
  ∀ i, allows (p i) (x i)

theorem holds_intersection {n : Nat} (p q : Cube n) (x : Fin n → Bool) :
    holds (intersection p q) x ↔ holds p x ∧ holds q x := by
  constructor
  · intro h
    exact ⟨fun i => ((meet_exact (p i) (q i) (x i)).mp (h i)).1,
           fun i => ((meet_exact (p i) (q i) (x i)).mp (h i)).2⟩
  · rintro ⟨hp,hq⟩ i
    exact (meet_exact (p i) (q i) (x i)).mpr ⟨hp i,hq i⟩

noncomputable def indicator {n : Nat} (p : Cube n) (x : Fin n → Bool) : ℤ := by
  classical
  exact if holds p x then 1 else 0

theorem indicator_intersection {n : Nat} (p q : Cube n) (x : Fin n → Bool) :
    indicator (intersection p q) x = indicator p x * indicator q x := by
  classical
  by_cases hp : holds p x <;> by_cases hq : holds q x <;>
    simp [indicator, holds_intersection, hp, hq]

abbrev Terms (n : Nat) := List (ℤ × Cube n)

noncomputable def eval {n : Nat} (T : Terms n) (x : Fin n → Bool) : ℤ :=
  match T with
  | [] => 0
  | (a,p)::ts => a * indicator p x + eval ts x

def expand {n : Nat} (f : Cube n) : Terms n → Terms n
  | [] => []
  | (a,p)::ts => (a,p)::(-a,intersection p f)::expand f ts

-- Each forbidden cube multiplies the previous signed indicator by
-- (1-I_f). Opposite pins and duplicate intersections may subsequently
-- be compressed by the executable dictionary.
theorem expand_eval {n : Nat} (f : Cube n) (T : Terms n) (x : Fin n → Bool) :
    eval (expand f T) x = eval T x * (1-indicator f x) := by
  induction T with
  | nil => simp [eval, expand]
  | cons t ts ih =>
    rcases t with ⟨a,p⟩
    simp only [expand, eval, indicator_intersection, ih]
    ring

def compile {n : Nat} : List (Cube n) → Terms n
  | [] => [(1, fun _ => .any)]
  | f::fs => expand f (compile fs)

theorem compile_eval {n : Nat} (fs : List (Cube n)) (x : Fin n → Bool) :
    eval (compile fs) x = (if ∀ f ∈ fs, ¬ holds f x then 1 else 0) := by
  classical
  induction fs with
  | nil => simp [compile, eval, indicator, holds, allows]
  | cons f fs ih =>
    rw [compile, expand_eval, ih]
    by_cases hf : holds f x <;> by_cases hs : ∀ q ∈ fs, ¬ holds q x <;>
      simp [indicator, hf, hs]

end PNPSignedCubeIntersection
