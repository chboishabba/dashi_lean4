import Mathlib

namespace PNPGolay729Hyperbolic

-- Matrix copied from the ACTUAL systematic generator in
-- DASHI.Foundations.TernaryGolay.ExplicitCode729, with h_i=-e_i+sum_{j≠i} g_j.
-- Agda companion consumes that owner directly. All finite Gram and inverse
-- identities are concrete proof bodies; native checking remains pending.
abbrev K := ZMod 3
abbrev Word := Fin 12 → K
abbrev Mat := Matrix (Fin 12) (Fin 12) K

def P : Mat := !![1, 0, 0, 0, 0, 0, 2, 1, 1, 1, 1, 1;
   0, 1, 0, 0, 0, 0, 1, 2, 1, 1, 1, 1;
   0, 0, 1, 0, 0, 0, 1, 1, 2, 1, 1, 1;
   0, 0, 0, 1, 0, 0, 1, 1, 1, 2, 1, 1;
   0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 2, 1;
   0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2;
   2, 2, 2, 2, 2, 0, 2, 2, 2, 2, 2, 1;
   0, 1, 2, 2, 1, 1, 1, 0, 2, 2, 0, 0;
   2, 1, 0, 1, 2, 1, 2, 0, 1, 0, 2, 0;
   1, 2, 2, 1, 0, 1, 0, 2, 2, 0, 1, 0;
   1, 0, 1, 2, 2, 1, 0, 1, 0, 2, 2, 0;
   2, 2, 1, 0, 1, 1, 2, 2, 0, 1, 0, 0]

def D : Mat := !![0, 1, 1, 1, 1, 1, 0, 1, 0, 2, 2, 0;
   1, 0, 1, 1, 1, 1, 0, 2, 2, 0, 1, 0;
   1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 2, 2;
   1, 1, 1, 0, 1, 1, 0, 0, 2, 2, 0, 1;
   1, 1, 1, 1, 0, 1, 0, 2, 0, 1, 0, 2;
   1, 1, 1, 1, 1, 0, 1, 2, 2, 2, 2, 2;
   2, 0, 0, 0, 0, 0, 1, 0, 1, 2, 2, 1;
   0, 2, 0, 0, 0, 0, 1, 2, 2, 1, 0, 1;
   0, 0, 2, 0, 0, 0, 1, 1, 0, 1, 2, 2;
   0, 0, 0, 2, 0, 0, 1, 1, 2, 2, 1, 0;
   0, 0, 0, 0, 2, 0, 1, 2, 1, 0, 1, 2;
   0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 2, 2]

def polarMatrix : Mat := fun i j => if i=j then 0 else 1

def hyperbolicMatrix : Mat := fun i j =>
  if i.val+6=j.val ∨ j.val+6=i.val then 1 else 0

set_option maxHeartbeats 4000000 in
theorem gram : P.transpose * polarMatrix * P = hyperbolicMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

set_option maxHeartbeats 4000000 in
theorem decoder_polar : D = hyperbolicMatrix * P.transpose * polarMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

set_option maxHeartbeats 2000000 in
theorem left_inverse : D * P = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

set_option maxHeartbeats 2000000 in
theorem right_inverse : P * D = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

def encode (x : Word) : Word := P *ᵥ x
def decode (x : Word) : Word := D *ᵥ x

theorem decode_encode (x : Word) : decode (encode x) = x := by
  rw [decode,encode,Matrix.mulVec_mulVec,left_inverse,Matrix.one_mulVec]

theorem encode_decode (x : Word) : encode (decode x) = x := by
  rw [encode,decode,Matrix.mulVec_mulVec,right_inverse,Matrix.one_mulVec]

def chartEquiv : Word ≃ Word where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

theorem polar_transport (x y : Word) :
    dotProduct (encode x) (polarMatrix *ᵥ encode y) =
      dotProduct x (hyperbolicMatrix *ᵥ y) := by
  unfold encode
  calc
    _ = dotProduct x (P.transpose *ᵥ (polarMatrix *ᵥ (P *ᵥ y))) := by
      rw [Matrix.dotProduct_transpose_mulVec]
      exact dotProduct_comm _ _
    _ = dotProduct x ((P.transpose * polarMatrix * P) *ᵥ y) := by
      rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
    _ = _ := by rw [gram]

-- 2 = inverse of 2 in F3. The actual original quadratic is the
-- upper-triangular pair sum; the new chart has six hyperbolic pairs.
def quadratic (x : Word) : K := 2 * dotProduct x (polarMatrix *ᵥ x)

theorem quadratic_transport (x : Word) :
    quadratic (encode x) = 2 * dotProduct x (hyperbolicMatrix *ᵥ x) := by
  rw [quadratic,polar_transport]

set_option maxHeartbeats 4000000 in
theorem original_pair_sum (x : Word) :
    quadratic x = ∑ i : Fin 12, ∑ j : Fin 12, if i<j then x i*x j else 0 := by
  simp [quadratic,polarMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem message_card : Fintype.card (Fin 6 → K) = 729 := by
  decide

end PNPGolay729Hyperbolic
