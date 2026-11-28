import Mathlib
import Welds.PNPStackFiveLaneTransferExact

namespace PNPMaterializedValuationResource

-- A resource ledger on the actual product representation, independent
-- of the number of accelerated transfers used to reach the exponent list.
structure Lane where
  base : Nat
  exponent : Nat
  lower : Nat
  upper : Nat

def packed : List Lane → Nat
  | [] => 1
  | p::ps => p.base ^ p.exponent * packed ps

def lowerExponent : List Lane → Nat
  | [] => 0
  | p::ps => p.lower * p.exponent + lowerExponent ps

def upperExponent : List Lane → Nat
  | [] => 0
  | p::ps => p.upper * p.exponent + upperExponent ps

-- Lower certificates can be generated from the actual prime's binary
-- width. This proof needs no primality, factorization or floating log.
theorem lower_power (ps : List Lane)
    (h : ∀ p ∈ ps, 2 ^ p.lower ≤ p.base) :
    2 ^ lowerExponent ps ≤ packed ps := by
  induction ps with
  | nil => simp [lowerExponent,packed]
  | cons p ps ih =>
    have hp := h p (by simp)
    have ht : ∀ q ∈ ps, 2 ^ q.lower ≤ q.base := by
      intro q hq
      exact h q (by simp [hq])
    simp only [lowerExponent,packed,pow_add,pow_mul]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hp _) (ih ht)

theorem upper_power (ps : List Lane)
    (h : ∀ p ∈ ps, p.base ≤ 2 ^ p.upper) :
    packed ps ≤ 2 ^ upperExponent ps := by
  induction ps with
  | nil => simp [upperExponent,packed]
  | cons p ps ih =>
    have hp := h p (by simp)
    have ht : ∀ q ∈ ps, q.base ≤ 2 ^ q.upper := by
      intro q hq
      exact h q (by simp [hq])
    simp only [upperExponent,packed,pow_add,pow_mul]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hp _) (ih ht)

-- If B binary cells represent the integer literally, its value must
-- be below 2^B. The lower certificate forces B strictly above the
-- summed exponent lower bound. This does not constrain compressed
-- representations or arbitrary standard-machine SAT deciders.
theorem literal_width (ps : List Lane) (B : Nat)
    (h : ∀ p ∈ ps, 2 ^ p.lower ≤ p.base)
    (fits : packed ps < 2^B) : lowerExponent ps < B := by
  by_contra hn
  have hb : B ≤ lowerExponent ps := Nat.le_of_not_gt hn
  have hp : (2 : Nat)^B ≤ 2^lowerExponent ps := by
    exact Nat.pow_le_pow_right (by decide) hb
  exact (Nat.not_lt_of_ge (hp.trans (lower_power ps h))) fits

-- The same numeric exponent has a compact binary exponent code while
-- a literal product lane at base >=2 needs more than exponent bits.
theorem single_lane_literal_width (p e B : Nat) (hp : 2 ≤ p)
    (fits : p^e < 2^B) : e < B := by
  have h := literal_width [⟨p,e,1,p⟩] B (by
    intro q hq
    simp only [List.mem_singleton] at hq
    subst q
    simpa using hp) (by simpa [packed] using fits)
  simpa [lowerExponent] using h

end PNPMaterializedValuationResource
