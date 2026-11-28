import Mathlib
import Welds.PNPCookAffineSeekExact

namespace PNPCookAffineSeek

-- Twice the original triangular affine prefix, so there is no
-- rounding ambiguity at the square-root inverse.
def twicePrefix (a c j : ℤ) : ℤ := a*j*(j-1)+2*c*j

theorem discriminant_identity (a c j k : ℤ) :
    (2*a*j+(2*c-a))^2 - ((2*c-a)^2+8*a*k) =
      4*a*(twicePrefix a c j-2*k) := by
  unfold twicePrefix
  ring

-- Exact integer certificate of floor quadratic inverse. The executable
-- digitwise sqrt supplies d^2<=D<(d+1)^2; integer division supplies
-- the two quotient inequalities. No real-number rounding needed.
theorem quadratic_inverse (a c j k d : ℤ)
    (ha : 0<a) (hc : 0<c) (hj : 0≤j) (hk : 0≤k) (hd : 0≤d)
    (hs : d^2≤(2*c-a)^2+8*a*k)
    (ht : (2*c-a)^2+8*a*k<(d+1)^2)
    (hl : 2*a*j+(2*c-a)≤d)
    (hu : d<2*a*(j+1)+(2*c-a)) :
    twicePrefix a c j≤2*k ∧ 2*k<twicePrefix a c (j+1) := by
  have hupper : d+1≤2*a*(j+1)+(2*c-a) := by omega
  have hpos : 0≤2*a*(j+1)+(2*c-a) := by
    nlinarith [mul_nonneg ha.le hj]
  have hh : (d+1)^2≤(2*a*(j+1)+(2*c-a))^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hupper)
      (show 0≤(2*a*(j+1)+(2*c-a))+(d+1) by linarith)]
  have u := discriminant_identity a c (j+1) k
  have upl : 0 < 4*a*(twicePrefix a c (j+1)-2*k) := by linarith
  have up : 2*k<twicePrefix a c (j+1) := by
    have hh' := (mul_pos_iff.mp upl)
    rcases hh' with h | h
    · omega
    · linarith [h.1]
  refine ⟨?_,up⟩
  by_cases hz : j=0
  · simp [twicePrefix,hz]; omega
  have hj' : 1≤j := by omega
  have hp : 0≤2*a*j+(2*c-a) := by
    nlinarith [mul_nonneg ha.le (show 0≤j-1 by omega)]
  have hsq : (2*a*j+(2*c-a))^2≤d^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl)
      (show 0≤d+(2*a*j+(2*c-a)) by linarith)]
  have e := discriminant_identity a c j k
  by_contra h
  have h' : 0<4*a*(twicePrefix a c j-2*k) :=
    mul_pos (by positivity) (by omega)
  linarith

theorem initial_one_correction (p k z : ℤ)
    (hp : 1≤p) (hz : 0≤z ∧ z≤p-1)
    (hl : twicePrefix 1 5 p≤2*k) :
    twicePrefix 1 5 (p-1)+2*z≤2*k := by
  unfold twicePrefix at *
  nlinarith

-- Conservative arithmetic model for fixed templates:
-- digitwise sqrt: <= b rounds, each <= c*b bit operations.
-- Fixed number of grade-school multiplication/division operations.
-- Indexed immutable pattern access is a separate charged premise.
theorem arithmetic_clock (b c muls reads total : Nat)
    (sqrtCost : Nat) (hs : sqrtCost ≤ c*b*b)
    (ht : total ≤ sqrtCost + muls*b*b+reads) :
    total ≤ (c+muls)*b*b+reads := by
  calc
    total ≤ sqrtCost+muls*b*b+reads := ht
    _ ≤ c*b*b+muls*b*b+reads := by omega
    _ = (c+muls)*b*b+reads := by ring

-- Many individually sublinear queries need not fit T. The actual count
-- and all non-query terms still enter the same-target closure.
theorem repeated_query_necessary (T Q per overhead : Nat)
    (h : Q*per+overhead≤T) : Q*per≤T := by omega

end PNPCookAffineSeek
