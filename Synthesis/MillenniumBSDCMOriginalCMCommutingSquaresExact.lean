import Synthesis.MillenniumBSDMathlibLFunctionWeld
import Synthesis.MillenniumBSDCMOriginalE32LiteralReductionGeometryExact
import Synthesis.MillenniumBSDCMActualLocalEulerPointCountBidiExact
import Integration.EisensteinJZeroPointCMExact
import Integration.EisensteinJZeroBadPrimeTwoExact
import Integration.EisensteinJZeroBadPrimeThreeExact
import Mathlib.Tactic

/-!
# Two ACTUAL commuting squares, not a fictional square between CM fields

Original owners, reused rather than rebuilt:
* Synthesis.MillenniumBSDMathlibLFunctionWeld.cmWeierstrass and cmLSeries
  for the selected E32 y²=x³-x (j=1728, Gaussian CM);
* Synthesis.MillenniumBSDCMActualLocalEulerPointCountBidiExact for
  the source E32 localEulerFactor-to-Frobenius reduction seam;
* original Agda classical S4 2-isogeny E32 -> E':y²=x³+4x;
* Integration.EisensteinJZeroPointCMExact.omegaPointEndomorphism on
  the EXISTING J+:y²=x³+1 curve (j=0, Eisenstein CM), and its
  original bad-prime 2 and 3 owners.

Square A, ORIGINAL BSD two-isogeny and dual:
    E32  --phi-->  E'
     |              |
    [2]          dual phi
     |              |
     v              v
    E32  --id-->  E32
On the nonexceptional affine chart,
phi(x,y)=(x-1/x,y*(1+1/x²)),
dualphi(X,Y)=((X+4/X)/4,Y*(1-4/X²)/8).
The existing S4 classical source owns the true rational isogeny;
this module proves CLEAR-DENOMINATOR POLYNOMIAL IDENTITIES
and chart naturality. An actual Lean group-point / multiplication-by-two
correspondence at infinity and torsion is NOT formalized here.

Square B, J+ and its -1 quadratic twist J- over a field K containing i:
     J+ --tau_i--> J-
      |             |
    C3 omega      C3 omega
      |             |
      v             v
     J+ --tau_i--> J-
tau_i(x,y)=(-x,i*y), i²=-1; the two paths agree.
This is SOURCE-COMPATIBLE with the existing J+ C3 endomorphism, but
does NOT replace its point-group proof or define a Q-isomorphism.
The necessary common coefficient field contains BOTH i and omega.

Frobenius refinement: on a good odd prime, Frobenius transports tau_i
to tau_(i^p). At p=1 mod4 it commutes, at p=3 mod4 it differs by
elliptic inversion. At bad primes 2 and 3, finite naive counts are NOT
local Euler factors. There is NO isogeny E32 <-> J+:
their geometric j invariants and rational CM endomorphism fields differ.

Native Lean/Mathlib 4.28 kernel NOT RUN; no new BSD or YM theorem.
-/

namespace Synthesis.Millennium.BSD

section UniversalClearedIsogeny
variable {R : Type*} [CommRing R]

/-- Exact universal numerator identity from original E32 to original
    classically 2-isogenous E': no division or new elliptic model. -/
theorem originalE32PhiClearedIdentity (x : R) :
    (x ^ 3 - x) * (x ^ 2 + 1) ^ 2 =
      x * ((x ^ 2 - 1) ^ 3 + 4 * (x ^ 2 - 1) * x ^ 2) := by
  ring

/-- The original curve's equation passes through the noncommutative-free
    chart identity BEFORE denominators are inverted. The genuine phi has
    denominators x and x² and is valid only on x≠0. -/
theorem originalE32PhiClearedEquation
    (x y : R) (h : y ^ 2 = x ^ 3 - x) :
    (y * (x ^ 2 + 1)) ^ 2 =
      x * ((x ^ 2 - 1) ^ 3 + 4 * (x ^ 2 - 1) * x ^ 2) := by
  calc
    (y * (x ^ 2 + 1)) ^ 2 =
        y ^ 2 * (x ^ 2 + 1) ^ 2 := by ring
    _ = (x ^ 3 - x) * (x ^ 2 + 1) ^ 2 := by rw [h]
    _ = x * ((x ^ 2 - 1) ^ 3 +
        4 * (x ^ 2 - 1) * x ^ 2) :=
      originalE32PhiClearedIdentity x

/-- Original dual 2-isogeny numerator identity, E': Y²=X³+4X
    back to E32, after the denominator 4X and 8X² is cleared. -/
theorem originalE32DualClearedIdentity (X : R) :
    (X ^ 3 + 4 * X) * (X ^ 2 - 4) ^ 2 =
      X * ((X ^ 2 + 4) ^ 3 -
        16 * X ^ 2 * (X ^ 2 + 4)) := by
  ring

theorem originalE32DualClearedEquation
    (X Y : R) (h : Y ^ 2 = X ^ 3 + 4 * X) :
    (Y * (X ^ 2 - 4)) ^ 2 =
      X * ((X ^ 2 + 4) ^ 3 -
        16 * X ^ 2 * (X ^ 2 + 4)) := by
  calc
    (Y * (X ^ 2 - 4)) ^ 2 =
        Y ^ 2 * (X ^ 2 - 4) ^ 2 := by ring
    _ = (X ^ 3 + 4 * X) * (X ^ 2 - 4) ^ 2 := by rw [h]
    _ = X * ((X ^ 2 + 4) ^ 3 -
        16 * X ^ 2 * (X ^ 2 + 4)) :=
      originalE32DualClearedIdentity X

/-- The numerator square commutes with EVERY ring homomorphism, hence
    under an actual prime-local reduction map on integral/unit charts.
    There is NO ring homomorphism Q -> Fp: reduction must pass through
    the original p-integral localization and x a unit. -/
theorem originalE32PhiNumeratorsNaturality
    {S : Type*} [CommRing S] (f : R →+* S) (x y : R) :
    f (x ^ 2 - 1) = (f x) ^ 2 - 1 ∧
    f (y * (x ^ 2 + 1)) = f y * ((f x) ^ 2 + 1) := by
  constructor <;> simp

/-- Composition of the two rational chart x-coordinate numerators.
    On x not 0, ±1, division gives
    (dualphi ∘ phi)_x=(x²+1)²/(4x(x²-1)), the original doubling chart. -/
theorem originalE32DualPhiDoubleXCleared (x : R) :
    (x ^ 2 - 1) ^ 2 + 4 * x ^ 2 = (x ^ 2 + 1) ^ 2 := by
  ring

/-- Exact chart y numerator of dualphi ∘ phi. The ordinary
    elliptic-curve chord-tangent doubling identity is an additional
    original point-group theorem, not silently inferred from this. -/
theorem originalE32DualPhiDoubleYCleared (x : R) :
    (x ^ 2 + 1) * ((x ^ 2 - 1) ^ 2 - 4 * x ^ 2) =
      (x ^ 2 + 1) * (x ^ 4 - 6 * x ^ 2 + 1) := by
  ring

end UniversalClearedIsogeny

section OriginalEisensteinTwist
variable {R : Type*} [CommRing R]

/-- The original j=0 +1 cubic transports to its -1 quadratic twist,
    over a ring containing a specified i with i²=-1. -/
theorem originalJPlusToJMinus
    (i x y : R) (hi : i ^ 2 = -1)
    (hplus : y ^ 2 = x ^ 3 + 1) :
    (i * y) ^ 2 = (-x) ^ 3 - 1 := by
  calc
    (i * y) ^ 2 = i ^ 2 * y ^ 2 := by ring
    _ = -(x ^ 3 + 1) := by rw [hi, hplus]; ring
    _ = (-x) ^ 3 - 1 := by ring

/-- Return from the -1 twist to the ORIGINAL +1 cubic.
    This is the inverse-coordinate map (-X,-iY). -/
theorem originalJMinusToJPlus
    (i X Y : R) (hi : i ^ 2 = -1)
    (hminus : Y ^ 2 = X ^ 3 - 1) :
    (-(i * Y)) ^ 2 = (-X) ^ 3 + 1 := by
  calc
    (-(i * Y)) ^ 2 = i ^ 2 * Y ^ 2 := by ring
    _ = -(X ^ 3 - 1) := by rw [hi, hminus]; ring
    _ = (-X) ^ 3 + 1 := by ring

/-- The forward and backward TWIST coordinate charts really are inverse.
    In contrast, the original E32 degree-two isogeny and its dual are not. -/
theorem originalJTwistCoordinateRoundTrip
    (i x y : R) (hi : i ^ 2 = -1) :
    (-(-x), -(i * (i * y))) = (x,y) := by
  apply Prod.ext
  · ring
  · calc
      -(i * (i * y)) = -(i ^ 2 * y) := by ring
      _ = y := by rw [hi]; ring

/-- The already-owned Eisenstein order-three action multiplies x by omega
    and leaves y fixed. It COMMUTES with the twist over a field containing
    BOTH i and omega. This is the actual C3-equivariant square at chart
    level; the original J+ point endomorphism is not reimplemented. -/
theorem originalJZeroC3TwistCommutingSquare
    (omega i x y : R) :
    (-(omega * x), i * y) = (omega * (-x), i * y) := by
  apply Prod.ext
  · ring
  · rfl

/-- The source C3 x-multiplication preserves the PLUS cubic when
    omega³=1. The original full group endomorphism is owned by
    Integration.EisensteinJZeroPointCMExact. -/
theorem originalJPlusC3Equation
    (omega x y : R) (homega : omega ^ 3 = 1)
    (h : y ^ 2 = x ^ 3 + 1) :
    y ^ 2 = (omega * x) ^ 3 + 1 := by
  rw [mul_pow, homega, one_mul]
  exact h

/-- The transported C3 action also preserves the MINUS twist cubic. -/
theorem originalJMinusC3Equation
    (omega X Y : R) (homega : omega ^ 3 = 1)
    (h : Y ^ 2 = X ^ 3 - 1) :
    Y ^ 2 = (omega * X) ^ 3 - 1 := by
  rw [mul_pow, homega, one_mul]
  exact h

/-- An arbitrary ring hom respects the two TWIST coordinates, but to
    preserve the isomorphism after reduction the chosen i must still map
    to a unit with square -1. Over inert p, i lives in F_(p²) and
    Frobenius(i)=-i; the square is sign-twisted. -/
theorem originalJTwistCoordinatesNaturality
    {S : Type*} [CommRing S] (f : R →+* S) (i x y : R) :
    f (-x) = -(f x) ∧ f (i * y) = f i * f y := by
  constructor <;> simp

end OriginalEisensteinTwist

end Synthesis.Millennium.BSD
