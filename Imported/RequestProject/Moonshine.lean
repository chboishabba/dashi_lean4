import Lean

/-!
# Moonshine: the 194 Monster irreps and the q-expansion of the j-invariant

This layer supplies the *key* for the moonshine flip-book (`MoonshineSVG`): the
genuine q-expansion of Klein's modular invariant `j`, and the projection of a
declaration's reflected hash into the **194 irreducible representations** of the
Monster group `𝕄` (the Monster has exactly 194 conjugacy classes, hence 194
complex irreducible representations).

## What is actually computed here

`j` is computed honestly as a truncated integer power series, from first
principles:

* `e4`  — the Eisenstein series `E₄ = 1 + 240 Σ σ₃(n) qⁿ`.
* `etaProd` — `∏_{n≥1} (1 - qⁿ)²⁴ = Δ / q`, the discriminant divided by `q`.
* `jSeries = E₄³ · (etaProd)⁻¹`, whose coefficient of `qᵐ` is the coefficient of
  `q^{m-1}` in `j`.  Thus `jSeries[0] = 1` (the `q⁻¹` term), `jSeries[1] = 744`,
  `jSeries[2] = 196884`, `jSeries[3] = 21493760`, …

The first coefficients match the classical values, and the famous **Monstrous
Moonshine head-character identities** (McKay's observation) are recorded as
*proved* theorems:

* `moonshine_c1 : 196884 = 1 + 196883`
* `moonshine_c2 : 21493760 = 1 + 196883 + 21296876`
* `moonshine_c3 : 864299970 = 2*1 + 2*196883 + 21296876 + 842609326`

where `1, 196883, 21296876, 842609326, …` are the smallest degrees of the 194
Monster irreps.

## Projection of an atom into the 194 irreps

`irrepOf h` sends a reflected declaration hash to its primary irrep index
`h % 194`; `irrepRot h rot` is the rotated index used to animate the *view* as
the flip-book turns (the rotation `rot` is read from the `j`-coefficient that
keys each page).
-/

namespace Moonshine

/-! ## Truncated integer power series -/

/-- Number of retained terms (`q⁰ … q^{N-1}`).  We need the `q⁻¹ … q¹⁰³` range of
`j`, i.e. `jSeries[0 … 104]`, so `N = 120` is comfortably enough. -/
def N : Nat := 120

/-- The all-zero series. -/
def zeros : Array Int := Array.replicate N 0

/-- The constant series `1`. -/
def psOne : Array Int := zeros.set! 0 1

/-- Truncated multiplication of two power series. -/
def psMul (a b : Array Int) : Array Int := Id.run do
  let mut r : Array Int := zeros
  for i in [0:N] do
    let ai := a[i]!
    if ai != 0 then
      for j in [0:N-i] do
        r := r.set! (i+j) (r[i+j]! + ai * b[j]!)
  return r

/-- Truncated `n`-th power of a power series. -/
def psPow (a : Array Int) (n : Nat) : Array Int := Id.run do
  let mut r := psOne
  for _ in [0:n] do
    r := psMul r a
  return r

/-- Truncated multiplicative inverse of a series with constant term `1`. -/
def psInv (a : Array Int) : Array Int := Id.run do
  let mut b : Array Int := zeros
  b := b.set! 0 1
  for n in [1:N] do
    let mut s : Int := 0
    for k in [1:n+1] do
      s := s + a[k]! * b[n-k]!
    b := b.set! n (-s)
  return b

/-! ## The Eisenstein series, the discriminant, and `j` -/

/-- `σ₃(n)` — the sum of the cubes of the divisors of `n`. -/
def sigma3 (n : Nat) : Int := Id.run do
  let mut s : Int := 0
  for d in [1:n+1] do
    if n % d == 0 then s := s + (Int.ofNat d)^3
  return s

/-- The Eisenstein series `E₄ = 1 + 240 Σ_{n≥1} σ₃(n) qⁿ`. -/
def e4 : Array Int := Id.run do
  let mut r : Array Int := zeros
  r := r.set! 0 1
  for n in [1:N] do
    r := r.set! n (240 * sigma3 n)
  return r

/-- `∏_{n≥1} (1 - qⁿ)²⁴ = Δ / q`, the modular discriminant divided by `q`. -/
def etaProd : Array Int := Id.run do
  let mut r := psOne
  for n in [1:N] do
    let mut f : Array Int := zeros
    f := f.set! 0 1
    if n < N then f := f.set! n (-1)
    for _ in [0:24] do
      r := psMul r f
  return r

/-- The q-expansion of `j`, shifted by one: `jSeries[m]` is the coefficient of
`q^{m-1}` in `j = E₄³ / Δ`.  In particular `jSeries[0] = 1` (the `q⁻¹` term),
`jSeries[1] = 744`, `jSeries[2] = 196884`, … -/
def jSeries : Array Int := psMul (psPow e4 3) (psInv etaProd)

/-- The coefficient of `qⁿ` in `j`, for `n ≥ -1` given as `n = idx - 1`.
`jCoeff 0 = 1` (the `q⁻¹` term), `jCoeff 1 = 744`, `jCoeff 2 = 196884`, … -/
def jCoeff (idx : Nat) : Int := jSeries[idx]!

/-! ## The first classical coefficients (verified) -/

theorem jc0 : jCoeff 0 = 1 := by native_decide
theorem jc1 : jCoeff 1 = 744 := by native_decide
theorem jc2 : jCoeff 2 = 196884 := by native_decide
theorem jc3 : jCoeff 3 = 21493760 := by native_decide
theorem jc4 : jCoeff 4 = 864299970 := by native_decide
theorem jc5 : jCoeff 5 = 20245856256 := by native_decide

/-! ## The Monster irreps and the moonshine head identities -/

/-- The number of irreducible representations of the Monster group, equal to its
number of conjugacy classes. -/
def numIrreps : Nat := 194

/-- The smallest degrees of the Monster's irreducible representations, in
increasing order (the leading entries of the 194-element degree sequence). -/
def smallIrrepDegrees : List Nat :=
  [1, 196883, 21296876, 842609326, 18538750076, 19360062527, 293553734298]

/-- **Monstrous Moonshine, level 1** (McKay's `196884 = 196883 + 1`): the
coefficient of `q¹` in `j` is the sum of the two smallest Monster irrep degrees. -/
theorem moonshine_c1 : jCoeff 2 = 1 + 196883 := by native_decide

/-- **Monstrous Moonshine, level 2**: the coefficient of `q²` in `j` decomposes
over the three smallest Monster irrep degrees. -/
theorem moonshine_c2 : jCoeff 3 = 1 + 196883 + 21296876 := by native_decide

/-- **Monstrous Moonshine, level 3**: the coefficient of `q³` in `j` decomposes
over the four smallest Monster irrep degrees with multiplicities `(2,2,1,1)`. -/
theorem moonshine_c3 :
    jCoeff 4 = 2 * 1 + 2 * 196883 + 21296876 + 842609326 := by native_decide

/-! ## Projection of an atom (declaration hash) into the 194 irreps -/

/-- The primary irrep an atom lands in: `h mod 194`. -/
def irrepOf (h : Nat) : Nat := h % numIrreps

/-- The irrep an atom occupies once the flip-book view has rotated by `rot`
(`rot` is derived from the `j`-coefficient that keys each page). -/
def irrepRot (h rot : Nat) : Nat := (h + rot) % numIrreps

/-- The rotation a page applies to the irrep wheel, read from the `j`-coefficient
keying that page (its residue mod 194). -/
def pageRot (idx : Nat) : Nat := ((jCoeff idx).emod (Int.ofNat numIrreps)).toNat

end Moonshine
