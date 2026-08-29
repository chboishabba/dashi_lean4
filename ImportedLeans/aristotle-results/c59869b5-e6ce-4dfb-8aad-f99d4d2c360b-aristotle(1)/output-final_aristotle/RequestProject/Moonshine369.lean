import Mathlib
import RequestProject.Tesla369
import RequestProject.DeltaGraph

/-!
# 3, 6, 9 in moonshine: Klein's `j`, and the McKay–Thompson series of classes 1A, 2A, 3A

The earlier files of this project read the digital-root trinity `{3, 6, 9}` off the coefficients
of the discriminant `Δ = q ∏ (1 - qⁿ)²⁴` (`DeltaGraph.digitalRoot_tau_table`: every third `τ`
has digital root nine).  This file does the same for the *hauptmoduls*:

* Klein's `j = E₄³/Δ = q⁻¹ + 744 + 196884 q + 21493760 q² + ⋯` (OEIS A000521), whose
  coefficients are the graded dimensions of the moonshine module;
* the McKay–Thompson series of class **2A**, given by the standard eta quotient
  `T₂ = (η(z)/η(2z))²⁴ + 2¹² (η(2z)/η(z))²⁴ + 24 = q⁻¹ + 4372 q + 96256 q² + ⋯`;
* the McKay–Thompson series of class **3A**, `T₃ = (η(z)/η(3z))¹² + 3⁶ (η(3z)/η(z))¹² + 12
  = q⁻¹ + 783 q + 8672 q² + ⋯`.

Everything is computed from the `q`-expansions as truncated integer power series, exactly as
`DeltaGraph.tau` is, and every table below is a kernel computation (`by decide`).

## What is found

* `jCoeff_table`, `T2_table`, `T3_table` — the coefficients, matching the published values.
* `three_pow_five_dvd_jCoeff_three_mul` — **every third coefficient of `j` is divisible by
  `3⁵ = 243`** (Lehner's congruence, verified here on the computed range), so
  `digitalRoot_jCoeff_three_mul`: its digital root is `9`.  The same happens for the class 2A
  and 3A series (`digitalRoot_T2_three_mul`, `digitalRoot_T3_three_mul`), and it is what
  `DeltaGraph.digitalRoot_tau_table` shows for `Δ`: on the multiples of three, all four series
  are in the trinity.
* `jCoeff_congr_T3_mod_729` — **`j` and the class 3A series agree modulo `3⁶ = 729`** on the
  computed range, hence `digitalRoot_jCoeff_eq_T3`: they have *exactly the same digital roots*.
  Three sees no difference between `j` and its 3A shadow.
* `jCoeff_congr_T2_mod_4096` — the class 2A series is the two-adic analogue: it agrees with `j`
  modulo `2¹² = 4096`, and `digitalRoot_T2_ne_jCoeff` shows its digital roots are *not* those of
  `j`.  Two and three split the moonshine picture, and the trinity belongs to three.
* `two_pow_eleven_dvd_jCoeff_two_mul` — the two-adic companion congruence, `2¹¹ ∣ c(2n)`.

All statements are verified on the range computed here, not proved for all `n`; the file says so
in each docstring.
-/

namespace Moonshine369

set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-! ## Truncated integer power series

A series is a list of coefficients, lowest degree first; all operations truncate to the length
of their first argument. -/

/-- Multiply by `q ^ k`, truncating back to the original length. -/
def shiftBy (k : ℕ) (p : List ℤ) : List ℤ := (List.replicate k 0 ++ p).take p.length

/-- Coefficientwise sum. -/
def addL (p q : List ℤ) : List ℤ := List.zipWith (· + ·) p q

/-- Multiply by `1 - q ^ n`. -/
def mulOneSub (n : ℕ) (p : List ℤ) : List ℤ := List.zipWith (· - ·) p (shiftBy n p)

/-- Divide by `1 - q ^ n`, i.e. multiply by `1 + qⁿ + q²ⁿ + ⋯`.  Six doubling steps give the
geometric series up to `q^(63n)`, which is beyond every truncation used in this file. -/
def divOneSub (n : ℕ) (p : List ℤ) : List ℤ :=
  (List.range 6).foldl (fun s i => addL s (shiftBy (n * 2 ^ i) s)) p

/-- Cauchy product, truncated to the length of `p`. -/
def mulT (p q : List ℤ) : List ℤ :=
  (List.range p.length).map fun k =>
    ((List.range (k + 1)).map (fun i => p.getD i 0 * q.getD (k - i) 0)).sum

/-- The constant series `1`, of length `N`. -/
def one (N : ℕ) : List ℤ := (List.range N).map fun k => if k = 0 then 1 else 0

/-- Raise `1 - q ^ n` to the `e`-th power inside a series. -/
def mulOneSubPow (n e : ℕ) (p : List ℤ) : List ℤ :=
  (List.replicate e ()).foldl (fun q _ => mulOneSub n q) p

/-- Divide by `(1 - q ^ n) ^ e`. -/
def divOneSubPow (n e : ℕ) (p : List ℤ) : List ℤ :=
  (List.replicate e ()).foldl (fun q _ => divOneSub n q) p

/-! ## Klein's `j` -/

/-- `σ₃ n = ∑_{d ∣ n} d³`. -/
def sigma3 (n : ℕ) : ℤ :=
  ((List.range' 1 n).filter (fun d => n % d = 0)).foldl (fun s d => s + (d : ℤ) ^ 3) 0

/-- The Eisenstein series `E₄ = 1 + 240 ∑_{n ≥ 1} σ₃(n) qⁿ`, truncated to `N` terms. -/
def E4 (N : ℕ) : List ℤ := (List.range N).map fun k => if k = 0 then 1 else 240 * sigma3 k

/-- `∏_{n = 1}^{N} (1 - qⁿ)^{-24}`, i.e. `q/Δ`, truncated to `N` terms. -/
def invEta24 (N : ℕ) : List ℤ :=
  (List.range' 1 N).foldl (fun p n => divOneSubPow n 24 p) (one N)

/-- `q·j = E₄³ · (q/Δ)`, truncated to `N` terms; the coefficient of `q^(m+1)` here is the
coefficient of `q^m` in `j`. -/
def jSeries (N : ℕ) : List ℤ := mulT (mulT (mulT (E4 N) (E4 N)) (E4 N)) (invEta24 N)

/-- **The coefficients of Klein's `j`.** `jCoeff n` is the coefficient of `qⁿ` in
`j = E₄³/Δ = q⁻¹ + 744 + 196884 q + ⋯`.  Only the factors `1 - qᵐ` with `m ≤ n + 1` can affect
it, so truncating at `N = n + 2` is harmless. -/
def jCoeff (n : ℕ) : ℤ := (jSeries (n + 2)).getD (n + 1) 0

/-- The polar coefficient: `j` begins with `q⁻¹`. -/
def jCoeffNegOne : ℤ := (jSeries 2).getD 0 0

theorem jCoeffNegOne_eq : jCoeffNegOne = 1 := by decide

/-- **The `j`-coefficients** (OEIS A000521): `744, 196884, 21493760, 864299970, …`. -/
theorem jCoeff_table :
    (List.range 13).map jCoeff =
      [744, 196884, 21493760, 864299970, 20245856256, 333202640600, 4252023300096,
        44656994071935, 401490886656000, 3176440229784420, 22567393309593600,
        146211911499519294, 874313719685775360] := by decide

/-- The McKay–Thompson series of **class 1A** is `j - 744`: the same coefficients with the
constant term removed. -/
def T1 (n : ℕ) : ℤ := if n = 0 then 0 else jCoeff n

theorem T1_table :
    (List.range' 1 12).map T1 =
      [196884, 21493760, 864299970, 20245856256, 333202640600, 4252023300096,
        44656994071935, 401490886656000, 3176440229784420, 22567393309593600,
        146211911499519294, 874313719685775360] := by decide

/-! ## Class 2A -/

/-- `∏_{n < N, n odd} (1 - qⁿ)²⁴ = (η(z)/η(2z))²⁴ · q`, truncated to `N` terms. -/
def oddProd24 (N : ℕ) : List ℤ :=
  ((List.range' 1 N).filter (fun n => n % 2 = 1)).foldl (fun p n => mulOneSubPow n 24 p) (one N)

/-- The reciprocal of `oddProd24`. -/
def invOddProd24 (N : ℕ) : List ℤ :=
  ((List.range' 1 N).filter (fun n => n % 2 = 1)).foldl (fun p n => divOneSubPow n 24 p) (one N)

/-- **The McKay–Thompson series of class 2A**,
`T₂ = (η(z)/η(2z))²⁴ + 2¹² (η(2z)/η(z))²⁴ + 24 = q⁻¹ + 0 + 4372 q + 96256 q² + ⋯`;
`T2 n` is the coefficient of `qⁿ`. -/
def T2 (n : ℕ) : ℤ :=
  if n = 0 then (oddProd24 2).getD 1 0 + 24
  else (oddProd24 (n + 2)).getD (n + 1) 0 + 4096 * (invOddProd24 (n + 2)).getD (n - 1) 0

/-- The class 2A series is normalised: its constant term is zero. -/
theorem T2_zero : T2 0 = 0 := by decide

/-- **The class 2A coefficients**: `4372, 96256, 1240002, 10698752, …`. -/
theorem T2_table :
    (List.range' 1 12).map T2 =
      [4372, 96256, 1240002, 10698752, 74428120, 431529984, 2206741887, 10117578752,
        42616961892, 166564106240, 611800208702, 2125795885056] := by decide

/-! ## Class 3A -/

/-- `∏_{n < N, 3 ∤ n} (1 - qⁿ)¹² = (η(z)/η(3z))¹² · q`, truncated to `N` terms. -/
def coprime3Prod12 (N : ℕ) : List ℤ :=
  ((List.range' 1 N).filter (fun n => n % 3 ≠ 0)).foldl (fun p n => mulOneSubPow n 12 p) (one N)

/-- The reciprocal of `coprime3Prod12`. -/
def invCoprime3Prod12 (N : ℕ) : List ℤ :=
  ((List.range' 1 N).filter (fun n => n % 3 ≠ 0)).foldl (fun p n => divOneSubPow n 12 p) (one N)

/-- **The McKay–Thompson series of class 3A**,
`T₃ = (η(z)/η(3z))¹² + 3⁶ (η(3z)/η(z))¹² + 12 = q⁻¹ + 0 + 783 q + 8672 q² + ⋯`;
`T3 n` is the coefficient of `qⁿ`. -/
def T3 (n : ℕ) : ℤ :=
  if n = 0 then (coprime3Prod12 2).getD 1 0 + 12
  else (coprime3Prod12 (n + 2)).getD (n + 1) 0 + 729 * (invCoprime3Prod12 (n + 2)).getD (n - 1) 0

/-- The class 3A series is normalised: its constant term is zero. -/
theorem T3_zero : T3 0 = 0 := by decide

/-- **The class 3A coefficients**: `783, 8672, 65367, 371520, …`. -/
theorem T3_table :
    (List.range' 1 12).map T3 =
      [783, 8672, 65367, 371520, 1741655, 7161696, 26567946, 90521472, 288078201,
        864924480, 2469235686, 6748494912] := by decide

/-! ## The trinity in the coefficients -/

/-- The digital root of a coefficient, as in `DeltaGraph`. -/
def dr (m : ℤ) : ℕ := Tesla369.digitalRoot m.natAbs

/-- **Lehner's three-adic congruence, on the computed range.** Every third coefficient of `j` is
divisible by `3⁵ = 243`. -/
theorem three_pow_five_dvd_jCoeff_three_mul :
    ∀ n ∈ Finset.Icc 1 4, ((3 : ℤ) ^ 5) ∣ jCoeff (3 * n) := by decide

/-- **Lehner's two-adic congruence, on the computed range.** Every second coefficient of `j` is
divisible by `2¹¹ = 2048`. -/
theorem two_pow_eleven_dvd_jCoeff_two_mul :
    ∀ n ∈ Finset.Icc 1 6, ((2 : ℤ) ^ 11) ∣ jCoeff (2 * n) := by decide

/-- The digital roots of the `j`-coefficients `c(1), …, c(12)`. -/
theorem digitalRoot_jCoeff_table :
    (List.range' 1 12).map (fun n => dr (jCoeff n)) =
      [9, 5, 9, 9, 2, 9, 9, 3, 9, 9, 6, 9] := by decide

/-- The digital roots of the class 2A coefficients. -/
theorem digitalRoot_T2_table :
    (List.range' 1 12).map (fun n => dr (T2 n)) = [7, 1, 9, 2, 1, 9, 9, 8, 9, 5, 8, 9] := by decide

/-- The digital roots of the class 3A coefficients. -/
theorem digitalRoot_T3_table :
    (List.range' 1 12).map (fun n => dr (T3 n)) = [9, 5, 9, 9, 2, 9, 9, 3, 9, 9, 6, 9] := by decide

/-- **The trinity on the multiples of three, for `j`.** -/
theorem digitalRoot_jCoeff_three_mul :
    ∀ n ∈ Finset.Icc 1 4, dr (jCoeff (3 * n)) = 9 := by decide

/-- **The trinity on the multiples of three, for class 2A.** -/
theorem digitalRoot_T2_three_mul : ∀ n ∈ Finset.Icc 1 4, dr (T2 (3 * n)) = 9 := by decide

/-- **The trinity on the multiples of three, for class 3A.** -/
theorem digitalRoot_T3_three_mul : ∀ n ∈ Finset.Icc 1 4, dr (T3 (3 * n)) = 9 := by decide

/-- **The trinity on the multiples of three, for `Δ`** — the same phenomenon for the
discriminant, read off `DeltaGraph.tau`. -/
theorem digitalRoot_tau_three_mul :
    ∀ n ∈ Finset.Icc 1 10, Tesla369.digitalRoot (DeltaGraph.tau (3 * n)).natAbs = 9 := by decide

/-! ## `j` against its 2A and 3A shadows -/

/-- **`j` and the class 3A series agree modulo `3⁶ = 729`**, on the computed range. -/
theorem jCoeff_congr_T3_mod_729 :
    ∀ n ∈ Finset.Icc 1 12, (729 : ℤ) ∣ jCoeff n - T3 n := by decide

/-- **Hence the same digital roots.** Three cannot tell `j` from its 3A shadow. -/
theorem digitalRoot_jCoeff_eq_T3 : ∀ n ∈ Finset.Icc 1 12, dr (jCoeff n) = dr (T3 n) := by decide

/-- **`j` and the class 2A series agree modulo `2¹² = 4096`**, on the computed range: the
two-adic analogue of the previous congruence. -/
theorem jCoeff_congr_T2_mod_4096 :
    ∀ n ∈ Finset.Icc 1 12, (4096 : ℤ) ∣ jCoeff n - T2 n := by decide

/-- **But not the same digital roots.** The class 2A series parts company with `j` already at
the first coefficient: `4372` has digital root `7`, `196884` has digital root `9`. -/
theorem digitalRoot_T2_ne_jCoeff : dr (T2 1) ≠ dr (jCoeff 1) := by decide

/-- The congruence forces the digital roots to agree: two positive integers congruent mod `9`
have the same digital root.  This is why `jCoeff_congr_T3_mod_729` implies
`digitalRoot_jCoeff_eq_T3`. -/
theorem dr_eq_of_mod_nine {a b : ℤ} (ha : 0 < a) (hb : 0 < b) (hab : (9 : ℤ) ∣ a - b) :
    dr a = dr b := by
  refine Tesla369.digitalRoot_congr (Nat.modEq_iff_dvd.mpr ?_) ?_
  · rw [Int.natAbs_of_nonneg ha.le, Int.natAbs_of_nonneg hb.le]
    exact dvd_sub_comm.mp hab
  · simp [Int.natAbs_eq_zero, ha.ne', hb.ne']

end Moonshine369
