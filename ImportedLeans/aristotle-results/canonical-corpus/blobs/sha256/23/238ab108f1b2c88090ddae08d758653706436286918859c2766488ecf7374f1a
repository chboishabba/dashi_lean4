import Mathlib

/-!
# WorkbookData: the Monster / `j`-function trace data extracted from the workbook

This file extracts and re-verifies the genuine numeric dataset bundled in the
uploaded workbook archive (`…-aristotle (5).tar.gz`, files
`RequestProject/Main.lean` and `RequestProject/FullTable.lean`).  The data is the
per-prime breakdown of the McKay–Thompson class 1A coefficients (the `j`-function
coefficients, OEIS A000521) against the 15 supersingular primes dividing `|𝕄|`.

Everything here is re-proved from the transcribed data with `native_decide`, so
the file is a *verified* extraction rather than a bare transcription.  The
extracted pieces are:

* `ORDER` — the 15 supersingular primes (the primes dividing `|𝕄|`);
* `rows` — for each of the first 7 `j`-coefficients `y_j`, the exponent vector
  `ssp` such that `∏_k ORDER[k] ^ ssp[k]` is the supersingular reduction `temp_j`;
* `temp`, `total` — the running product per row and the accumulated grand total;
* `literalTable` — the full 105-row × 8-column trace table, with `genTable`
  reconstructing it from `ORDER` and `rows` and `full_table_eq_generated`
  proving the two agree cell-for-cell.
-/

namespace WorkbookData

/-! ## Core data -/

/-- The 15 primes dividing the order of the Monster group (the supersingular
primes), in the order used by the reference script (`ORDER`). -/
def ORDER : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

/-- The data rows: each entry is a pair `(y, ssp)` where `y` is the `j`-th
coefficient of the modular `j`-function (OEIS A000521 / McKay–Thompson class 1A)
and `ssp` is the corresponding row of exponents (15 entries, one per prime in
`ORDER`). -/
def rows : List (ℕ × List ℕ) :=
  [ (1,            [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]),
    (744,          [0,0,0,0,0,0,0,0,0,0,0,0,1,1,1]),
    (196884,       [2,0,0,0,0,0,0,0,0,0,1,1,0,1,1]),
    (21493760,     [1,0,0,0,0,2,0,0,0,1,1,0,1,1,0]),
    (864299970,    [2,0,0,1,1,0,0,0,1,1,1,1,0,0,1]),
    (20245856256,  [0,0,0,0,0,2,0,0,1,1,0,1,0,1,1]),
    (333202640600, [1,1,0,0,1,0,0,1,0,1,0,1,1,1,1]) ]

/-- The inner product of the script: `temp = ∏_k ORDER[k] ^ ssp[k]`. -/
def temp (ssp : List ℕ) : ℕ := (List.zipWith (fun p e => p ^ e) ORDER ssp).prod

/-- The accumulated total of the script: `total = 1 + Σ_j (temp_j * y_j)`. -/
def total : ℕ := 1 + (rows.map (fun ye => temp ye.2 * ye.1)).sum

/-! ## Basic sanity checks on the core data -/

/-- `ORDER` lists exactly 15 primes. -/
theorem ORDER_length : ORDER.length = 15 := by native_decide

/-- Every entry of `ORDER` is prime. -/
theorem ORDER_prime : ∀ p ∈ ORDER, Nat.Prime p := by decide

/-- There are 7 data rows, each with a 15-entry exponent vector. -/
theorem rows_shape : rows.length = 7 ∧ ∀ ye ∈ rows, ye.2.length = 15 := by
  native_decide

/-- The `j`-function coefficients recorded in `rows` are the genuine OEIS A000521
values `c(0..6)`. -/
theorem rows_coeffs :
    rows.map (·.1) =
      [1, 744, 196884, 21493760, 864299970, 20245856256, 333202640600] := by
  native_decide

/-- The reproduced value of `temp` for each row matches the trace's `temp` column. -/
theorem temp_values :
    rows.map (fun ye => temp ye.2) =
      [1, 196883, 21296876, 842609326, 18538750076, 19360062527, 293553734298] := by
  native_decide

/-- The final accumulated `total` for class 1A equals `98220881625283513136530`. -/
theorem total_eq : total = 98220881625283513136530 := by native_decide

/-! ## The full per-prime trace table -/

/-- Generate one block of the table for the `j`-th coefficient `y` with exponent
row `ssp`.  Produces 15 rows `[1, j, y, k, e, p, p^e, run]`, with `run` the
running product `∏_{i ≤ k} ORDER[i] ^ e_i`. -/
def genBlock (j y : ℕ) (ssp : List ℕ) : List (List ℕ) :=
  let pe := List.zipWith (fun p e => p ^ e) ORDER ssp
  let runs := (List.scanl (· * ·) 1 pe).tail
  let idx := List.range ssp.length
  List.zipWith (fun (t : ℕ × ℕ × ℕ) (rp : ℕ) =>
      [1, j, y, t.1, t.2.2, t.2.1, t.2.1 ^ t.2.2, rp])
    (List.zip idx (List.zip ORDER ssp)) runs

/-- The full generated table: concatenate the blocks for all rows, indexed by `j`. -/
def genTable : List (List ℕ) :=
  (List.zipWith (fun j ye => genBlock j ye.1 ye.2) (List.range rows.length) rows).flatten

/-- The literal table supplied in the workbook (105 rows × 8 columns), transcribed
verbatim. -/
def literalTable : List (List ℕ) :=
[[1,0,1,0,0,2,1,1],[1,0,1,1,0,3,1,1],[1,0,1,2,0,5,1,1],[1,0,1,3,0,7,1,1],[1,0,1,4,0,11,1,1],[1,0,1,5,0,13,1,1],[1,0,1,6,0,17,1,1],[1,0,1,7,0,19,1,1],[1,0,1,8,0,23,1,1],[1,0,1,9,0,29,1,1],[1,0,1,10,0,31,1,1],[1,0,1,11,0,41,1,1],[1,0,1,12,0,47,1,1],[1,0,1,13,0,59,1,1],[1,0,1,14,0,71,1,1],
[1,1,744,0,0,2,1,1],[1,1,744,1,0,3,1,1],[1,1,744,2,0,5,1,1],[1,1,744,3,0,7,1,1],[1,1,744,4,0,11,1,1],[1,1,744,5,0,13,1,1],[1,1,744,6,0,17,1,1],[1,1,744,7,0,19,1,1],[1,1,744,8,0,23,1,1],[1,1,744,9,0,29,1,1],[1,1,744,10,0,31,1,1],[1,1,744,11,0,41,1,1],[1,1,744,12,1,47,47,47],[1,1,744,13,1,59,59,2773],[1,1,744,14,1,71,71,196883],
[1,2,196884,0,2,2,4,4],[1,2,196884,1,0,3,1,4],[1,2,196884,2,0,5,1,4],[1,2,196884,3,0,7,1,4],[1,2,196884,4,0,11,1,4],[1,2,196884,5,0,13,1,4],[1,2,196884,6,0,17,1,4],[1,2,196884,7,0,19,1,4],[1,2,196884,8,0,23,1,4],[1,2,196884,9,0,29,1,4],[1,2,196884,10,1,31,31,124],[1,2,196884,11,1,41,41,5084],[1,2,196884,12,0,47,1,5084],[1,2,196884,13,1,59,59,299956],[1,2,196884,14,1,71,71,21296876],
[1,3,21493760,0,1,2,2,2],[1,3,21493760,1,0,3,1,2],[1,3,21493760,2,0,5,1,2],[1,3,21493760,3,0,7,1,2],[1,3,21493760,4,0,11,1,2],[1,3,21493760,5,2,13,169,338],[1,3,21493760,6,0,17,1,338],[1,3,21493760,7,0,19,1,338],[1,3,21493760,8,0,23,1,338],[1,3,21493760,9,1,29,29,9802],[1,3,21493760,10,1,31,31,303862],[1,3,21493760,11,0,41,1,303862],[1,3,21493760,12,1,47,47,14281514],[1,3,21493760,13,1,59,59,842609326],[1,3,21493760,14,0,71,1,842609326],
[1,4,864299970,0,2,2,4,4],[1,4,864299970,1,0,3,1,4],[1,4,864299970,2,0,5,1,4],[1,4,864299970,3,1,7,7,28],[1,4,864299970,4,1,11,11,308],[1,4,864299970,5,0,13,1,308],[1,4,864299970,6,0,17,1,308],[1,4,864299970,7,0,19,1,308],[1,4,864299970,8,1,23,23,7084],[1,4,864299970,9,1,29,29,205436],[1,4,864299970,10,1,31,31,6368516],[1,4,864299970,11,1,41,41,261109156],[1,4,864299970,12,0,47,1,261109156],[1,4,864299970,13,0,59,1,261109156],[1,4,864299970,14,1,71,71,18538750076],
[1,5,20245856256,0,0,2,1,1],[1,5,20245856256,1,0,3,1,1],[1,5,20245856256,2,0,5,1,1],[1,5,20245856256,3,0,7,1,1],[1,5,20245856256,4,0,11,1,1],[1,5,20245856256,5,2,13,169,169],[1,5,20245856256,6,0,17,1,169],[1,5,20245856256,7,0,19,1,169],[1,5,20245856256,8,1,23,23,3887],[1,5,20245856256,9,1,29,29,112723],[1,5,20245856256,10,0,31,1,112723],[1,5,20245856256,11,1,41,41,4621643],[1,5,20245856256,12,0,47,1,4621643],[1,5,20245856256,13,1,59,59,272676937],[1,5,20245856256,14,1,71,71,19360062527],
[1,6,333202640600,0,1,2,2,2],[1,6,333202640600,1,1,3,3,6],[1,6,333202640600,2,0,5,1,6],[1,6,333202640600,3,0,7,1,6],[1,6,333202640600,4,1,11,11,66],[1,6,333202640600,5,0,13,1,66],[1,6,333202640600,6,0,17,1,66],[1,6,333202640600,7,1,19,19,1254],[1,6,333202640600,8,0,23,1,1254],[1,6,333202640600,9,1,29,29,36366],[1,6,333202640600,10,0,31,1,36366],[1,6,333202640600,11,1,41,41,1491006],[1,6,333202640600,12,1,47,47,70077282],[1,6,333202640600,13,1,59,59,4134559638],[1,6,333202640600,14,1,71,71,293553734298]]

/-- The supplied table has 105 rows. -/
theorem literalTable_length : literalTable.length = 105 := by native_decide

/-- **Main check.**  The full literal table supplied in the workbook is *exactly*
the table generated from `ORDER` and `rows` by the documented algorithm.  This
verifies every one of the 105 rows and all eight columns: the constant `1`, the
`j`/`y_j` indexing, the prime `p = ORDER[k]`, the exponent `e = rows[j].2[k]`,
the prime power `p^e`, and the running product. -/
theorem full_table_eq_generated : genTable = literalTable := by native_decide

/-- Column consistency: in every row, the seventh entry (`p^e`) really is the
sixth entry (`p`) raised to the fifth entry (`e`). -/
theorem full_table_power_column :
    ∀ r ∈ literalTable, r[6]! = r[5]! ^ r[4]! := by native_decide

/-- The first column of every row is the constant `1`. -/
theorem full_table_first_column :
    ∀ r ∈ literalTable, r[0]! = 1 := by native_decide

/-- The running product reached at the end of each block (`k = 14`) agrees with
`temp` for that row, so the table is consistent with the `temp` computation. -/
theorem full_table_running_product_eq_temp :
    (List.range rows.length).map (fun j => (literalTable[15 * j + 14]!)[7]!)
      = rows.map (fun ye => temp ye.2) := by native_decide

/-- Combined with `temp_values`, the final running products are the expected
`temp` column. -/
theorem full_table_running_product_values :
    (List.range rows.length).map (fun j => (literalTable[15 * j + 14]!)[7]!)
      = [1, 196883, 21296876, 842609326, 18538750076, 19360062527, 293553734298] := by
  native_decide

/-! ## Tie-in to the dual atlas

The structured prime powers `2^46, 3^20, 5^9, 7^6, 11^2, 13^3` that the dual
atlas dualizes are exactly the first six entries of `ORDER` carrying the high
exponents in `|𝕄| = 2^46·3^20·5^9·7^6·11^2·13^3·17·19·23·29·31·41·47·59·71`. -/

/-- The six structured prime bases of the dual atlas are the first six entries
of `ORDER`. -/
theorem dualAtlas_bases_in_ORDER :
    ORDER.take 6 = [2, 3, 5, 7, 11, 13] := by native_decide

/-- The full Monster order, reconstructed from `ORDER` with the exponent vector
`[46,20,9,6,2,3,1,1,1,1,1,1,1,1,1]`, is `|𝕄|`. -/
theorem monsterOrder_from_ORDER :
    temp [46,20,9,6,2,3,1,1,1,1,1,1,1,1,1]
      = 808017424794512875886459904961710757005754368000000000 := by
  native_decide

end WorkbookData
