import RequestProject.DualFailureCensus
import RequestProject.Visualization

/-!
# Act VII — the pivot ladder: how many dual failures below `M`

The seventh panel of the twist series, `svg/twist-7-pivot-ladder.svg`.  Act VI stopped at
`q = 1824`, where `729 = 3⁶` is the only size at which *both* canonical maps onto the prime
subfield are broken.  This panel continues the scan on a logarithmic axis up to `10¹²` and
shows the whole ladder of such **dual failures**, together with the count below each of the
bounds `10³, 10⁶, 10⁹, 10¹²`.

Everything drawn is pinned to the theorems of `RequestProject/DualFailureCensus.lean`:

* `pivots_correct` — the seven drawn rungs are *exactly* the dual failures of size at most
  `10¹²` (`DualDial.census_1e12`);
* the running counts `1, 2, 4, 7` drawn at the four bounds are the theorems
  `DualDial.census_1e3`, `census_1e6`, `census_1e9`, `census_1e12`, and for `10¹²` also the
  prime-by-prime split `4 + 2 + 1` of `DualDial.count_1e12_split`;
* the classification `k = m·p` with `m ≢ 1 (mod p-1)` is `DualDial.isDualFailure_iff`, and the
  bottom rung `729` is least by `DualDial.min_size`.
-/

namespace PivotViz

open SvgCore

private def gold : String := "#b45309"
private def violet : String := "#7c3aed"
private def slate : String := "#334155"

/-! ## The drawn data -/

/-- The dual failures of size at most `10¹²`, as pairs `(p, k)` in increasing order of `p^k`. -/
def pivots : List (ℕ × ℕ) :=
  [(3, 6), (3, 12), (5, 10), (3, 18), (5, 15), (3, 24), (7, 14)]

/-- **The drawn rungs are exactly the dual failures below `10¹²`.** -/
theorem pivots_correct (p k : ℕ) :
    (DualDial.IsDualFailure p k ∧ p ^ k ≤ 10 ^ 12) ↔ (p, k) ∈ pivots := by
  rw [DualDial.census_1e12]
  constructor <;> (intro h; fin_cases h <;> decide)

/-- The rungs are drawn in increasing order of size. -/
theorem pivots_sorted :
    (pivots.map fun pk => pk.1 ^ pk.2) =
      [729, 531441, 9765625, 387420489, 30517578125, 282429536481, 678223072849] := by
  decide +kernel

/-! ## Geometry -/

private def baseY : Float := 372.0

/-- Position on the logarithmic axis, from `10²` on the left to `10¹³` on the right. -/
private def xOf (q : ℕ) : Float :=
  let l := Float.log10 q.toFloat
  80.0 + (l - 2.0) * (1120.0 / 11.0)

private def xOfPow (e : Float) : Float := 80.0 + (e - 2.0) * (1120.0 / 11.0)

private def sup (k : ℕ) : String :=
  let digit (d : ℕ) : String :=
    if d == 0 then "⁰" else if d == 1 then "¹" else if d == 2 then "²" else
    if d == 3 then "³" else if d == 4 then "⁴" else if d == 5 then "⁵" else
    if d == 6 then "⁶" else if d == 7 then "⁷" else if d == 8 then "⁸" else "⁹"
  if k < 10 then digit k else digit (k / 10) ++ digit (k % 10)

/-- The decade grid, `10²` … `10¹³`. -/
private def decades : List String :=
  (List.range 12).flatMap fun i =>
    let e := (i + 2).toFloat
    let x := xOfPow e
    [ line x (baseY - 250.0) x (baseY + 6.0) "#e2e8f0" 1.0,
      textMid x (baseY + 26.0) ("10" ++ sup (i + 2)) 11.5 "#94a3b8" ]

/-- The four bounds of the census, with the number of dual failures below each. -/
private def bounds : List (ℕ × ℕ) := [(3, 1), (6, 2), (9, 4), (12, 7)]

private def boundMarks : List String :=
  bounds.flatMap fun (e, n) =>
    let x := xOfPow e.toFloat
    [ line x (baseY - 252.0) x (baseY + 40.0) violet 1.6 (dash := "6 5")
        (extra := "opacity=\"0.65\""),
      chip x (baseY + 58.0) 152.0 28.0
        ("below 10" ++ sup e ++ " :  " ++ toString n) "#f5f3ff" violet "#5b21b6" 12.5 ]

private def rungs : List String :=
  pivots.zipIdx.flatMap fun ((p, k), i) =>
    let q := p ^ k
    let x := xOf q
    let h := 74.0 + 22.0 * i.toFloat
    let first := i == 0
    let col := if first then violet else gold
    [ line x baseY x (baseY - h) col (if first then 3.2 else 2.2),
      circle x (baseY - h) (if first then 9.0 else 7.0)
        (if first then "#ede9fe" else "#fffbeb") col 2.0,
      textMid x (baseY - h - 30.0) (toString q) 12.5 col "middle" "bold",
      textMid x (baseY - h - 14.0) (toString p ++ sup k) 11.0 "#94a3b8" ] ++
    (if first then [ pulse x (baseY - h) 18.0 "#ddd6fe" 2.8 0.0 ] else [])

/-! ## The panel -/

/-- `svg/twist-7-pivot-ladder.svg` — Act VII: the ladder of sizes where both canonical maps
onto the prime subfield are broken, and how many lie below a bound. -/
def act7Svg : String :=
  document 1280.0 760.0 <|
    [ text 40.0 50.0 "Act VII — the pivot ladder: how many below M?" 24.0 "#0f172a" "start"
        "bold",
      text 40.0 76.0
        "A dual failure is a size q = pᵏ where both canonical maps onto 𝔽ₚ are broken: the orbit sum annihilates 𝔽ₚ (p ∣ k) and the orbit product moves a point of it ((p−1) ∤ (k−1))."
        13.0 "#475569" "start",
      text 40.0 98.0
        "Act VI found one below 1825, namely 729. On a logarithmic axis the rest of the ladder is very sparse: seven rungs in the whole range up to 10¹²."
        12.5 "#94a3b8" "start" ] ++
    decades ++ boundMarks ++
    [ line 80.0 baseY 1200.0 baseY slate 1.6 ] ++
    rungs ++
    [ card 70.0 452.0 560.0 250.0 16.0,
      text 94.0 484.0 "The classification" 16.0 "#0f172a" "start" "bold",
      text 94.0 512.0 "pᵏ is a dual failure  ⟺  p is odd, k = m·p," 13.0 slate "start",
      text 94.0 534.0 "and m ≢ 1 (mod p − 1)." 13.0 slate "start",
      text 94.0 562.0 "p = 2 never fails twice: p − 1 = 1 divides everything." 12.0 "#64748b"
        "start",
      text 94.0 584.0 "k = p never fails twice: k − 1 = p − 1." 12.0 "#64748b" "start",
      text 94.0 612.0 "So the smallest exponent that fails twice is k = 2p," 12.5 slate "start",
      text 94.0 634.0 "and the smallest dual failure of all is 3⁶ = 729." 13.0 violet "start"
        "bold",
      text 94.0 664.0 "(isDualFailure_iff, isDualFailure_two_mul, min_size)" 11.0 "#94a3b8"
        "start",
      card 660.0 452.0 550.0 250.0 16.0,
      text 684.0 484.0 "The count below M" 16.0 "#0f172a" "start" "bold",
      text 684.0 512.0 "For each odd prime p, with mmax the largest m" 12.5 slate "start",
      text 684.0 534.0 "such that p^(m·p) ≤ M, the number of dual" 12.5 slate "start",
      text 684.0 556.0 "failures of characteristic p below M is" 12.5 slate "start",
      text 684.0 584.0 "mmax − (mmax − 1)/(p − 1) − 1." 14.0 gold "start" "bold",
      text 684.0 614.0 "At M = 10¹²:  p = 3 gives 8 − 3 − 1 = 4," 12.5 slate "start",
      text 684.0 636.0 "p = 5 gives 3 − 0 − 1 = 2, p = 7 gives 2 − 0 − 1 = 1;" 12.5 slate
        "start",
      text 684.0 658.0 "total 7, and no larger prime contributes." 13.0 violet "start" "bold",
      text 684.0 686.0 "(card_dualExponents, count_1e12_split)" 11.0 "#94a3b8" "start",
      text 640.0 736.0
        "The counts are theorems, not samples: census_1e3, census_1e6, census_1e9 and census_1e12 each list every dual-failure pair below their bound."
        12.0 "#64748b" ]

end PivotViz
