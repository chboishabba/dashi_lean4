import RequestProject.BigFieldSizeScan
import RequestProject.SvgCore

/-!
# The error terms in three dimensions

`svg/frobenius-defect-3d.svg` (`Heat3DViz.heat3dSvg`) is the three-dimensional version of the
heat map of `RequestProject/EyeCandy.lean`: over the base plane of characteristics `p` and
degrees `k` it raises a solid bar of height

  `frobDefect p k = (p − 1) − gcd (p − 1, k − 1)`,

the number of elements of the prime field `𝔽ₚ` that the Frobenius orbit product of `GF(pᵏ)`
moves (`FieldSizeScan.card_frobNorm_failures`).  Flat green tiles are the genuine retractions
(`FieldSizeScan.retraction_iff_frobDefect_eq_zero`).

The picture is drawn over exactly the primes reachable by the expanded scan of
`RequestProject/BigFieldSizeScan.lean` — `p ≤ 41`, since `41² = 1681 ≤ 1824 < 43²` — and the
cells that really are field sizes `q = pᵏ ≤ 1824` are outlined in gold and labelled with `q`
(`inScanCells_eq`, `inScanCells_are_field_sizes`).

Three features of the surface are theorems:

* the `k = 1` edge lies flat on the floor (`frobDefect_degree_one`);
* the `k = 2` line is the straight ridge `frobDefect p 2 = p − 2` (`frobDefect_degree_two`),
  whose highest gold-rimmed point is `GF(41²) = GF(1681)` with error `39`
  (`BigFieldSizeScan.bigScan_max_error`, `surface_max`);
* along the `k` direction each row repeats with period `p − 1`
  (`HeatViz.frobDefect_periodic`), so the green tiles line up in diagonal furrows.

The numbers drawn are pinned down by `surface_eq`.
-/

set_option maxRecDepth 100000

namespace Heat3DViz

open SvgCore FieldSizeScan

/-! ### The surface -/

/-- The characteristics carried by the `p` axis: every prime `p` with `p² ≤ 1824`, i.e. every
characteristic in which the expanded scan sees a proper prime power.  They are listed from the
back of the picture to the front, so that the tall bars never hide the short ones. -/
def axisPrimes : List ℕ := [41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2]

/-- The degrees carried by the `k` axis. -/
def axisDegrees : List ℕ := List.range' 1 12

/-- The drawn surface: for each characteristic `p`, the errors `frobDefect p k` for
`k = 1, …, 12`. -/
def surface : List (ℕ × List ℕ) :=
  axisPrimes.map fun p => (p, axisDegrees.map fun k => frobDefect p k)

/-- The heights actually drawn. -/
theorem surface_eq :
    surface =
      [(41, [0, 39, 38, 39, 36, 35, 38, 39, 32, 39, 30, 39]),
       (37, [0, 35, 34, 33, 32, 35, 30, 35, 32, 27, 34, 35]),
       (31, [0, 29, 28, 27, 28, 25, 24, 29, 28, 27, 20, 29]),
       (29, [0, 27, 26, 27, 24, 27, 26, 21, 24, 27, 26, 27]),
       (23, [0, 21, 20, 21, 20, 21, 20, 21, 20, 21, 20, 11]),
       (19, [0, 17, 16, 15, 16, 17, 12, 17, 16, 9, 16, 17]),
       (17, [0, 15, 14, 15, 12, 15, 14, 15, 8, 15, 14, 15]),
       (13, [0, 11, 10, 9, 8, 11, 6, 11, 8, 9, 10, 11]),
       (11, [0, 9, 8, 9, 8, 5, 8, 9, 8, 9, 0, 9]),
       (7, [0, 5, 4, 3, 4, 5, 0, 5, 4, 3, 4, 5]),
       (5, [0, 3, 2, 3, 0, 3, 2, 3, 0, 3, 2, 3]),
       (3, [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]),
       (2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])] := by
  decide

/-- The tallest bar of the picture has height `39`: it is `GF(41²) = GF(1681)`, the worst
failure of the whole scan `q ≤ 1824` (`BigFieldSizeScan.bigScan_max_error`). -/
theorem surface_max : (surface.flatMap Prod.snd).foldl max 0 = 39 := by decide

/-- **The `k = 1` edge is flat**: in degree `1` the orbit product is the identity, so the error
is `0` in every characteristic. -/
theorem frobDefect_degree_one (p : ℕ) : frobDefect p 1 = 0 := by
  simp [frobDefect]

/-- **The `k = 2` line is a straight ridge**: in degree `2` the orbit product `x ↦ x²` moves
all but two elements of `𝔽ₚ`. -/
theorem frobDefect_degree_two {p : ℕ} (hp : 2 ≤ p) : frobDefect p 2 = p - 2 := by
  unfold frobDefect
  simp [Nat.gcd_one_right]
  omega

/-! ### The cells that the expanded scan actually reaches -/

/-- The cells `(p, k)` of the picture that are genuine field sizes `q = pᵏ ≤ 1824`, listed as
`(q, p, k)`.  These are drawn with a gold rim and labelled with `q`. -/
def inScanCells : List (ℕ × ℕ × ℕ) :=
  axisPrimes.flatMap fun p =>
    axisDegrees.filterMap fun k => if p ^ k ≤ 1824 then some (p ^ k, p, k) else none

/-- The gold-rimmed cells. -/
theorem inScanCells_eq :
    inScanCells =
      [(41, 41, 1), (1681, 41, 2), (37, 37, 1), (1369, 37, 2), (31, 31, 1), (961, 31, 2),
       (29, 29, 1), (841, 29, 2), (23, 23, 1), (529, 23, 2), (19, 19, 1), (361, 19, 2),
       (17, 17, 1), (289, 17, 2), (13, 13, 1), (169, 13, 2), (11, 11, 1), (121, 11, 2),
       (1331, 11, 3), (7, 7, 1), (49, 7, 2), (343, 7, 3), (5, 5, 1), (25, 5, 2), (125, 5, 3),
       (625, 5, 4), (3, 3, 1), (9, 3, 2), (27, 3, 3), (81, 3, 4), (243, 3, 5), (729, 3, 6),
       (2, 2, 1), (4, 2, 2), (8, 2, 3), (16, 2, 4), (32, 2, 5), (64, 2, 6), (128, 2, 7),
       (256, 2, 8), (512, 2, 9), (1024, 2, 10)] := by
  decide

/-- Every gold-rimmed cell really is a field size seen by the expanded scan. -/
theorem inScanCells_are_field_sizes :
    inScanCells.all (fun r => BigFieldSizeScan.gfDataBig r.1 == some (r.2.1, r.2.2)) = true := by
  decide +kernel

/-- The `29` gold-rimmed cells of degree `k ≥ 2` are exactly the proper prime powers `≤ 1824`
of the expanded scan: the `11` retractions of
`BigFieldSizeScan.bigScan_retractive_proper_prime_powers` and the `18` failures of
`BigFieldSizeScan.bigScan_failing_sizes`. -/
theorem inScanCells_proper_count :
    (inScanCells.filter fun r => 2 ≤ r.2.2).length = 29 ∧
    (inScanCells.filter fun r => 2 ≤ r.2.2 ∧ frobDefect r.2.1 r.2.2 = 0).length = 11 ∧
    (inScanCells.filter fun r => 2 ≤ r.2.2 ∧ frobDefect r.2.1 r.2.2 ≠ 0).length = 18 := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### Rendering the surface -/

private def ax : Float := 44.0
private def ay : Float := 26.0
private def hz : Float := 4.6
private def ox : Float := 700.0
private def oy : Float := 300.0
private def inset : Float := 0.09

private def width : Float := 1420.0
private def height : Float := 1250.0

/-- The isometric projection: `u` runs along the degree axis, `v` along the characteristic
axis, `z` is the error. -/
private def proj (u v z : Float) : Float × Float :=
  (ox + (u - v) * ax, oy + (u + v) * ay - z * hz)

private def nRows : Nat := 13
private def nCols : Nat := 12

private def primeAt (j : Nat) : Nat := axisPrimes.getD j 0
private def degreeAt (i : Nat) : Nat := axisDegrees.getD i 0
private def defectAt (i j : Nat) : Nat := frobDefect (primeAt j) (degreeAt i)

/-- The colour ramp of the heat map, as an `(r,g,b)` triple so that the side faces of a bar
can be shaded darker. -/
private def rampRGB (u : Float) : Nat × Nat × Nat :=
  let u := if u < 0.0 then 0.0 else if u > 1.0 then 1.0 else u
  let mix (a b : Nat) (t : Float) : Nat := (a.toFloat + (b.toFloat - a.toFloat) * t).round.toUInt32.toNat
  if u ≤ 0.5 then
    let t := u * 2.0
    (mix 254 251 t, mix 243 146 t, mix 199 60 t)
  else
    let t := (u - 0.5) * 2.0
    (mix 251 159 t, mix 146 18 t, mix 60 57 t)

private def faceColor (c : Nat × Nat × Nat) (dark : Float) : String := lerpColor c (0, 0, 0) dark

/-- One bar, drawn as three shaded faces; a flat green tile when the error is `0`. -/
private def bar (i j : Nat) : List String :=
  let p := primeAt j
  let d := defectAt i j
  let u₀ := i.toFloat + inset
  let u₁ := i.toFloat + 1.0 - inset
  let v₀ := j.toFloat + inset
  let v₁ := j.toFloat + 1.0 - inset
  let h := d.toFloat
  let gold := (inScanCells.any fun r => r.2.1 == p && r.2.2 == degreeAt i)
  let back := proj u₀ v₀ h
  let right := proj u₁ v₀ h
  let front := proj u₁ v₁ h
  let left := proj u₀ v₁ h
  let rightB := proj u₁ v₀ 0.0
  let frontB := proj u₁ v₁ 0.0
  let leftB := proj u₀ v₁ 0.0
  let span := if p ≤ 2 then 1.0 else (p - 1 : ℕ).toFloat
  let c := rampRGB (d.toFloat / span)
  let topFill := if d == 0 then "#10b981" else rgb c.1 c.2.1 c.2.2
  let rimColor := if gold then "#b45309" else if d == 0 then "#047857" else "#ffffff"
  let rimWidth := if gold then 2.2 else 0.8
  let sides :=
    if d == 0 then []
    else
      [ polygon [right, front, frontB, rightB] (faceColor c 0.22) "#ffffff" 0.5,
        polygon [left, front, frontB, leftB] (faceColor c 0.4) "#ffffff" 0.5 ]
  let top :=
    polygon [back, right, front, left] topFill rimColor rimWidth "class=\"cell\""
  let label :=
    if gold && 2 ≤ degreeAt i then
      let q := p ^ degreeAt i
      let lx := (back.1 + front.1) / 2.0
      let ly := ((back.2 + front.2) / 2.0) - 14.0
      -- a white halo underneath, so that the label stays legible on top of a dark bar
      [ textMid lx ly (toString q) 12.0 "#ffffff" "middle" "bold"
          "stroke=\"#ffffff\" stroke-width=\"3.2\" stroke-linejoin=\"round\"",
        textMid lx ly (toString q) 12.0 "#7c2d12" "middle" "bold" ]
    else []
  sides ++ [top] ++ label

/-- The base plane, its rim, and the two horizontal axes with their tick labels. -/
private def floorAndAxes : List String :=
  let c00 := proj 0.0 0.0 0.0
  let c10 := proj nCols.toFloat 0.0 0.0
  let c11 := proj nCols.toFloat nRows.toFloat 0.0
  let c01 := proj 0.0 nRows.toFloat 0.0
  let plane :=
    [ polygon [c00, c10, c11, c01] "#eef2ff" "#c7d2fe" 1.2 ]
  let gridK := (List.range (nCols + 1)).map fun i =>
    let a := proj i.toFloat 0.0 0.0
    let b := proj i.toFloat nRows.toFloat 0.0
    line a.1 a.2 b.1 b.2 "#dbe2f5" 0.8
  let gridP := (List.range (nRows + 1)).map fun j =>
    let a := proj 0.0 j.toFloat 0.0
    let b := proj nCols.toFloat j.toFloat 0.0
    line a.1 a.2 b.1 b.2 "#dbe2f5" 0.8
  let kTicks := (List.range nCols).map fun i =>
    let a := proj (i.toFloat + 0.5) (nRows.toFloat + 0.6) 0.0
    textMid a.1 a.2 (toString (degreeAt i)) 14.0 "#0f172a" "middle" "bold"
  let pTicks := (List.range nRows).map fun j =>
    let a := proj (nCols.toFloat + 0.6) (j.toFloat + 0.5) 0.0
    textMid a.1 a.2 (toString (primeAt j)) 14.0 "#0f172a" "middle" "bold"
  let kTitle :=
    let a := proj (nCols.toFloat / 2.0) (nRows.toFloat + 2.2) 0.0
    textMid a.1 a.2 "degree k" 19.0 "#1d4ed8" "middle" "bold"
  let pTitle :=
    let a := proj (nCols.toFloat + 1.9) (nRows.toFloat / 2.0) 0.0
    textMid a.1 a.2 "characteristic p" 19.0 "#be185d" "middle" "bold"
  plane ++ gridK ++ gridP ++ kTicks ++ pTicks ++ [kTitle, pTitle]

/-- The vertical scale of the picture, standing just outside the left corner of the floor. -/
private def zAxis : List String :=
  let bu : Float := -0.6
  let bv : Float := nRows.toFloat + 1.4
  let base := proj bu bv 0.0
  let top := proj bu bv 42.0
  let corner := proj 0.0 nRows.toFloat 0.0
  let ticks := [0, 10, 20, 30, 40].flatMap fun z =>
    let a := proj bu bv z.toFloat
    [ line a.1 a.2 (a.1 - 9.0) a.2 "#475569" 1.2,
      textMid (a.1 - 14.0) a.2 (toString z) 12.5 "#475569" "end" "normal" ]
  [ line base.1 base.2 corner.1 corner.2 "#94a3b8" 1.0 "" "4 5",
    line base.1 base.2 top.1 top.2 "#475569" 1.6 "slate",
    text (top.1 + 14.0) (top.2 - 24.0) "error" 17.0 "#0f172a" "start" "bold",
    text (top.1 + 14.0) (top.2 - 6.0) "#{a ∈ 𝔽ₚ : N(a) ≠ a}" 12.5 "#475569" "start" ] ++
    ticks

/-- The bars, drawn back to front so that the near ones overlap the far ones. -/
private def bars : List String :=
  (List.range (nCols + nRows)).flatMap fun s =>
    ((List.range nCols).filterMap fun i =>
      if i ≤ s ∧ s - i < nRows then some (i, s - i) else none).flatMap fun (i, j) => bar i j

private def legend : List String :=
  let y := 1000.0
  [ text 90.0 (y - 16.0) "error, as a fraction of the maximum p − 1" 14.0 "#475569" "start" ] ++
  rampBar 90.0 y 280.0 18.0 24 heatRamp ++
  [ text 90.0 (y + 34.0) "0" 12.5 "#64748b" "start",
    text 370.0 (y + 34.0) "p − 1" 12.5 "#64748b" "end",
    rect 430.0 y 26.0 18.0 6.0 "#10b981" "#047857" 2.0,
    text 466.0 (y + 14.0) "flat green tile : error 0, N is a retraction onto 𝔽ₚ" 14.0 "#475569"
      "start",
    rect 900.0 y 26.0 18.0 6.0 "#ffffff" "#b45309" 2.4,
    text 936.0 (y + 14.0) "gold rim : q = pᵏ ≤ 1824, a field size of the scan" 14.0 "#475569"
      "start" ]

/-- The 18 failures of the expanded scan, listed under the picture; the list is exactly the
one computed in `BigFieldSizeScan.bigScan_failing_sizes`. -/
def failurePanelData : List (ℕ × ℕ × ℕ × ℕ) :=
  BigFieldSizeScan.bigScan.filterMap fun r =>
    match r.2 with
    | some (p, k, d) => if d ≠ 0 then some (r.1, p, k, d) else none
    | none => none

private def sup (k : ℕ) : String :=
  match k with
  | 2 => "²" | 3 => "³" | 4 => "⁴" | 5 => "⁵" | 6 => "⁶" | 7 => "⁷" | 8 => "⁸" | 9 => "⁹"
  | 10 => "¹⁰" | 11 => "¹¹" | 12 => "¹²" | _ => "^" ++ toString k

private def failureEntry (r : ℕ × ℕ × ℕ × ℕ) : String :=
  toString r.1 ++ " = " ++ toString r.2.1 ++ sup r.2.2.1 ++ " (" ++ toString r.2.2.2 ++ ")"

/-- A panel summarising the expanded scan, in the empty corner above the picture. -/
private def summaryCard : List String :=
  let x := 60.0
  let y := 150.0
  [ card x y 380.0 168.0 16.0,
    text (x + 20.0) (y + 34.0) "The expanded scan q = 2 … 1824" 17.0 "#0f172a" "start" "bold",
    text (x + 20.0) (y + 62.0) "1823 candidate sizes in all" 13.5 "#475569" "start",
    text (x + 20.0) (y + 88.0) "1513 are not field sizes at all" 13.5 "#b91c1c" "start",
    text (x + 20.0) (y + 114.0) "292 have error 0 — genuine retractions" 13.5 "#047857" "start",
    text (x + 20.0) (y + 140.0) "18 have a nonzero error" 13.5 "#b45309" "start" ]

private def notes : List String :=
  let y := 1070.0
  [ text 90.0 y
      "the k = 1 edge lies flat on the floor : the orbit product is the identity there, so the error is 0 in every characteristic (frobDefect p 1 = 0)"
      14.0 "#334155" "start",
    text 90.0 (y + 26.0)
      "the k = 2 line is the straight ridge frobDefect p 2 = p − 2 ; its tallest gold cell is GF(41²) = GF(1681), error 39 — the worst below 1825"
      14.0 "#334155" "start",
    text 90.0 (y + 52.0)
      "along k each row repeats with period p − 1, so the green tiles line up in diagonal furrows: error 0 exactly when k ≡ 1 (mod p − 1)"
      14.0 "#334155" "start",
    text 90.0 (y + 84.0)
      ("the 18 field sizes q ≤ 1824 with a nonzero error, as q = pᵏ (error) :   " ++
        String.intercalate " ,   " ((failurePanelData.take 9).map failureEntry))
      13.5 "#7c2d12" "start",
    text 90.0 (y + 108.0)
      (String.intercalate " ,   " ((failurePanelData.drop 9).map failureEntry))
      13.5 "#7c2d12" "start" ]

/-- The 3-d picture of the error terms. -/
def heat3dSvg : String :=
  let title :=
    [ text (width / 2.0) 56.0
        "The error of the Frobenius orbit product, in three dimensions" 30.0 "url(#ink)"
        "middle" "bold",
      text (width / 2.0) 88.0
        "height of the bar over (p, k) = how many elements of 𝔽ₚ the orbit product N of GF(pᵏ) moves = (p−1) − gcd(p−1, k−1)"
        15.5 "#475569",
      text (width / 2.0) 112.0
        "the scan q ≤ 1824 reaches exactly the gold-rimmed cells: every prime power pᵏ ≤ 1824, so every prime p ≤ 41 = the largest with p² ≤ 1824"
        15.5 "#475569" ]
  document width height
    (title ++ summaryCard ++ floorAndAxes ++ zAxis ++ bars ++ legend ++ notes)

end Heat3DViz
