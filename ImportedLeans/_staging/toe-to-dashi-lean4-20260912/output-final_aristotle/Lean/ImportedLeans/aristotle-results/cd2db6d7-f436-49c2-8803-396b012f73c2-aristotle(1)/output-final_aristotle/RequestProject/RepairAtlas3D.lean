import RequestProject.Anim3D
import RequestProject.RepairScan

/-!
# The atlas of errors, and their repair, in three dimensions

`svg/repair-atlas-3d.svg` draws the whole outcome of the scan `q = 2 … 1824` in one animated
three-dimensional picture: one bar for each of the `18` field sizes whose Frobenius orbit
product is **not** a retraction onto the prime subfield, of height equal to the error — the
number of points of `𝔽ₚ` that the orbit product moves (`BigFieldSizeScan.bigScan_failing_sizes`).

The scene rocks back and forth so that the bars read as solids, and the animation applies the
repair: the bars sink to flat green tiles (the repaired maps, which move no point at all) and
rise again, so one sees the errors and their correction in the same picture.

The bars are marked by which repairs exist (`RepairScan.repairTable_eq`):

* **gold rim** — a *multiplicative* repair exists, `gcd (k, p−1) = 1`: only `q = 125` and
  `q = 1331`, repaired by `x ↦ x⁹³` and `x ↦ x⁹³¹`;
* **violet rim** — the *rescaled* orbit sum does not repair the additive error either,
  because `p ∣ k`: only `q = 729`, where the twisted orbit sum `x ↦ Tr(c·x)` is needed;
* **plain rim** — the rescaled orbit sum `x ↦ k⁻¹ Tr(x)` already repairs it.

Every bar sinks to zero, because *every* error is repairable additively
(`GaloisFieldRepair.all_errors_additively_repairable`).  The numbers drawn are `atlas_eq`.
-/

set_option maxRecDepth 100000

namespace AtlasViz

open SvgCore Anim3D

/-! ### The data -/

/-- The failing sizes with their errors and the two repair flags, as drawn. -/
def atlas : List (ℕ × ℕ × ℕ × ℕ × Bool × Bool) :=
  RepairScan.repairTable.map fun r => (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2.1)

/-- The eighteen bars: `(q, p, k, error, rescaling repairs the additive error,
a multiplicative repair exists)`. -/
theorem atlas_eq :
    atlas =
      [(9, 3, 2, 1, true, false), (25, 5, 2, 3, true, false), (49, 7, 2, 5, true, false),
       (81, 3, 4, 1, true, false), (121, 11, 2, 9, true, false), (125, 5, 3, 2, true, true),
       (169, 13, 2, 11, true, false), (289, 17, 2, 15, true, false),
       (343, 7, 3, 4, true, false), (361, 19, 2, 17, true, false),
       (529, 23, 2, 21, true, false), (625, 5, 4, 3, true, false),
       (729, 3, 6, 1, false, false), (841, 29, 2, 27, true, false),
       (961, 31, 2, 29, true, false), (1331, 11, 3, 8, true, true),
       (1369, 37, 2, 35, true, false), (1681, 41, 2, 39, true, false)] := by
  rfl

/-- The tallest bar is `q = 1681 = 41²` with error `39`, and there are eighteen bars. -/
theorem atlas_max :
    atlas.length = 18 ∧ (atlas.map fun r => r.2.2.2.1).foldl max 0 = 39 := by
  refine ⟨by decide, by decide⟩

/-! ### The animation -/

private def frames : Nat := 30

private def cycle : Float := 15.0

/-- The rocking angle of frame `i`: a gentle ±24° oscillation, one period per cycle. -/
private def angleAt (i : Nat) : Float :=
  0.58 + 0.26 * Float.sin (tau * i.toFloat / frames.toFloat)

/-- How much of the error is still standing at frame `i`: full for the first third of the
cycle, then the repair is applied and the bars sink to zero, then they rise again. -/
private def heightAt (i : Nat) : Float :=
  let u := i.toFloat / frames.toFloat
  if u < 0.34 then 1.0
  else if u < 0.46 then 1.0 - (u - 0.34) / 0.12
  else if u < 0.82 then 0.0
  else (u - 0.82) / 0.18

private def cam : Cam := ⟨640.0, 455.0, 95.0, 0.55⟩

private def maxError : Float := 39.0

/-- World height of a bar of error `d` at animation frame `i`. -/
private def barHeight (d : ℕ) (i : Nat) : Float :=
  1.6 * d.toFloat / maxError * heightAt i

private def cols : Nat := 6

private def cellX (idx : Nat) : Float := ((idx % cols).toFloat - 2.5) * 1.34
private def cellY (idx : Nat) : Float := ((idx / cols).toFloat - 1.0) * 1.5

private def corner (idx : Nat) (dx dy z : Float) : P3 :=
  ⟨cellX idx + dx, cellY idx + dy, z⟩

private def quadPoints (i : Nat) (ps : List P3) : String :=
  String.intercalate " " (ps.map fun p =>
    let q := proj cam (rotZ (angleAt i) p)
    num q.1 ++ "," ++ num q.2)

private def animPoints (mk : Nat → String) : String :=
  animStrings "points" ((List.range frames).map mk) cycle

private def brokenTop : Nat × Nat × Nat := (225, 29, 72)
private def brokenSide : Nat × Nat × Nat := (159, 18, 57)
private def repairedTop : Nat × Nat × Nat := (16, 185, 129)

private def animFill (c₀ c₁ : Nat × Nat × Nat) : String :=
  animStrings "fill" ((List.range frames).map fun i => lerpColor c₀ c₁ (heightAt i)) cycle

/-- One animated bar: three shaded faces whose corners are recomputed every frame, sinking to
a flat tile as the repair is applied. -/
private def bar (idx : Nat) (row : ℕ × ℕ × ℕ × ℕ × Bool × Bool) : List String :=
  let (q, _p, _k, d, scalingOK, multOK) := row
  let hAt := fun i => barHeight d i
  let a := 0.44
  let b := 0.55
  let rim :=
    if multOK then "#b45309" else if scalingOK then "#ffffff" else "#7c3aed"
  let rimW : Float := if multOK || ¬ scalingOK then 2.4 else 0.7
  let topQuad := fun i =>
    quadPoints i [corner idx (-a) (-b) (hAt i), corner idx a (-b) (hAt i),
      corner idx a b (hAt i), corner idx (-a) b (hAt i)]
  let frontQuad := fun i =>
    quadPoints i [corner idx (-a) b (hAt i), corner idx a b (hAt i),
      corner idx a b 0.0, corner idx (-a) b 0.0]
  let sideQuad := fun i =>
    quadPoints i [corner idx a (-b) (hAt i), corner idx a b (hAt i),
      corner idx a b 0.0, corner idx a (-b) 0.0]
  let labelPts := (List.range frames).map fun i =>
    proj cam (rotZ (angleAt i) (corner idx 0.0 0.0 (hAt i + 0.16)))
  [ "  <polygon points=\"" ++ frontQuad 0 ++ "\" fill=\"" ++
      lerpColor repairedTop brokenSide 1.0 ++ "\" stroke=\"#ffffff\" stroke-width=\"0.5\">" ++
      animPoints frontQuad ++ animFill repairedTop brokenSide ++ "</polygon>",
    "  <polygon points=\"" ++ sideQuad 0 ++ "\" fill=\"" ++
      lerpColor repairedTop brokenSide 1.0 ++ "\" stroke=\"#ffffff\" stroke-width=\"0.5\">" ++
      animPoints sideQuad ++ animFill repairedTop brokenSide ++ "</polygon>",
    "  <polygon points=\"" ++ topQuad 0 ++ "\" fill=\"" ++
      lerpColor repairedTop brokenTop 1.0 ++ "\" stroke=\"" ++ rim ++
      "\" stroke-width=\"" ++ num rimW ++ "\" stroke-linejoin=\"round\">" ++
      animPoints topQuad ++ animFill repairedTop brokenTop ++ "</polygon>",
    "  <text x=\"" ++ num (labelPts.headD (0.0, 0.0)).1 ++ "\" y=\"" ++
      num (labelPts.headD (0.0, 0.0)).2 ++
      "\" font-size=\"11\" fill=\"#0f172a\" text-anchor=\"middle\" " ++
      "dominant-baseline=\"central\" font-weight=\"bold\">" ++ toString q ++
      animValues "x" (labelPts.map Prod.fst) cycle ++
      animValues "y" (labelPts.map Prod.snd) cycle ++ "</text>" ]

/-- The floor tile under each bar, so that the sunk bars still sit on a visible grid. -/
private def floorTiles : List String :=
  (List.range atlas.length).map fun idx =>
    let quad := fun i =>
      quadPoints i [corner idx (-0.48) (-0.6) 0.0, corner idx 0.48 (-0.6) 0.0,
        corner idx 0.48 0.6 0.0, corner idx (-0.48) 0.6 0.0]
    "  <polygon points=\"" ++ quad 0 ++
      "\" fill=\"#e2e8f0\" stroke=\"#cbd5e1\" stroke-width=\"0.8\">" ++
      animPoints quad ++ "</polygon>"

/-- Depth of a cell at the mean rocking angle; larger is nearer to the camera. -/
private def cellDepth (idx : Nat) : Float := (rotZ 0.58 ⟨cellX idx, cellY idx, 0.0⟩).y

/-- The cells, from the back of the scene to the front. -/
private def cellsByDepth : List Nat :=
  (List.range atlas.length).mergeSort fun a b => cellDepth a ≤ cellDepth b

/-- The bars, tallest at the back: the eighteen errors are laid out in decreasing order along
the depth of the scene, so that no bar hides a taller one behind it, and drawn from the back
forwards. -/
private def bars : List String :=
  let byError := atlas.mergeSort fun a b => b.2.2.2.1 ≤ a.2.2.2.1
  (List.zip cellsByDepth byError).flatMap fun (idx, row) => bar idx row

private def legend : List String :=
  [ card 40.0 662.0 1200.0 140.0 14.0,
    circle 74.0 696.0 9.0 "#e11d48" "#ffffff" 1.0,
    text 92.0 701.0
      "height = error: the number of points of 𝔽ₚ moved by the orbit product N(x) = x^(1+p+⋯+p^(k−1))"
      13.0 "#334155" "start",
    circle 74.0 724.0 9.0 "#10b981" "#047857" 1.0,
    text 92.0 729.0
      "flat green = repaired: the twisted orbit sum x ↦ Tr(c·x) with Tr(c) = 1 moves no point at all — this exists for every finite field"
      13.0 "#334155" "start",
    rect 66.0 742.0 16.0 16.0 3.0 "#fef3c7" "#b45309" 2.4,
    text 92.0 755.0
      "gold rim = a multiplicative repair also exists, gcd(k, p−1) = 1: only q = 125 (x ↦ x⁹³) and q = 1331 (x ↦ x⁹³¹)"
      13.0 "#334155" "start",
    rect 66.0 768.0 16.0 16.0 3.0 "#ede9fe" "#7c3aed" 2.4,
    text 92.0 781.0
      "violet rim = rescaling the orbit sum fails (p ∣ k): only q = 729, where the twist x ↦ Tr(c·x) is indispensable"
      13.0 "#334155" "start" ]

/-- `svg/repair-atlas-3d.svg`: the eighteen errors of the scan, rocking in three dimensions
and collapsing as the repair is applied. -/
def atlasSvg : String :=
  document 1280.0 830.0 <|
    [ text 40.0 52.0 "Every error of the scan q = 2 … 1824, and its repair" 22.0 "#0f172a"
        "start" "bold",
      text 40.0 78.0
        "18 field sizes have a nonzero error; the bars sink to green as the repaired map replaces the orbit product, and rise again as it is taken away."
        13.0 "#475569" "start" ] ++
    floorTiles ++ bars ++ legend

end AtlasViz
