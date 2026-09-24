import RequestProject.TwistSeries
import RequestProject.Visualization
import RequestProject.Anim3D

/-!
# The twist, in six panels

The pictures `svg/twist-1-dead-dial.svg` … `svg/twist-6-census.svg`: a series that zooms in on
the one word the earlier gear picture could only afford to say once — *twist*.

Every number drawn here is computed from the Lean definitions of
`RequestProject/TwistSeries.lean` (which are themselves checked against the general theory by
kernel computation), and the shapes of the drawn data are pinned down by the theorems in this
file (`TwistViz.levels_eq`, `TwistViz.twistLevels_eq`, `TwistViz.twistImages_eq`,
`TwistViz.deadDialMarks_eq`).

* **Act I** `twist-1-dead-dial.svg` — the orbit sum of `GF(27)` collapses the whole prime
  subfield to `0`, and rescaling can never undo that: a rescaling repair exists *exactly* when
  `p ∤ k` (`FrobeniusPrimeSubfield.scalar_repair_iff_not_dvd`).
* **Act II** `twist-2-still-onto.svg` — yet the orbit sum is onto: `GF(27)` splits into three
  level sets of nine (`GF27Twist.trace3_fibre_card`).  The map is not small, it is aimed
  wrongly: `𝔽₃` lies inside the level `Tr = 0`.
* **Act III** `twist-3-the-twist.svg` — the twist turns the *field*, not the value:
  multiplication by `c = 2t²` carries `𝔽₃` across all three levels, because
  `Tr(c·a) = a·Tr(c) = a`.
* **Act IV** `twist-4-repaired-map.svg` — the repaired map `R(x) = Tr(2t²·x) = x.c₀ + x.c₂`
  and its three gold fixed points: a genuine retraction onto `𝔽₃`
  (`GF27Twist.twistMap_isRetraction`), at the cost of multiplicativity.
* **Act V** `twist-5-nine-twists.svg` — there are nine twists, giving nine different
  retractions: exactly the nine `𝔽₃`-linear functionals with `1 ↦ 1`
  (`GF27Twist.twistFunctionals_eq`, `GF27Twist.twists_pairwise_distinct`).
* **Act VI** `twist-6-census.svg` — where the twist is indispensable: the seven sizes
  `4, 16, 27, 64, 256, 729, 1024` below `1825` whose dial is dead
  (`TwistCensus.deadDialSizes_eq`), of which `729` is the one that also fails
  multiplicatively.
-/

namespace TwistViz

open SvgCore Anim3D GF27 GF27Twist

/-! ## Drawn data -/

/-- The `27` elements, in the order of `GF27.enum`. -/
def elems : List GF27 := GF27.enum

/-- The value of the orbit sum, as a digit `0, 1, 2`. -/
def trVal (x : GF27) : ℕ := (trace3 x).c0.val

/-- The value of the twisted map, as a digit `0, 1, 2`. -/
def twVal (x : GF27) : ℕ := (twistMap x).c0.val

/-- Membership of the prime subfield. -/
def isPrime (x : GF27) : Bool := decide (x.c1 = 0 ∧ x.c2 = 0)

/-- The three elements of the prime subfield, in the order `0, 1, 2`. -/
def primeElems : List GF27 := elems.filter isPrime

/-- The level set `Tr = v` of the orbit sum. -/
def level (v : ℕ) : List GF27 := elems.filter fun x => trVal x == v

/-- The level set `R = v` of the twisted map. -/
def twistLevel (v : ℕ) : List GF27 := elems.filter fun x => twVal x == v

/-- **The drawn level sets of the orbit sum are correct**: nine elements each, and the level
`Tr = 0` is the one containing the whole prime subfield `{0, 1, 2}` (codes `000`, `001`,
`002`). -/
theorem levels_eq :
    (level 0).map GF27Viz.code =
      ["000", "010", "020", "001", "011", "021", "002", "012", "022"] ∧
    (level 1).map GF27Viz.code =
      ["200", "210", "220", "201", "211", "221", "202", "212", "222"] ∧
    (level 2).map GF27Viz.code =
      ["100", "110", "120", "101", "111", "121", "102", "112", "122"] := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **The drawn level sets of the twisted map are correct**, and this time the prime subfield
`{000, 001, 002}` meets all three of them — one point each, which is exactly the retraction
property `R(a) = a`. -/
theorem twistLevels_eq :
    (twistLevel 0).map GF27Viz.code =
      ["000", "010", "020", "201", "211", "221", "102", "112", "122"] ∧
    (twistLevel 1).map GF27Viz.code =
      ["100", "110", "120", "001", "011", "021", "202", "212", "222"] ∧
    (twistLevel 2).map GF27Viz.code =
      ["200", "210", "220", "101", "111", "121", "002", "012", "022"] := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **The twist in one line.**  Multiplication by `c = 2t²` moves the three points of `𝔽₃`
onto `0, 2t², t²`, whose orbit sums are `0, 1, 2`: the prime subfield, which lay flat inside
the single level `Tr = 0`, is spread across all three levels. -/
theorem twistImages_eq :
    primeElems.map (fun a => (GF27Viz.code a, GF27Viz.code (theTwist * a),
        trVal (theTwist * a))) =
      [("000", "000", 0), ("001", "200", 1), ("002", "100", 2)] := by
  decide +kernel

/-! ## Act I — the dial that dies -/

private def deadRed : String := "#be185d"
private def liveGreen : String := "#047857"
private def gold : String := "#b45309"

private def collapseArrows : List String :=
  (List.range 3).flatMap fun i =>
    let y := 236.0 + 92.0 * i.toFloat
    let d := curveD 178.0 y 452.0 328.0 26.0 34.0 (18.0 - 18.0 * i.toFloat)
    [ path d deadRed 1.8 "pink",
      comet d "#fb7185" 3.4 3.2 (0.7 * i.toFloat) 210.0 ]

private def sourceNodes : List String :=
  (List.range 3).map fun i =>
    let y := 236.0 + 92.0 * i.toFloat
    nodeGroup
      [ circle 152.0 y 24.0 "url(#fill-gold)" gold 1.6,
        textMid 152.0 y (toString i) 16.0 "#7c2d12" "middle" "bold",
        textMid 152.0 (y - 38.0) (if i == 0 then "𝔽₃ ⊂ GF(27)" else "") 11.5 "#94a3b8" ]

private def deadDialRows : List (String × String × String × Bool) :=
  [ ("GF(4) = 2²", "k = 2,  p = 2", "2 ∣ 2 — dead", false),
    ("GF(9) = 3²", "k = 2,  p = 3", "3 ∤ 2 — alive, c = 2⁻¹", true),
    ("GF(27) = 3³", "k = 3,  p = 3", "3 ∣ 3 — dead", false),
    ("GF(729) = 3⁶", "k = 6,  p = 3", "3 ∣ 6 — dead", false) ]

private def deadDialTable : List String :=
  (deadDialRows.zipIdx).flatMap fun ((name, ratio, verdict, ok), i) =>
    let y := 268.0 + 62.0 * i.toFloat
    [ text 676.0 (y + 4.0) name 14.0 "#0f172a" "start" "bold",
      text 676.0 (y + 22.0) ratio 11.5 "#64748b" "start",
      chip 1080.0 (y + 8.0) 292.0 28.0 verdict
        (if ok then "#ecfdf5" else "#fff1f2") (if ok then liveGreen else deadRed)
        (if ok then "#065f46" else "#9f1239") 12.5 ]

/-- `svg/twist-1-dead-dial.svg` — Act I: on the prime subfield the orbit sum is the scalar
`k`, and when `p ∣ k` that scalar is `0`. -/
def act1Svg : String :=
  document 1280.0 700.0 <|
    [ text 40.0 52.0 "Act I — the dial that dies" 24.0 "#0f172a" "start" "bold",
      text 40.0 78.0
        "On the prime subfield the Frobenius orbit sum is not a map at all — it is a single scalar, Tr(a) = k·a.  In GF(27) that scalar is 3 = 0."
        13.0 "#475569" "start",
      card 40.0 104.0 560.0 456.0 18.0,
      text 64.0 138.0 "GF(27) = 𝔽₃[t]/(t³ − t − 1),  p = k = 3" 15.0 "#0f172a" "start" "bold",
      text 64.0 162.0 "Tr(x) = x + x³ + x⁹" 12.5 "#334155" "start",
      text 64.0 182.0 "on 𝔽₃ this is Tr(a) = 3a = 0" 12.5 "#9f1239" "start" "bold",
      pulse 484.0 328.0 46.0 "#fecdd3" 3.0 0.0,
      circle 484.0 328.0 30.0 "#fff1f2" deadRed 2.0,
      textMid 484.0 328.0 "0" 18.0 "#9f1239" "middle" "bold",
      textMid 484.0 384.0 "every point of 𝔽₃" 11.5 "#9f1239",
      textMid 484.0 400.0 "lands on 0" 11.5 "#9f1239",
      chip 320.0 512.0 480.0 30.0
        "Tr kills 𝔽₃ — and so does c·Tr, for every scalar c" "#fff1f2" deadRed "#9f1239" 13.0,
      card 640.0 104.0 600.0 456.0 18.0,
      text 664.0 138.0 "When can a rescaling repair it?" 15.0 "#0f172a" "start" "bold",
      chip 940.0 190.0 520.0 40.0 "∃ c :  c · Tr(1) = 1      ⟺      p ∤ k" "#eef2ff" "#4338ca"
        "#3730a3" 16.0,
      text 664.0 232.0 "(scalar_repair_iff_not_dvd — the exact dividing line)" 11.5 "#94a3b8"
        "start" ] ++
    collapseArrows ++ sourceNodes ++ deadDialTable ++
    [ text 640.0 596.0
        "So on a dead dial no value-side correction survives: c·Tr(a) = c·k·a = 0.  The repair has to act on the argument."
        13.0 "#334155",
      text 640.0 620.0
        "That is the twist:  R(x) = Tr(c·x),  and Act II shows why such a c always exists."
        13.0 "#0f172a" "middle" "bold" ]

/-! ## Act II — the orbit sum is still onto -/

private def towerCam : Cam := ⟨500.0, 402.0, 196.0, 0.44⟩
private def towerDur : Float := 22.0
private def levelZ (v : ℕ) : Float := -1.02 + 1.02 * v.toFloat
private def levelColour (v : ℕ) : String :=
  if v == 0 then "#94a3b8" else if v == 1 then "#7c3aed" else "#0ea5e9"

private def levelDots (v : ℕ) (highlightPrime : Bool) : List String :=
  ((level v).zipIdx).flatMap fun (x, i) =>
    let p := ringPoint 9 i 1.0 (levelZ v)
    let isP := isPrime x
    [ spinDot towerCam p (if isP && highlightPrime then 11.0 else 6.5)
        (if isP && highlightPrime then "url(#fill-gold)" else "#e2e8f0")
        (if isP && highlightPrime then gold else levelColour v) towerDur
        (if isP && highlightPrime then 1.8 else 1.0),
      spinLabel towerCam p (GF27Viz.code x) 9.5
        (if isP && highlightPrime then "#7c2d12" else "#475569") towerDur (-16.0)
        (if isP && highlightPrime then "bold" else "normal") ]

private def levelRings : List String :=
  (List.range 3).flatMap fun v =>
    let ctr := proj towerCam ⟨0.0, 0.0, levelZ v⟩
    [ ringOutline towerCam 1.0 (levelZ v) (levelColour v) 1.3 "4 5" 0.6,
      textMid (ctr.1 - 272.0) ctr.2 ("Tr = " ++ toString v) 14.0 (levelColour v) "start"
        "bold",
      textMid (ctr.1 - 272.0) (ctr.2 + 17.0) "9 elements" 11.0 "#94a3b8" "start" ]

private def towerAxis : String :=
  let a := proj towerCam ⟨0.0, 0.0, levelZ 0 - 0.25⟩
  let b := proj towerCam ⟨0.0, 0.0, levelZ 2 + 0.25⟩
  line a.1 a.2 b.1 b.2 "#cbd5e1" 1.2 "" "5 6"

/-- `svg/twist-2-still-onto.svg` — Act II: the orbit sum is onto `𝔽₃`, with three level sets
of nine; the prime subfield sits inside the single level `Tr = 0`. -/
def act2Svg : String :=
  document 1280.0 780.0 <|
    [ text 40.0 52.0 "Act II — the orbit sum is not small, it is aimed wrongly" 24.0 "#0f172a"
        "start" "bold",
      text 40.0 78.0
        "GF(27) cut into the three level sets of Tr: nine elements each, so Tr is onto 𝔽₃.  Rotating: one turn every 22 s."
        13.0 "#475569" "start",
      towerAxis ] ++
    levelRings ++
    levelDots 0 true ++ levelDots 1 false ++ levelDots 2 false ++
    [ card 880.0 118.0 360.0 546.0 18.0,
      text 904.0 152.0 "Onto, but blind to 𝔽₃" 17.0 "#0f172a" "start" "bold",
      text 904.0 182.0 "Tr(x) = x + x³ + x⁹ takes each of the" 12.5 "#334155" "start",
      text 904.0 200.0 "three values 0, 1, 2 exactly nine times" 12.5 "#334155" "start",
      text 904.0 218.0 "(trace3_fibre_card): the image is all of 𝔽₃." 12.5 "#334155" "start",
      text 904.0 252.0 "So nothing is missing on the value side." 12.5 "#334155" "start",
      text 904.0 270.0 "What is wrong is where the prime subfield" 12.5 "#334155" "start",
      text 904.0 288.0 "sits: all three gold points 000, 001, 002" 12.5 "#334155" "start",
      text 904.0 306.0 "lie in the same level, Tr = 0." 12.5 "#9f1239" "start" "bold",
      text 904.0 340.0 "In coordinates Tr(x) = −x.c₂ : the orbit" 12.5 "#334155" "start",
      text 904.0 358.0 "sum reads the t² coordinate and nothing" 12.5 "#334155" "start",
      text 904.0 376.0 "else, and 𝔽₃ has t² coordinate 0." 12.5 "#334155" "start",
      text 904.0 410.0 "The kernel is a plane" 15.0 "#0f172a" "start" "bold",
      text 904.0 434.0 "Level Tr = 0 is a 2-dimensional 𝔽₃-subspace" 12.5 "#334155" "start",
      text 904.0 452.0 "of GF(27), and it happens to contain 𝔽₃." 12.5 "#334155" "start",
      text 904.0 470.0 "The other two levels are its translates." 12.5 "#334155" "start",
      text 904.0 504.0 "Which suggests the repair" 15.0 liveGreen "start" "bold",
      text 904.0 528.0 "Do not change the values — move the input." 12.5 "#334155" "start",
      text 904.0 546.0 "Pick c with Tr(c) = 1 and feed c·x instead" 12.5 "#334155" "start",
      text 904.0 564.0 "of x.  Nine of the 27 elements qualify." 12.5 "#334155" "start",
      chip 1060.0 610.0 300.0 34.0 "R(x) = Tr(c · x),   c = 2t²" "#ecfdf5" liveGreen "#065f46"
        14.0,
      text 640.0 712.0
        "Gold: the prime subfield 𝔽₃ = {000, 001, 002}, all three trapped in the level Tr = 0 — the whole failure, in one picture."
        13.0 "#334155",
      text 640.0 736.0 "A node abc denotes a·t² + b·t + c." 12.0 "#94a3b8" ]

/-! ## Act III — the twist -/

private def twistEdges : List String :=
  elems.flatMap fun x =>
    let y := theTwist * x
    let v := trVal x
    let w := trVal y
    let i := ((level v).idxOf x)
    let j := ((level w).idxOf y)
    let p := ringPoint 9 i 1.0 (levelZ v)
    let q := ringPoint 9 j 1.0 (levelZ w)
    if isPrime x then
      [ spinEdge towerCam p q 9.0 11.0 gold towerDur 2.6 0.95 ""
          "marker-end=\"url(#arrow-gold)\"" ]
    else
      [ spinEdge towerCam p q 6.0 7.0 "#cbd5e1" towerDur 0.8 0.35 "3 4" ]

private def twistDots : List String :=
  (List.range 3).flatMap fun v =>
    ((level v).zipIdx).flatMap fun (x, i) =>
      let p := ringPoint 9 i 1.0 (levelZ v)
      let isP := isPrime x
      let isImg := (primeElems.map fun a => theTwist * a).contains x
      [ spinDot towerCam p (if isP || isImg then 10.0 else 5.5)
          (if isP then "url(#fill-gold)" else if isImg then "#ecfdf5" else "#e2e8f0")
          (if isP then gold else if isImg then liveGreen else levelColour v) towerDur
          (if isP || isImg then 1.7 else 0.9),
        spinLabel towerCam p (GF27Viz.code x) 9.5
          (if isP then "#7c2d12" else if isImg then "#065f46" else "#94a3b8") towerDur
          (-15.0) (if isP || isImg then "bold" else "normal") ]

/-- `svg/twist-3-the-twist.svg` — Act III: multiplication by `c = 2t²` carries the prime
subfield out of the kernel and across all three levels. -/
def act3Svg : String :=
  document 1280.0 780.0 <|
    [ text 40.0 52.0 "Act III — turn the field, not the value" 24.0 "#0f172a" "start" "bold",
      text 40.0 78.0
        "The gold arrows are x ↦ c·x for c = 2t².  They lift 𝔽₃ off the level Tr = 0 and lay it across all three levels — one point each."
        13.0 "#475569" "start",
      towerAxis ] ++
    levelRings ++ twistEdges ++ twistDots ++
    [ card 880.0 118.0 360.0 546.0 18.0,
      text 904.0 152.0 "Why one twist is enough" 17.0 "#0f172a" "start" "bold",
      text 904.0 184.0 "Tr is 𝔽₃-linear, so for a ∈ 𝔽₃" 12.5 "#334155" "start",
      chip 1060.0 216.0 300.0 34.0 "Tr(c·a) = a · Tr(c)" "#eef2ff" "#4338ca" "#3730a3" 14.5,
      text 904.0 250.0 "— the scalar a slides straight out of the" 12.5 "#334155" "start",
      text 904.0 268.0 "orbit sum.  So if Tr(c) = 1 then" 12.5 "#334155" "start",
      chip 1060.0 300.0 300.0 34.0 "R(a) = Tr(c·a) = a" "#ecfdf5" liveGreen "#065f46" 14.5,
      text 904.0 334.0 "for every a of the prime subfield: the map" 12.5 "#334155" "start",
      text 904.0 352.0 "that killed 𝔽₃ now fixes it pointwise." 12.5 "#334155" "start",
      text 904.0 386.0 "The chosen twist" 15.0 "#0f172a" "start" "bold",
      text 904.0 410.0 "c = 2t² (code 200), Tr(c) = 1.  Its images" 12.5 "#334155" "start",
      text 904.0 428.0 "of 𝔽₃ are the green points:" 12.5 "#334155" "start",
      text 904.0 452.0 "c·0 = 000  (Tr = 0)" 12.5 "#065f46" "start" "bold",
      text 904.0 470.0 "c·1 = 200  (Tr = 1)" 12.5 "#065f46" "start" "bold",
      text 904.0 488.0 "c·2 = 100  (Tr = 2)" 12.5 "#065f46" "start" "bold",
      text 904.0 522.0 "Grey arrows: the same multiplication on" 12.5 "#94a3b8" "start",
      text 904.0 540.0 "the other 24 elements.  It is a bijection —" 12.5 "#94a3b8" "start",
      text 904.0 558.0 "the twist rearranges the field, it loses" 12.5 "#94a3b8" "start",
      text 904.0 576.0 "nothing." 12.5 "#94a3b8" "start",
      chip 1060.0 618.0 300.0 34.0 "twistImages_eq" "#f8fafc" "#cbd5e1" "#64748b" 12.0,
      text 640.0 712.0
        "Gold: 𝔽₃.  Green: its image under the twist, one point in each level.  Reading the levels off again is the repaired map R."
        13.0 "#334155",
      text 640.0 736.0 "A node abc denotes a·t² + b·t + c." 12.0 "#94a3b8" ]

/-! ## Act IV — the repaired map -/

private def fibreBox (v : ℕ) : List String :=
  let y := 132.0 + 214.0 * v.toFloat
  let xs := twistLevel v
  let chips := (xs.zipIdx).flatMap fun (x, i) =>
    let cx := 150.0 + 148.0 * (i % 3).toFloat
    let cy := y + 52.0 + 52.0 * (i / 3).toFloat
    let isP := isPrime x
    [ nodeGroup
        [ circle cx cy 20.0 (if isP then "url(#fill-gold)" else "#f1f5f9")
            (if isP then gold else "#cbd5e1") (if isP then 2.0 else 1.2),
          textMid cx cy (GF27Viz.code x) 11.5 (if isP then "#7c2d12" else "#475569") "middle"
            (if isP then "bold" else "normal") ] ]
  let arrowD := curveD 588.0 (y + 92.0) 664.0 (y + 92.0) 4.0 32.0 0.0
  [ card 80.0 y 500.0 190.0 16.0 "#ffffff" "#e2e8f0" 1.2,
    text 104.0 (y + 26.0) ("R = " ++ toString v ++ "   —   nine elements") 13.0 "#475569"
      "start" "bold",
    path arrowD "#1d4ed8" 2.0 "blue",
    comet arrowD "#93c5fd" 3.6 3.4 (0.6 * v.toFloat) 90.0,
    pulse 696.0 (y + 92.0) 40.0 "#fef3c7" 3.2 (0.4 * v.toFloat),
    circle 696.0 (y + 92.0) 28.0 "url(#fill-gold)" gold 2.0,
    textMid 696.0 (y + 92.0) (toString v) 18.0 "#7c2d12" "middle" "bold",
    selfLoop 696.0 (y + 92.0) 28.0 gold "gold",
    textMid 696.0 (y + 158.0) ("R(" ++ toString v ++ ") = " ++ toString v) 12.0 "#92400e" ] ++
  chips

/-- `svg/twist-4-repaired-map.svg` — Act IV: the twisted map as a retraction onto `𝔽₃`. -/
def act4Svg : String :=
  document 1280.0 830.0 <|
    [ text 40.0 46.0 "Act IV — the repaired map" 24.0 "#0f172a" "start" "bold",
      text 40.0 72.0
        "R(x) = Tr(2t²·x) = x.c₀ + x.c₂ : additive, 𝔽₃-linear, onto 𝔽₃, idempotent, and the identity on 𝔽₃ (twistMap_isRetraction).  Gold: the three fixed points."
        13.0 "#475569" "start",
      text 40.0 94.0
        "Each box is one fibre of R — nine elements, as for the untwisted orbit sum; what changed is that each fibre now contains exactly one point of 𝔽₃, its own value."
        12.5 "#94a3b8" "start" ] ++
    fibreBox 0 ++ fibreBox 1 ++ fibreBox 2 ++
    [ card 780.0 132.0 460.0 190.0 16.0 "#f8fafc" "#e2e8f0" 1.2,
      text 804.0 160.0 "In coordinates" 14.0 "#0f172a" "start" "bold",
      text 804.0 184.0 "Tr(x)  =  −x.c₂        (kills 𝔽₃)" 12.5 "#9f1239" "start" "bold",
      text 804.0 206.0 "R(x)  =  x.c₀ + x.c₂    (fixes 𝔽₃)" 12.5 "#065f46" "start" "bold",
      text 804.0 232.0 "The twist adds the one coordinate the" 12.0 "#334155" "start",
      text 804.0 250.0 "orbit sum could not see." 12.0 "#334155" "start",
      text 804.0 280.0 "twistMap_coords, trace3_coords" 11.0 "#94a3b8" "start",
      card 780.0 346.0 460.0 190.0 16.0 "#f8fafc" "#e2e8f0" 1.2,
      text 804.0 374.0 "What it costs" 14.0 "#0f172a" "start" "bold",
      text 804.0 398.0 "R is not multiplicative:" 12.5 "#334155" "start",
      text 804.0 422.0 "R(t²·t) = 1   but   R(t²)·R(t) = 0." 12.5 "#9f1239" "start" "bold",
      text 804.0 448.0 "The multiplicative retraction of GF(27) is" 12.0 "#334155" "start",
      text 804.0 466.0 "the orbit product N(x) = x¹³ — and that" 12.0 "#334155" "start",
      text 804.0 484.0 "one is not additive.  No map is both," 12.0 "#334155" "start",
      text 804.0 502.0 "unless the field is 𝔽ₚ itself." 12.0 "#334155" "start",
      card 780.0 560.0 460.0 190.0 16.0 "#f8fafc" "#e2e8f0" 1.2,
      text 804.0 588.0 "Idempotent" 14.0 "#0f172a" "start" "bold",
      text 804.0 612.0 "R(R(x)) = R(x): the second application" 12.0 "#334155" "start",
      text 804.0 630.0 "changes nothing, because R(x) already" 12.0 "#334155" "start",
      text 804.0 648.0 "lies in 𝔽₃, where R is the identity." 12.0 "#334155" "start",
      text 804.0 676.0 "That is precisely what makes R a" 12.0 "#334155" "start",
      text 804.0 694.0 "retraction and not merely a surjection." 12.0 "#334155" "start",
      text 804.0 722.0 "twistMap_idempotent" 11.0 "#94a3b8" "start",
      text 640.0 800.0
        "Same nine-element fibres as before, but aimed correctly: 𝔽₃ ↪ GF(27) → 𝔽₃ is the identity."
        13.0 "#334155" ]

/-! ## Act V — the space of twists -/

private def twistCards : List String :=
  (twistFunctionals.zipIdx).flatMap fun ((c, r1, rt, rt2), i) =>
    let col := (i % 3).toFloat
    let row := (i / 3).toFloat
    let x := 56.0 + 396.0 * col
    let y := 136.0 + 190.0 * row
    let chosen := decide (c = theTwist)
    [ card x y 356.0 166.0 16.0 (if chosen then "#ecfdf5" else "#ffffff")
        (if chosen then liveGreen else "#e2e8f0") (if chosen then 2.0 else 1.2),
      text (x + 24.0) (y + 34.0) ("c = " ++ GF27Viz.label c) 15.0
        (if chosen then "#065f46" else "#0f172a") "start" "bold",
      text (x + 24.0) (y + 56.0) ("code " ++ GF27Viz.code c ++ ",   Tr(c) = 1") 11.5 "#94a3b8"
        "start",
      text (x + 24.0) (y + 88.0) ("R(1)   = " ++ toString r1.c0.val) 13.0 "#334155" "start",
      text (x + 24.0) (y + 110.0) ("R(t)   = " ++ toString rt.c0.val) 13.0 "#334155" "start",
      text (x + 24.0) (y + 132.0) ("R(t²) = " ++ toString rt2.c0.val) 13.0 "#334155" "start",
      circle (x + 300.0) (y + 60.0) 15.0 "url(#fill-gold)" gold 1.6,
      textMid (x + 300.0) (y + 60.0) (toString r1.c0.val) 13.0 "#7c2d12" "middle" "bold",
      circle (x + 300.0) (y + 96.0) 15.0 "#eef2ff" "#4338ca" 1.4,
      textMid (x + 300.0) (y + 96.0) (toString rt.c0.val) 13.0 "#3730a3" "middle" "bold",
      circle (x + 300.0) (y + 132.0) 15.0 "#eef2ff" "#4338ca" 1.4,
      textMid (x + 300.0) (y + 132.0) (toString rt2.c0.val) 13.0 "#3730a3" "middle" "bold" ] ++
    (if chosen then
      [ chip (x + 178.0) (y + 12.0) 168.0 24.0 "the one drawn here" "#ecfdf5" liveGreen
          "#065f46" 11.0 ]
     else [])

/-- `svg/twist-5-nine-twists.svg` — Act V: the nine twists and the nine retractions they
give. -/
def act5Svg : String :=
  document 1280.0 780.0 <|
    [ text 40.0 50.0 "Act V — nine twists, nine repairs" 24.0 "#0f172a" "start" "bold",
      text 40.0 76.0
        "Every c with Tr(c) = 1 repairs the orbit sum, and GF(27) has nine of them — the elements with t² coordinate 2.  Different c, different retraction (twists_pairwise_distinct)."
        13.0 "#475569" "start",
      text 40.0 98.0
        "Read as 𝔽₃-linear functionals through the basis 1, t, t², the nine maps R_c are exactly the nine functionals sending 1 ↦ 1: the gold value is always 1, the two blue ones run over all nine pairs."
        12.5 "#94a3b8" "start" ] ++
    twistCards ++
    [ text 640.0 726.0
        "That count is not an accident: the twists form a coset of the kernel of Tr, of size pᵏ⁻¹ = 3² = 9, and c ↦ R_c is injective."
        13.0 "#334155",
      text 640.0 750.0
        "There is no canonical additive retraction onto 𝔽ₚ — only a canonical supply of them."
        13.0 "#0f172a" "middle" "bold" ]

/-! ## Act VI — where the twist is indispensable -/

open BigFieldSizeScan in
/-- Every field size `q ≤ 1824`, with the degree data of the scan. -/
def fieldSizes : List (ℕ × ℕ × ℕ × ℕ) :=
  bigScan.filterMap fun r =>
    match r.2 with
    | some (p, k, d) => some (r.1, p, k, d)
    | none => none

/-- The sizes with a dead additive dial, marked in the census picture. -/
def deadDialMarks : List (ℕ × ℕ × ℕ × ℕ) := fieldSizes.filter fun r => r.2.1 ∣ r.2.2.1

/-- **The marked sizes of the census picture are the seven dead dials**, and `729` is the only
one that also fails multiplicatively. -/
theorem deadDialMarks_eq :
    deadDialMarks = [(4, 2, 2, 0), (16, 2, 4, 0), (27, 3, 3, 0), (64, 2, 6, 0),
      (256, 2, 8, 0), (729, 3, 6, 1), (1024, 2, 10, 0)] ∧
    fieldSizes.length = 310 := by
  refine ⟨by decide +kernel, by decide +kernel⟩

private def censusX (i : ℕ) : Float := 70.0 + 1140.0 * i.toFloat / 309.0

private def censusTicks : List String :=
  (fieldSizes.zipIdx).flatMap fun ((_, p, k, _), i) =>
    let x := censusX i
    if p ∣ k then [] else
      [ line x 388.0 x (if k == 1 then 378.0 else 368.0) "#cbd5e1" 1.1 ]

private def expChar (k : ℕ) : String :=
  if k == 2 then "²" else if k == 3 then "³" else if k == 4 then "⁴" else
  if k == 6 then "⁶" else if k == 8 then "⁸" else "¹⁰"

/-- The dead dials, with the drawing order used to stagger their stems so that the labels of
the three small ones (`4`, `16`, `27`) do not collide. -/
private def censusMarks : List String :=
  ((fieldSizes.zipIdx).filter fun ((_, p, k, _), _) => p ∣ k).zipIdx.flatMap
    fun (((q, p, k, d), i), j) =>
      let x := censusX i
      let critical := d != 0
      let col := if critical then "#7c3aed" else deadRed
      let h := if critical then 252.0 else 128.0 + 44.0 * (j % 3).toFloat
      [ line x 388.0 x (388.0 - h) col (if critical then 3.2 else 2.4),
        circle x (388.0 - h) 7.0 (if critical then "#ede9fe" else "#fff1f2") col 2.0 ] ++
      (if critical then
        [ textMid (x + 26.0) (388.0 - h - 6.0) (toString q) 14.0 col "start" "bold",
          textMid (x + 26.0) (388.0 - h + 12.0) (toString p ++ expChar k) 11.0 "#a78bfa"
            "start" ]
       else
        [ textMid x (388.0 - h - 34.0) (toString q) 13.0 col "middle" "bold",
          textMid x (388.0 - h - 18.0) (toString p ++ expChar k) 11.0 "#94a3b8" ]) ++
      (if critical then
        [ pulse x (388.0 - h) 18.0 "#ddd6fe" 2.8 0.0,
          chip x 106.0 232.0 26.0 "also fails multiplicatively" "#f5f3ff" "#7c3aed" "#5b21b6"
            11.0 ]
       else [])

/-- `svg/twist-6-census.svg` — Act VI: the seven sizes below `1825` where the twist is not a
convenience but a necessity. -/
def act6Svg : String :=
  document 1280.0 700.0 <|
    [ text 40.0 50.0 "Act VI — where the twist is indispensable" 24.0 "#0f172a" "start" "bold",
      text 40.0 76.0
        "All 310 field sizes q = pᵏ ≤ 1824, in order.  Grey tick: p ∤ k, so rescaling the orbit sum already repairs it.  Coloured stem: p ∣ k — the dial is dead and only the twist works."
        13.0 "#475569" "start",
      line 70.0 388.0 1210.0 388.0 "#334155" 1.6 ] ++
    censusTicks ++ censusMarks ++
    [ text 70.0 412.0 "q = 2" 11.5 "#94a3b8" "start",
      text 1210.0 412.0 "q = 1681" 11.5 "#94a3b8" "end",
      card 70.0 440.0 550.0 196.0 16.0,
      text 94.0 470.0 "The ledger" 16.0 "#0f172a" "start" "bold",
      text 94.0 498.0 "rescaling  x ↦ c·Tr(x)     works ⟺ p ∤ k" 13.0 "#334155" "start",
      text 94.0 522.0 "twist        x ↦ Tr(c·x)     always works" 13.0 liveGreen "start" "bold",
      text 94.0 552.0 "and the two agree when both are available:" 12.0 "#334155" "start",
      text 94.0 574.0 "for p ∤ k the choice c = k⁻¹ turns the twist" 12.0 "#334155" "start",
      text 94.0 596.0 "back into the normalized orbit sum." 12.0 "#334155" "start",
      text 94.0 620.0 "(twistedTrace_inv_natCast_eq_normalized)" 11.0 "#94a3b8" "start",
      card 660.0 440.0 550.0 196.0 16.0,
      text 684.0 470.0 "Seven dead dials below 1825" 16.0 "#0f172a" "start" "bold",
      text 684.0 498.0 "4 = 2²,  16 = 2⁴,  27 = 3³,  64 = 2⁶," 13.0 deadRed "start" "bold",
      text 684.0 520.0 "256 = 2⁸,  729 = 3⁶,  1024 = 2¹⁰" 13.0 deadRed "start" "bold",
      text 684.0 550.0 "Of these only 729 is also a failure of the" 12.0 "#334155" "start",
      text 684.0 572.0 "multiplicative orbit product: the single size" 12.0 "#334155" "start",
      text 684.0 594.0 "in the whole scan where neither dial turns" 12.0 "#334155" "start",
      text 684.0 616.0 "and the twist is the only repair left." 12.0 "#5b21b6" "start" "bold" ]

end TwistViz
