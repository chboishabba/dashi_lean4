import RequestProject.Anim3D
import RequestProject.RepairScan

/-!
# The repair in three dimensions

Two rotating three-dimensional pictures explaining *how* the Frobenius orbit product fails to
be a retraction onto the prime subfield, and *how* the failure is repaired.

## `svg/repair-wheel-3d.svg` — the collapse onto the prime dial

The multiplicative group `GF(125)ˣ` is cyclic of order `124`: fix a generator `g` and label
the nonzero elements by their discrete logarithm `j`, so that multiplication becomes addition
of labels mod `124`.  The picture draws the `124` labels as spheres on a slowly rotating
horizontal wheel.  The prime subfield `𝔽₅ˣ = {1, 2, 3, 4}` is the subgroup of index
`s = 1 + 5 + 5² = 31`, i.e. the labels `0, 31, 62, 93` (`wheelSubgroupIndices`), lifted onto
the small wheel above.

The orbit product `N(x) = x · x⁵ · x²⁵ = x³¹` reads on labels as `j ↦ 31·j mod 124`
(`normIndexMap_lands_in_subgroup`), which is why it always lands in the prime subfield: it is
the *collapse of the big wheel onto the small one*.  Four Frobenius orbits `{j, 5j, 25j}` are
drawn collapsing to their common image.

Restricted to the small wheel the collapse is not the identity but the *gear ratio* `k = 3`:
in the coordinate `u` with label `31u` it is `u ↦ 3u mod 4` (`dialMap125`), which fixes `2` of
the `4` points and moves the other `2` — exactly the error `frobDefect 5 3 = 2` of the scan
(`dialMap125_error`).  Since `gcd(3, 4) = 1` the gear ratio can be inverted (`3·3 ≡ 1 mod 4`),
and the repaired map is `x ↦ N(x)³ = x⁹³` (`RepairScan.repair_exponents`).

## `svg/repair-gears-3d.svg` — the two dials of a finite field

Every repair question is a question about one of two dials, drawn here for three fields.

* The **multiplicative dial** is `𝔽ₚˣ ≅ ℤ/(p−1)`, written additively in the discrete
  logarithm.  On it the orbit product `N` is multiplication by `k`.  It can be undone exactly
  when `k` is invertible mod `p − 1`, i.e. when `gcd (k, p − 1) = 1`
  (`FrobeniusPrimeSubfield.multiplicative_retraction_iff_coprime`).
* The **additive dial** is `𝔽ₚ ≅ ℤ/p`.  On it the orbit sum `Tr` is multiplication by `k`.
  Rescaling undoes it exactly when `p ∤ k`; when `p ∣ k` the dial is dead
  (`FrobeniusPrimeSubfield.no_scalar_repair_of_dvd`) and one twists the *input* instead,
  `x ↦ Tr(c·x)` with `Tr(c) = 1`, which always works
  (`FrobeniusPrimeSubfield.twistedTrace_isRetraction`).

The three columns are `GF(9)` (multiplicative dial jammed, additive dial repairable),
`GF(125)` (both repairable) and `GF(729)` (both dials jammed — the only size in the scan
where even the rescaling fails, so that the twist is needed).  The gear ratios drawn are
pinned down by `dialTable_eq`.
-/

namespace Repair3D

open SvgCore Anim3D

/-! ## The data drawn, checked by computation -/

/-- The labels of the prime subfield `𝔽₅ˣ` inside `GF(125)ˣ ≅ ℤ/124`: the multiples of the
orbit exponent `s = 31`. -/
theorem wheelSubgroupIndices :
    (List.range 124).filter (fun j => j % 31 == 0) = [0, 31, 62, 93] := by decide

/-- The orbit product acts on labels as `j ↦ 31·j mod 124`, and every value is a multiple of
`31` — the collapse of the big wheel onto the small one. -/
theorem normIndexMap_lands_in_subgroup :
    ((List.range 124).map fun j => (31 * j) % 124 % 31).all (· == 0) = true := by decide

/-- On the small wheel, in the coordinate `u` with label `31u`, the collapse is the gear
ratio `k = 3`: `u ↦ 3u mod 4`. -/
theorem dialMap125 :
    ((List.range 4).map fun u => (31 * (31 * u) % 124) / 31) = [0, 3, 2, 1] ∧
      ((List.range 4).map fun u => (3 * u) % 4) = [0, 3, 2, 1] := by
  refine ⟨by decide, by decide⟩

/-- The gear ratio `3` on `ℤ/4` moves `2` of the `4` points, matching the scan's error
`frobDefect 5 3 = 2` for `q = 125`. -/
theorem dialMap125_error :
    ((List.range 4).filter fun u => (3 * u) % 4 != u).length = FieldSizeScan.frobDefect 5 3 := by
  decide

/-- The three fields of `svg/repair-gears-3d.svg`, each with its two dials: for `q = p^k` the
multiplicative dial `ℤ/(p−1)` and the additive dial `ℤ/p`, both carrying multiplication by
`k`, together with the number of points each dial moves and whether the dial can be undone. -/
def dialTable : List (ℕ × ℕ × ℕ × (ℕ × ℕ × Bool) × (ℕ × ℕ × Bool)) :=
  [(9, 3, 2), (125, 5, 3), (729, 3, 6)].map fun (q, p, k) =>
    (q, p, k,
      (p - 1, ((List.range (p - 1)).filter fun u => (k * u) % (p - 1) != u).length,
        Nat.gcd k (p - 1) == 1),
      (p, ((List.range p).filter fun a => (k * a) % p != a).length, ¬ (p ∣ k)))

/-- The gear data drawn in `svg/repair-gears-3d.svg`.  Reading the rows: `GF(9)` has a jammed
multiplicative dial (ratio `2` on `ℤ/2` moves `1` point and is not invertible) and a working
additive dial (ratio `2` on `ℤ/3`); `GF(125)` has both dials invertible; `GF(729)` has both
dials jammed, the ratio `6` being `0` both mod `2` and mod `3`. -/
theorem dialTable_eq :
    dialTable =
      [(9, 3, 2, (2, 1, false), (3, 2, true)),
       (125, 5, 3, (4, 2, true), (5, 4, true)),
       (729, 3, 6, (2, 1, false), (3, 2, false))] := by
  rfl

/-- The number of points moved by the multiplicative dial is exactly the error of the scan. -/
theorem dialTable_matches_scan :
    (dialTable.map fun r => (r.1, r.2.2.2.1.2.1)) = [(9, 1), (125, 2), (729, 1)] ∧
      [FieldSizeScan.frobDefect 3 2, FieldSizeScan.frobDefect 5 3,
        FieldSizeScan.frobDefect 3 6] = [1, 2, 1] := by
  refine ⟨by decide, by decide⟩

/-! ## Picture 1: the wheel of `GF(125)` collapsing onto `𝔽₅` -/

private def wheelCam : Cam := ⟨430.0, 530.0, 212.0, 0.42⟩

private def spinDur : Float := 24.0

/-- The Frobenius orbits `{j, 5j, 25j}` drawn collapsing onto their image `31j`. -/
def drawnOrbits : List ℕ := [4, 1, 2, 3]

theorem drawnOrbits_are_orbits :
    drawnOrbits.map (fun j => [j, 5 * j % 124, 25 * j % 124]) =
      [[4, 20, 100], [1, 5, 25], [2, 10, 50], [3, 15, 75]] ∧
    drawnOrbits.map (fun j => (31 * j) % 124) = [0, 31, 62, 93] := by
  refine ⟨by decide, by decide⟩

private def orbitColors : List String := ["#1d4ed8", "#be185d", "#047857", "#7c3aed"]

private def wheelDots : List String :=
  (List.range 124).map fun j =>
    let p := ringPoint 124 j 1.0 0.0
    if j % 31 == 0 then
      spinDot wheelCam p 7.0 "url(#fill-gold)" "#b45309" spinDur 1.4
    else
      spinDot wheelCam p 3.4 "#cbd5e1" "#94a3b8" spinDur 0.7

private def dialZ : Float := 1.5
private def dialR : Float := 0.52

private def dialDots : List String :=
  (List.range 4).map fun u =>
    spinDot wheelCam (ringPoint 4 u dialR dialZ) 10.5 "url(#fill-gold)" "#b45309" spinDur 1.6

private def dialLabels : List String :=
  (List.range 4).map fun u =>
    spinLabel wheelCam (ringPoint 4 u dialR dialZ) (toString (31 * u)) 11.0 "#7c2d12" spinDur
      22.0 "bold"

/-- The collapse arrows: every member of a drawn orbit is joined to the small-wheel point it
is sent to. -/
private def collapseEdges : List String :=
  (List.zip drawnOrbits orbitColors).zipIdx.flatMap fun ((j, col), o) =>
    let target := (31 * j) % 124
    let u := target / 31
    -- each orbit lights up in turn, so that the collapse is seen happening orbit by orbit
    let pulse :=
      "<animate attributeName=\"opacity\" values=\"0.18;0.95;0.18\" dur=\"6s\" begin=\"" ++
        num (1.5 * o.toFloat) ++ "s\" repeatCount=\"indefinite\"/>"
    [j, 5 * j % 124, 25 * j % 124].map fun i =>
      spinEdge wheelCam (ringPoint 124 i 1.0 0.0) (ringPoint 4 u dialR dialZ) 5.0 10.0 col
        spinDur 1.6 0.6 "" "" pulse

/-- The error on the small wheel: the gear ratio `u ↦ 3u`, in crimson where it moves the
point and in green where it fixes it. -/
private def dialArrows : List String :=
  (List.range 4).flatMap fun u =>
    let v := (3 * u) % 4
    if v == u then
      [spinDot wheelCam (ringPoint 4 u dialR dialZ) 15.0 "none" "#047857" spinDur 2.4]
    else
      [spinEdge wheelCam (ringPoint 4 u dialR (dialZ + 0.06 * u.toFloat))
        (ringPoint 4 v dialR (dialZ + 0.06 * u.toFloat)) 12.0 15.0 "#be185d" spinDur 2.6 0.95
        "" "marker-end=\"url(#arrow-pink)\""]

private def wheelLegend : List String :=
  [ card 880.0 118.0 360.0 545.0 16.0,
    text 900.0 152.0 "How the collapse works" 17.0 "#0f172a" "start" "bold",
    text 900.0 182.0 "GF(125)ˣ is cyclic of order 124.  Write each" 12.5 "#334155" "start",
    text 900.0 200.0 "nonzero x as gʲ: multiplying elements adds" 12.5 "#334155" "start",
    text 900.0 218.0 "labels mod 124.  The big wheel is j = 0…123." 12.5 "#334155" "start",
    text 900.0 250.0 "N(x) = x · x⁵ · x²⁵ = x³¹" 14.0 "#1d4ed8" "start" "bold",
    text 900.0 272.0 "on labels:  j ↦ 31·j  (mod 124)." 12.5 "#334155" "start",
    text 900.0 290.0 "Every value is a multiple of 31, so N lands in" 12.5 "#334155" "start",
    text 900.0 308.0 "the subgroup of index 31 — that subgroup is 𝔽₅ˣ," 12.5 "#334155" "start",
    text 900.0 326.0 "the small wheel.  This is the retraction idea:" 12.5 "#334155" "start",
    text 900.0 344.0 "a whole Frobenius orbit {j, 5j, 25j} is crushed" 12.5 "#334155" "start",
    text 900.0 362.0 "onto one point of the prime field." 12.5 "#334155" "start",
    text 900.0 396.0 "Why it is not yet a retraction" 15.0 "#0f172a" "start" "bold",
    text 900.0 420.0 "On the small wheel, with label 31u, the map is" 12.5 "#334155" "start",
    text 900.0 438.0 "u ↦ 3u (mod 4):  the gear ratio is k = 3." 12.5 "#be185d" "start" "bold",
    text 900.0 458.0 "It fixes u = 0, 2 and moves u = 1, 3 — the error 2" 12.5 "#334155" "start",
    text 900.0 476.0 "that the scan records at q = 125." 12.5 "#334155" "start",
    text 900.0 510.0 "The repair" 15.0 "#0f172a" "start" "bold",
    text 900.0 534.0 "gcd(3, 4) = 1, so the gear can be turned back:" 12.5 "#334155" "start",
    text 900.0 552.0 "3 · 3 ≡ 1 (mod 4), hence" 12.5 "#334155" "start",
    text 900.0 578.0 "R(x) = N(x)³ = x⁹³" 15.0 "#047857" "start" "bold",
    text 900.0 600.0 "is multiplicative, lands in 𝔽₅ and fixes it" 12.5 "#334155" "start",
    text 900.0 618.0 "pointwise: a true multiplicative retraction." 12.5 "#334155" "start",
    text 900.0 644.0 "(GF(9) has gcd(2,2) = 2 — there no repair exists.)" 11.5 "#64748b" "start" ]

/-- `svg/repair-wheel-3d.svg`: the rotating wheel of `GF(125)ˣ` collapsing onto the prime
dial `𝔽₅ˣ`. -/
def wheelSvg : String :=
  document 1280.0 760.0 <|
    [ text 40.0 54.0 "The Frobenius orbit product as a collapse onto the prime dial" 22.0
        "#0f172a" "start" "bold",
      text 40.0 80.0
        "GF(125)ˣ ≅ ℤ/124 (big wheel)  —  N(x) = x³¹ ⟶  𝔽₅ˣ ≅ ℤ/4 (small wheel).  Rotating: one turn every 24 s."
        13.0 "#475569" "start",
      ringOutline wheelCam 1.0 0.0 "#94a3b8" 1.0 "4 5" 0.55,
      ringOutline wheelCam dialR dialZ "#b45309" 1.2 "" 0.65 ] ++
    collapseEdges ++ wheelDots ++ dialArrows ++ dialDots ++ dialLabels ++
    [ text 430.0 118.0 "𝔽₅ˣ — the retract, a dial with 4 positions" 13.5 "#b45309" "middle"
        "bold",
      text 70.0 208.0 "on the dial:  u ↦ 3u (mod 4)" 13.0 "#be185d" "start" "bold",
      text 70.0 228.0 "crimson = moved (2 points — the error)" 11.5 "#64748b" "start",
      text 70.0 246.0 "green ring = fixed (2 points)" 11.5 "#64748b" "start",
      text 430.0 700.0 "GF(125)ˣ — 124 points, labelled by discrete logarithm" 13.0 "#475569",
      text 430.0 722.0 "gold = the 4 points of the prime subfield (labels 0, 31, 62, 93)" 12.0
        "#94a3b8" ] ++
    wheelLegend

/-! ## Picture 2: the two dials of three fields -/

private structure DialSpec where
  title : String
  ratio : ℕ
  modulus : ℕ
  colour : String
  cam : Cam

private def dialSpinDur : Float := 18.0

/-- One dial: `n` points on a rotating ring, with an arrow from each point `u` to `k·u mod n`,
green where the point is fixed and crimson where it is moved. -/
private def dialScene (d : DialSpec) : List String :=
  let n := d.modulus
  let ring := ringOutline d.cam 1.0 0.0 "#cbd5e1" 1.0 "3 4" 0.7
  let dots := (List.range n).map fun u =>
    let moved := (d.ratio * u) % n != u
    spinDot d.cam (ringPoint n u 1.0 0.0) 8.0
      (if moved then "#fecdd3" else "#d1fae5") (if moved then "#be185d" else "#047857")
      dialSpinDur 1.4
  let labels := (List.range n).map fun u =>
    spinLabel d.cam (ringPoint n u 1.0 0.0) (toString u) 10.5 "#0f172a" dialSpinDur 0.0 "bold"
  let arrows := (List.range n).flatMap fun u =>
    let v := (d.ratio * u) % n
    if v == u then []
    else [spinEdge d.cam (ringPoint n u 1.0 0.0) (ringPoint n v 1.0 0.0) 10.0 13.0 "#be185d"
            dialSpinDur 2.2 0.95 "" "marker-end=\"url(#arrow-pink)\""]
  let hub :=
    [ circle d.cam.cx d.cam.cy 21.0 "#ffffff" d.colour 1.6,
      textMid d.cam.cx d.cam.cy ("×" ++ toString d.ratio) 14.0 d.colour "middle" "bold" ]
  (ring :: arrows) ++ dots ++ labels ++ hub

private def dialCam (cx cy : Float) : Cam := ⟨cx, cy, 98.0, 0.45⟩

private def columnX : List Float := [230.0, 640.0, 1050.0]

private def multRow : List (String × ℕ × ℕ × Bool × String) :=
  [ ("GF(9) = 3²", 2, 2, false, "gcd(2, 2) = 2  ✗  jammed"),
    ("GF(125) = 5³", 3, 4, true, "gcd(3, 4) = 1  ✓  invert: t = 3"),
    ("GF(729) = 3⁶", 6, 2, false, "gcd(6, 2) = 2  ✗  jammed") ]

private def addRow : List (String × ℕ × ℕ × Bool × String) :=
  [ ("GF(9) = 3²", 2, 3, true, "3 ∤ 2  ✓  divide by k: 2⁻¹ = 2"),
    ("GF(125) = 5³", 3, 5, true, "5 ∤ 3  ✓  divide by k: 3⁻¹ = 2"),
    ("GF(729) = 3⁶", 6, 3, false, "3 ∣ 6  ✗  dial dead — twist instead") ]

private def rowScenes (row : List (String × ℕ × ℕ × Bool × String)) (cy : Float)
    (label : String) : List String :=
  (List.zip columnX row).flatMap fun (cx, (title, k, n, ok, verdict)) =>
    dialScene ⟨title, k, n, if ok then "#047857" else "#be185d", dialCam cx cy⟩ ++
    [ text cx (cy - 122.0) title 15.0 "#0f172a" "middle" "bold",
      text cx (cy - 102.0) ("dial " ++ label ++ ",  ratio ×" ++ toString k) 12.0 "#475569",
      chip cx (cy + 122.0) 300.0 26.0 verdict
        (if ok then "#ecfdf5" else "#fff1f2") (if ok then "#047857" else "#be185d")
        (if ok then "#065f46" else "#9f1239") 12.0 ]

/-- `svg/repair-gears-3d.svg`: the multiplicative dial `ℤ/(p−1)` and the additive dial `ℤ/p`
of `GF(9)`, `GF(125)` and `GF(729)`, each turning in three dimensions and each carrying the
gear ratio `k`. -/
def gearsSvg : String :=
  document 1280.0 850.0 <|
    [ text 40.0 50.0 "Both repairs are one question: can the gear ratio k be turned back?" 22.0
        "#0f172a" "start" "bold",
      text 40.0 76.0
        "Restricted to the prime field, the orbit product is the exponent k and the orbit sum is the scalar k.  Crimson arrows are moved points."
        13.0 "#475569" "start",
      card 40.0 100.0 1200.0 336.0 16.0,
      text 60.0 128.0 "Multiplicative dial   𝔽ₚˣ ≅ ℤ/(p−1),   N = ×k" 15.0 "#1d4ed8" "start"
        "bold",
      card 40.0 456.0 1200.0 340.0 16.0,
      text 60.0 484.0 "Additive dial   𝔽ₚ ≅ ℤ/p,   Tr = ×k" 15.0 "#7c3aed" "start" "bold" ] ++
    rowScenes multRow 292.0 "ℤ/(p−1)" ++
    rowScenes addRow 648.0 "ℤ/p" ++
    [ text 640.0 826.0
        "A repair exists exactly when the ratio is invertible: gcd(k, p−1) = 1 multiplicatively, p ∤ k additively — and when the additive dial is dead, twisting the input still works."
        13.0 "#334155" ]

end Repair3D
