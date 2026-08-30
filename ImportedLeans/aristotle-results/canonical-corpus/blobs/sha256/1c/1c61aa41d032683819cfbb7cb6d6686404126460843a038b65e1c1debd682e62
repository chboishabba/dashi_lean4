import RequestProject.Visualization
import RequestProject.DualFailureCensus
import RequestProject.RepairScan
import RequestProject.SvgCore

/-!
# The one-sheet infographic

`svg/infographic.svg` (`InfoViz.infographicSvg`) is a single poster summarising the whole
project: the two retraction questions, the dictionary that turns one into the other, the
Frobenius orbit picture of `GF(27)`, the dichotomy grid of characteristics and degrees, and
the headline counts.

As everywhere else in the picture layer, the *data* drawn is computed in Lean and pinned down
by kernel computation against the statements proved elsewhere:

* the four-colour status of a cell `(p, k)` of the grid is `InfoViz.cellStatus`, and
  `InfoViz.status_dual_iff` proves that its crimson value is exactly `DualDial.IsDualFailure`,
  `InfoViz.status_norm_iff` that its amber value is the failure of the orbit product
  `(p-1) ∣ (k-1)` — i.e. `FieldSizeScan.frobDefect p k ≠ 0` — and `InfoViz.status_trace_iff`
  that its blue value is the failure `p ∣ k` of the orbit sum;
* `InfoViz.grid_dual_cells` lists the crimson cells of the drawn grid: `3⁶`, `3¹²` and `5¹⁰`,
  in agreement with the census `DualDial.census_1e12`, and `InfoViz.grid_primes_prime` checks
  that the drawn rows really are primes;
* the `GF(27)` panel draws `GF27Viz.orbits`, already proved to cover `GF(27)` exactly once
  (`GF27Viz.orbits_cover`), to consist of `11` orbits of sizes `1` and `3`
  (`GF27Viz.orbits_length`, `GF27Viz.orbit_length_eq`) whose singletons are exactly the prime
  subfield (`GF27Viz.singletons_eq_primeSubfield`); `InfoViz.fixedOrbits_length` and
  `InfoViz.movedOrbits_length` check the `3 + 8` split actually drawn;
* the numbers on the score cards are the ones proved in the project: `8` is the least order of
  a group with no centre retraction
  (`CenterRetractionSmall.eight_is_least_order_without_center_retraction`), `729 = 3⁶` is
  the smallest dual-failure field size (`DualDial.min_size`, `DualDial.isDualFailure_three_six`),
  there are `7` dual failures below `10¹²` (`DualDial.census_1e12`), and of the `310` field
  sizes `q ≤ 1824` exactly `294` admit a multiplicative retraction onto the prime subfield
  while all `310` admit an additive one (`RepairScan.fullVerdict_counts`).
-/

namespace InfoViz

open SvgCore

/-! ## The status of a cell `(p, k)` of the dichotomy grid -/

/-- The Frobenius orbit product `N(x) = x^(1+p+⋯+p^(k−1))` is a retraction onto `𝔽ₚ` exactly
when `p - 1 ∣ k - 1`. -/
def normOK (p k : ℕ) : Bool := decide (p - 1 ∣ k - 1)

/-- The Frobenius orbit sum `Tr(x) = x + x^p + ⋯ + x^(p^(k−1))` is a retraction onto `𝔽ₚ`
exactly when `p ∤ k`. -/
def traceOK (p k : ℕ) : Bool := decide (¬ p ∣ k)

/-- A *multiplicative* retraction onto `𝔽ₚ` exists at all exactly when `gcd (k, p−1) = 1`
(`FrobeniusPrimeSubfield.multiplicative_retraction_iff_coprime`). -/
def multOK (p k : ℕ) : Bool := decide (Nat.gcd k (p - 1) = 1)

/-- The four-valued status of a cell: `0` both canonical maps retract, `1` the orbit product
fails, `2` the orbit sum fails, `3` both fail — a dual failure. -/
def cellStatus (p k : ℕ) : ℕ :=
  (if normOK p k then 0 else 1) + (if traceOK p k then 0 else 2)

theorem status_norm_iff (p k : ℕ) : cellStatus p k = 1 ↔ (¬ (p - 1 ∣ k - 1) ∧ ¬ p ∣ k) := by
  unfold cellStatus normOK traceOK
  by_cases h₁ : p - 1 ∣ k - 1 <;> by_cases h₂ : p ∣ k <;> simp [h₁, h₂]

theorem status_trace_iff (p k : ℕ) : cellStatus p k = 2 ↔ ((p - 1 ∣ k - 1) ∧ p ∣ k) := by
  unfold cellStatus normOK traceOK
  by_cases h₁ : p - 1 ∣ k - 1 <;> by_cases h₂ : p ∣ k <;> simp [h₁, h₂]

/-- **The crimson cells are exactly the dual failures.** -/
theorem status_dual_iff {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    cellStatus p k = 3 ↔ DualDial.IsDualFailure p k := by
  unfold cellStatus normOK traceOK DualDial.IsDualFailure
  by_cases h₁ : p - 1 ∣ k - 1 <;> by_cases h₂ : p ∣ k <;> simp [h₁, h₂, hp, hk]

/-- The green cells of a prime row are exactly the sizes where the orbit product is already a
retraction, i.e. where the Frobenius error count vanishes. -/
theorem status_zero_iff {p k : ℕ} (hp : p.Prime) :
    cellStatus p k = 0 ↔ (FieldSizeScan.frobDefect p k = 0 ∧ ¬ p ∣ k) := by
  rw [FieldSizeScan.frobDefect_eq_zero_iff hp]
  unfold cellStatus normOK traceOK
  by_cases h₁ : p - 1 ∣ k - 1 <;> by_cases h₂ : p ∣ k <;> simp [h₁, h₂]

/-! ## The drawn grid -/

/-- The characteristics drawn as rows of the grid. -/
def gridPrimes : List ℕ := [2, 3, 5, 7, 11, 13]

/-- The degrees drawn as columns of the grid. -/
def gridDegrees : List ℕ := (List.range 12).map (· + 1)

theorem grid_primes_prime : ∀ p ∈ gridPrimes, Nat.Prime p := by decide

theorem grid_degrees_eq : gridDegrees = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] := by decide

/-- The cells of the drawn grid, as pairs `(p, k)`. -/
def gridCells : List (ℕ × ℕ) :=
  gridPrimes.flatMap fun p => gridDegrees.map fun k => (p, k)

/-- **The dual failures visible on the sheet**: `3⁶ = 729`, `3¹² = 531441` and
`5¹⁰ = 9765625` — the three members of the census `DualDial.census_1e12` with `p ≤ 13` and
`k ≤ 12`. -/
theorem grid_dual_cells :
    gridCells.filter (fun c => cellStatus c.1 c.2 == 3) = [(3, 6), (3, 12), (5, 10)] := by
  decide

/-- Characteristic `2` never fails twice, and on the drawn grid it never fails at all
multiplicatively: the whole first row is green or blue. -/
theorem grid_two_row :
    ∀ k ∈ gridDegrees, cellStatus 2 k = 0 ∨ cellStatus 2 k = 2 := by decide

/-- Every cell of the drawn grid whose orbit product fails nevertheless admits *some*
multiplicative retraction unless `gcd (k, p−1) ≠ 1`; these are the cells the sheet marks with
a dot. -/
def gridRepairable : List (ℕ × ℕ) :=
  gridCells.filter (fun c => !(normOK c.1 c.2) && multOK c.1 c.2)

theorem grid_repairable_eq :
    gridRepairable = [(5, 3), (5, 7), (5, 11), (7, 5), (11, 3), (11, 7), (11, 9),
      (13, 5), (13, 7), (13, 11)] := by decide

/-! ## The `GF(27)` panel -/

/-- The three singleton Frobenius orbits of `GF(27)` — the prime subfield `𝔽₃`. -/
def fixedOrbits : List (List GF27) := GF27Viz.orbits.filter (fun o => o.length == 1)

/-- The eight three-element Frobenius orbits of `GF(27)`. -/
def movedOrbits : List (List GF27) := GF27Viz.orbits.filter (fun o => o.length == 3)

theorem fixedOrbits_length : fixedOrbits.length = 3 := by decide +kernel

theorem movedOrbits_length : movedOrbits.length = 8 := by decide +kernel

/-- The two families exhaust the eleven orbits. -/
theorem orbits_split : fixedOrbits.length + movedOrbits.length = GF27Viz.orbits.length := by
  decide +kernel

/-! ## Drawing -/

private def ink : String := "#0f172a"
private def dim : String := "#475569"
private def gold : String := "#b45309"
private def blue : String := "#1d4ed8"
private def green : String := "#047857"
private def crimson : String := "#9f1239"

/-- The fill of a grid cell of the given status. -/
def statusFill (s : ℕ) : String :=
  if s == 0 then "#bbf7d0" else if s == 1 then "#fed7aa"
  else if s == 2 then "#bfdbfe" else "#fecdd3"

/-- The stroke of a grid cell of the given status. -/
def statusStroke (s : ℕ) : String :=
  if s == 0 then green else if s == 1 then gold else if s == 2 then blue else crimson

private def panel (x y w h : Float) (n : String) (title : String) (subtitle : String)
    : List String :=
  [ card x y w h 16.0,
    rect x y w 6.0 3.0 "url(#ink)" "none" 0.0,
    chip (x + 30.0) (y + 34.0) 30.0 24.0 n "#0f172a" "#0f172a" "#f8fafc" 13.0,
    text (x + 56.0) (y + 32.0) title 19.0 ink "start" "bold",
    text (x + 56.0) (y + 52.0) subtitle 12.5 dim "start" "normal" "italic" ]

private def bullet (x y : Float) (mark : String) (col : String) (s : String)
    (size : Float := 12.5) : List String :=
  [ text x y mark size col "start" "bold",
    text (x + 17.0) y s size ink "start" "normal" ]

/-! ### Panel 1 — the group question -/

private def groupPanel : List String :=
  let x := 40.0
  let y := 104.0
  let cx := x + 148.0
  let cy := y + 168.0
  panel x y 740.0 330.0 "1" "The group question"
    "Is there a homomorphism r : G → Z(G) restricting to the identity on Z(G)?" ++
  [ circle cx cy 92.0 "url(#fill-blue)" blue 1.6,
    text cx (cy - 66.0) "G" 20.0 blue "middle" "bold",
    pulse cx (cy + 16.0) 34.0 "#fde68a" 3.0 0.0,
    circle cx (cy + 16.0) 34.0 "url(#fill-gold)" gold 1.6,
    textMid cx (cy + 16.0) "Z(G)" 13.0 gold "middle" "bold",
    curve (cx - 34.0) (cy + 16.0) (cx - 92.0) cy 0.0 0.0 20.0 gold "gold" 1.6,
    text (cx - 118.0) (cy + 52.0) "ι" 14.0 gold "middle" "bold" "italic",
    curve (cx + 92.0) cy (cx + 34.0) (cy + 16.0) 0.0 0.0 20.0 blue "blue" 1.6,
    text (cx + 118.0) (cy + 52.0) "r" 14.0 blue "middle" "bold" "italic",
    textMid cx (cy + 116.0) "r ∘ ι = id" 13.5 ink "middle" "bold" ] ++
  [ text (x + 300.0) (y + 88.0) "r exists  ⟺  Z(G) has a complement  ⟺  G ≅ N × Z(G), N centreless"
      12.5 ink "start" "bold" ] ++
  bullet (x + 300.0) (y + 116.0) "✓" green "G abelian, or Z(G) = 1" ++
  bullet (x + 300.0) (y + 140.0) "✓" green "gcd(|Z(G)|, [G : Z(G)]) = 1  (transfer)" ++
  bullet (x + 300.0) (y + 164.0) "✓" green "Dₙ  for  4 ∤ n;  Sₙ, Aₙ;  squarefree order" ++
  bullet (x + 300.0) (y + 188.0) "✓" green "products: ∏ Gᵢ retracts ⟺ every Gᵢ does" ++
  bullet (x + 300.0) (y + 220.0) "✗" crimson "nonabelian nilpotent (e.g. any p-group)" ++
  bullet (x + 300.0) (y + 244.0) "✗" crimson "Q₈ — the least failure, of order 8;  Dₙ for 4 ∣ n" ++
  bullet (x + 300.0) (y + 268.0) "✗" crimson "GL₂(R) whenever 2 ≠ 0 — and every even size" ++
  [ text (x + 300.0) (y + 300.0) "not hereditary: it passes to neither subgroups nor quotients"
      11.5 dim "start" "normal" "italic" ]

/-! ### Panel 2 — the field question -/

private def fieldPanel : List String :=
  let x := 800.0
  let y := 104.0
  let cx := x + 148.0
  let cy := y + 168.0
  panel x y 760.0 330.0 "2" "The field question"
    "Is there a retraction K = GF(pᵏ) → 𝔽ₚ built out of the Frobenius x ↦ xᵖ?" ++
  [ circle cx cy 92.0 "url(#fill-violet)" "#7c3aed" 1.6,
    text cx (cy - 66.0) "K = GF(pᵏ)" 15.0 "#7c3aed" "middle" "bold",
    pulse cx (cy + 16.0) 34.0 "#fde68a" 3.0 0.4,
    circle cx (cy + 16.0) 34.0 "url(#fill-gold)" gold 1.6,
    textMid cx (cy + 16.0) "𝔽ₚ" 14.0 gold "middle" "bold",
    selfLoop cx (cy - 62.0) 20.0 "#7c3aed" "violet",
    text cx (cy - 88.0) "x ↦ xᵖ" 13.0 "#7c3aed" "middle" "bold",
    curve (cx + 92.0) cy (cx + 34.0) (cy + 16.0) 0.0 0.0 20.0 blue "blue" 1.6,
    text (cx + 118.0) (cy + 52.0) "N, Tr" 12.5 blue "middle" "bold" "italic",
    textMid cx (cy + 116.0) "Fix(x ↦ xᵖ) = 𝔽ₚ" 13.5 gold "middle" "bold" ] ++
  [ text (x + 300.0) (y + 88.0) "orbit product   N(x) = x · xᵖ ⋯ x^(p^(k−1)) = x^((pᵏ−1)/(p−1))"
      12.5 ink "start" "bold",
    text (x + 300.0) (y + 110.0) "orbit sum       Tr(x) = x + xᵖ + ⋯ + x^(p^(k−1))"
      12.5 ink "start" "bold" ] ++
  bullet (x + 300.0) (y + 142.0) "✓" green "N retracts onto 𝔽ₚ  ⟺  p − 1 ∣ k − 1" ++
  bullet (x + 300.0) (y + 166.0) "✓" green "Tr retracts onto 𝔽ₚ  ⟺  p ∤ k" ++
  bullet (x + 300.0) (y + 198.0) "★" gold "a multiplicative retraction exists ⟺ gcd(k, p−1) = 1" ++
  bullet (x + 300.0) (y + 222.0) "★" gold "then x ↦ N(x)ᵗ works, t = k^(φ(p−1)−1)" ++
  bullet (x + 300.0) (y + 254.0) "★" gold "an additive retraction always exists: x ↦ Tr(c·x)," ++
  [ text (x + 317.0) (y + 276.0) "for any c with Tr(c) = 1 — no field is beyond repair"
      12.5 ink "start" "normal",
    text (x + 300.0) (y + 304.0)
      "both maps are transfers: N is the transfer of 𝔽ₚˣ ≤ Kˣ" 11.5 dim "start" "normal"
      "italic" ]

/-! ### Panel 3 — the dictionary -/

/-- The ten lines of the dictionary printed on the sheet. -/
def dictionary : List (String × String) :=
  [ ("centre  Z(G) ≤ G", "prime subfield  𝔽ₚ ≤ K"),
    ("conjugation  g ↦ hgh⁻¹", "Frobenius  x ↦ xᵖ"),
    ("Z(G) = fixed points", "𝔽ₚ = Fix(Frobenius)"),
    ("index  [G : Z(G)]", "degree  k = [K : 𝔽ₚ]"),
    ("transfer  V : G → Z(G)", "orbit product  N(x) = ∏ x^(p^i)"),
    ("V|Z(G) : z ↦ z^[G:Z(G)]", "N|𝔽ₚ : a ↦ a^(1+p+⋯+p^(k−1))"),
    ("coprime index ⇒ retraction", "gcd(k, p−1) = 1 ⇒ retraction"),
    ("Schur–Zassenhaus complement", "Hilbert 90 / Artin–Schreier"),
    ("Q₈ : least obstruction", "3⁶ = 729 : least dual failure"),
    ("kernel of r, centreless core", "kernel of Tr, additive core") ]

theorem dictionary_length : dictionary.length = 10 := by decide

private def dictPanel : List String :=
  let x := 40.0
  let y := 452.0
  let rowY := fun (i : ℕ) => y + 92.0 + i.toFloat * 24.0
  panel x y 740.0 348.0 "3" "The dictionary"
    "One transfer argument, read twice: the group column becomes the field column." ++
  [ text (x + 40.0) (y + 78.0) "GROUPS" 12.0 blue "start" "bold",
    text (x + 400.0) (y + 78.0) "FINITE FIELDS" 12.0 "#7c3aed" "start" "bold",
    line (x + 386.0) (y + 84.0) (x + 386.0) (y + 332.0) "#e2e8f0" 1.2 ] ++
  (dictionary.zipIdx.flatMap fun (row, i) =>
    [ rect (x + 28.0) (rowY i - 15.0) 684.0 22.0 6.0
        (if i % 2 == 0 then "#f8fafc" else "#ffffff") "none" 0.0,
      text (x + 40.0) (rowY i) row.1 12.0 ink "start" "normal",
      text (x + 372.0) (rowY i) "↔" 12.0 gold "middle" "bold",
      text (x + 400.0) (rowY i) row.2 12.0 ink "start" "normal" ])

/-! ### Panel 4 — the orbits of `GF(27)` -/

private def orbitTriangle (cx cy r : Float) (o : List GF27) : List String :=
  let pos : ℕ → Float × Float := fun i =>
    let a := -1.5707963 + i.toFloat * 2.0943951
    (cx + r * Float.cos a, cy + r * Float.sin a)
  let edges := (List.range 3).map fun i =>
    let (x₁, y₁) := pos i
    let (x₂, y₂) := pos ((i + 1) % 3)
    arrow x₁ y₁ x₂ y₂ 12.0 14.0 "#94a3b8" "slate" 1.2
  let dots := (o.zipIdx.map fun (v, i) =>
    let (px, py) := pos i
    nodeGroup
      [ circle px py 12.0 "url(#fill-violet)" "#7c3aed" 1.2,
        textMid px py (GF27Viz.label v) 8.5 ink "middle" "normal" ])
  edges ++ dots

private def orbitPanel : List String :=
  let x := 800.0
  let y := 452.0
  panel x y 760.0 348.0 "4" "Frobenius orbits of GF(27)"
    "27 elements, 11 orbits: three fixed points and eight 3-cycles." ++
  [ rect (x + 30.0) (y + 84.0) 176.0 236.0 12.0 "#fffbeb" gold 1.2 "4 4",
    text (x + 118.0) (y + 106.0) "𝔽₃ = Fix(x ↦ x³)" 12.5 gold "middle" "bold" ] ++
  ((fixedOrbits.flatten).zipIdx.flatMap fun (v, i) =>
    [ pulse (x + 118.0) (y + 150.0 + i.toFloat * 56.0) 17.0 "#fde68a" 2.4 (i.toFloat * 0.5),
      circle (x + 118.0) (y + 150.0 + i.toFloat * 56.0) 17.0 "url(#fill-gold)" gold 1.4,
      textMid (x + 118.0) (y + 150.0 + i.toFloat * 56.0) (GF27Viz.label v) 10.0 ink
        "middle" "bold" ]) ++
  [ text (x + 118.0) (y + 308.0) "x³ = x" 11.5 gold "middle" "normal" "italic" ] ++
  (movedOrbits.zipIdx.flatMap fun (o, i) =>
    orbitTriangle (x + 300.0 + (i % 4).toFloat * 116.0)
      (y + 154.0 + (i / 4).toFloat * 122.0) 30.0 o) ++
  [ text (x + 532.0) (y + 330.0)
      "each 3-cycle is one Galois orbit; the orbit product x ↦ x¹³ collapses them to 𝔽₃"
      11.5 dim "middle" "normal" "italic" ]

/-! ### Panel 5 — the dichotomy grid -/

private def gridPanel : List String :=
  let x := 40.0
  let y := 818.0
  let x0 := x + 92.0
  let y0 := y + 104.0
  let cw := 40.0
  let ch := 30.0
  panel x y 860.0 336.0 "5" "Which dial is alive?"
    "Rows: characteristic p.  Columns: degree k.  The colour of GF(pᵏ)." ++
  ((gridDegrees.zipIdx).map fun (k, j) =>
    text (x0 + (j.toFloat + 0.5) * cw) (y0 - 10.0) (toString k) 11.5 dim "middle" "bold") ++
  [ text (x0 - 34.0) (y0 - 10.0) "k =" 11.5 dim "middle" "bold" ] ++
  (gridPrimes.zipIdx.flatMap fun (p, i) =>
    text (x0 - 16.0) (y0 + (i.toFloat + 0.5) * ch + 4.0) ("p = " ++ toString p) 11.5 dim
      "end" "bold" ::
    (gridDegrees.zipIdx.flatMap fun (k, j) =>
      let s := cellStatus p k
      let px := x0 + j.toFloat * cw
      let py := y0 + i.toFloat * ch
      [ rect (px + 1.5) (py + 1.5) (cw - 3.0) (ch - 3.0) 5.0 (statusFill s)
          (statusStroke s) 1.1 "" "class=\"cell\"" ] ++
      (if s == 3 then
        [ textMid (px + cw / 2.0) (py + ch / 2.0) "✗✗" 11.0 crimson "middle" "bold" ]
       else if multOK p k && !(normOK p k) then
        [ circle (px + cw / 2.0) (py + ch / 2.0) 3.2 gold "none" 0.0 ]
       else []))) ++
  [ text (x + 40.0) (y + 274.0) "legend" 11.0 dim "start" "bold",
    rect (x + 92.0) (y + 264.0) 14.0 14.0 4.0 (statusFill 0) (statusStroke 0) 1.1,
    text (x + 112.0) (y + 275.0) "both N and Tr retract" 11.5 ink "start" "normal",
    rect (x + 256.0) (y + 264.0) 14.0 14.0 4.0 (statusFill 1) (statusStroke 1) 1.1,
    text (x + 276.0) (y + 275.0) "N fails (p−1 ∤ k−1)" 11.5 ink "start" "normal",
    rect (x + 414.0) (y + 264.0) 14.0 14.0 4.0 (statusFill 2) (statusStroke 2) 1.1,
    text (x + 434.0) (y + 275.0) "Tr fails (p ∣ k)" 11.5 ink "start" "normal",
    rect (x + 560.0) (y + 264.0) 14.0 14.0 4.0 (statusFill 3) (statusStroke 3) 1.1,
    text (x + 580.0) (y + 275.0) "dual failure — only the twist Tr(c·x) survives" 11.5 ink
      "start" "normal",
    circle (x + 99.0) (y + 300.0) 3.2 gold "none" 0.0,
    text (x + 112.0) (y + 304.0)
      "a gold dot marks a dead orbit product that a power map x ↦ N(x)ᵗ still repairs"
      11.5 ink "start" "normal" ]

/-! ### Panel 6 — the counts -/

/-- The score cards: headline number, caption, colour. -/
def scoreCards : List (String × String × String) :=
  [ ("8", "least order of a group with no centre retraction — Q₈", crimson),
    ("729 = 3⁶", "smallest field where both canonical maps die", crimson),
    ("7", "dual failures among all field sizes below 10¹²", gold),
    ("294 / 310", "field sizes q ≤ 1824 with a multiplicative retraction", blue),
    ("310 / 310", "of them with an additive retraction — the twist never fails", green) ]

theorem scoreCards_length : scoreCards.length = 5 := by decide

private def countPanel : List String :=
  let x := 920.0
  let y := 818.0
  panel x y 640.0 336.0 "6" "The score"
    "Everything below is proved in Lean, most of it by kernel computation." ++
  (scoreCards.zipIdx.flatMap fun (c, i) =>
    let cy := y + 100.0 + i.toFloat * 46.0
    [ rect (x + 28.0) (cy - 18.0) 584.0 38.0 10.0 "#f8fafc" "#e2e8f0" 1.1,
      text (x + 150.0) (cy + 6.0) c.1 19.0 c.2.2 "middle" "bold",
      text (x + 276.0) (cy + 5.0) c.2.1 12.0 ink "start" "normal" ]) ++
  [ text (x + 320.0) (y + 320.0)
      "no dual failure in characteristic 2, and none with k = p" 11.5 dim "middle" "normal"
      "italic" ]

/-! ### The sheet -/

/-- **The one-sheet infographic**, written to `svg/infographic.svg`. -/
def infographicSvg : String :=
  document 1600.0 1216.0
    ([ rect 0.0 0.0 1600.0 92.0 0.0 "url(#ink)" "none" 0.0,
       text 40.0 46.0 "Two retractions, one transfer" 30.0 "#f8fafc" "start" "bold",
       text 40.0 72.0
         "onto the centre of a group  ·  onto the prime subfield of a finite field"
         14.0 "#c7d2fe" "start" "normal" "italic",
       text 1560.0 44.0 "formalised in Lean 4 + Mathlib" 13.0 "#e0e7ff" "end" "bold",
       text 1560.0 68.0 "every picture generated from checked data" 12.0 "#a5b4fc" "end"
         "normal" "italic" ] ++
     groupPanel ++ fieldPanel ++ dictPanel ++ orbitPanel ++ gridPanel ++ countPanel ++
     [ text 800.0 1194.0
         ("Z(G) ↔ 𝔽ₚ  ·  conjugation ↔ Frobenius  ·  transfer ↔ orbit product  ·  " ++
          "the obstruction is an index, and the repair is a twist")
         12.5 dim "middle" "normal" "italic" ])

end InfoViz
