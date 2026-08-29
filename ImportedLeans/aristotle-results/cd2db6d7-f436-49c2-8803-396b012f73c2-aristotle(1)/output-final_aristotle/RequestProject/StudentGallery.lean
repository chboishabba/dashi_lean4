import RequestProject.StudentPosters
import RequestProject.PascalExpanded

/-!
# Drawing the six student posters

The rendering half of `RequestProject/StudentPosters.lean`: pure string manipulation on top of
`RequestProject.SvgCore`, using only data that the previous file has pinned down.

Written into `svg/` by `scripts/GenerateSvg.lean`:

| poster | function |
| --- | --- |
| `svg/student-1-freshmans-dream.svg` | `StudentViz.dreamSvg` |
| `svg/student-2-cyclotomic-clocks.svg` | `StudentViz.clocksSvg` |
| `svg/student-3-subfield-tower.svg` | `StudentViz.towerSvg` |
| `svg/student-4-dictionary.svg` | `StudentViz.dictionarySvg` |
| `svg/student-5-orbit-spiral.svg` | `StudentViz.spiralSvg` |
| `svg/student-6-exercise-ladder.svg` | `StudentViz.ladderSvg` |
-/

namespace StudentViz

open SvgCore

private def pi : Float := 3.14159265358979

/-- The title and subtitle at the top of every poster. -/
private def titleBlock (w : Float) (title subtitle : String) : List String :=
  [ text (w / 2.0) 52.0 title 28.0 "url(#ink)" "middle" "bold",
    text (w / 2.0) 82.0 subtitle 15.0 "#475569" ]

/-- The small "made in Lean" strip at the bottom of every poster. -/
private def footStrip (w h : Float) (s : String) : List String :=
  [ rect 0.0 (h - 40.0) w 40.0 0.0 "#0f172a" "none" 0.0,
    text (w / 2.0) (h - 15.0) s 12.5 "#94a3b8" ]

/-- A natural number written as a Unicode superscript, for labels like `GF(2¹²)`. -/
private def sup (n : Nat) : String :=
  String.join ((toString n).toList.map fun c =>
    match c with
    | '0' => "⁰" | '1' => "¹" | '2' => "²" | '3' => "³" | '4' => "⁴"
    | '5' => "⁵" | '6' => "⁶" | '7' => "⁷" | '8' => "⁸" | '9' => "⁹"
    | _ => "")

/-- A block of left-aligned lines inside a card. -/
private def lines (x y lead size : Float) (col : String) (ls : List String) : List String :=
  (ls.zipIdx).map fun (s, i) => text x (y + lead * i.toFloat) s size col "start"

/-! ## Poster 1 — the freshman's dream -/

/-- The colour of a nonzero residue in the small companion triangles. -/
private def residueColour (v : Nat) : String :=
  ["#1d4ed8", "#be185d", "#047857", "#7c3aed", "#b45309", "#0891b2"].getD ((v + 5) % 6) "#1d4ed8"

/-- A small companion triangle: `rows` rows of Pascal's triangle mod `p`, one square per entry
that is *not* divisible by `p`, so the self-similar pattern is what one sees. -/
private def miniTriangle (p rows : Nat) (cx top cell : Float) : List String :=
  (List.range rows).flatMap fun n =>
    (List.range (n + 1)).filterMap fun i =>
      let v := Nat.choose n i % p
      if v == 0 then none
      else
        let x := cx - n.toFloat * cell / 2.0 + i.toFloat * cell
        let y := top + n.toFloat * cell
        some (rect (x - cell / 2.0 + 0.35) (y - cell / 2.0 + 0.35) (cell - 0.7) (cell - 0.7) 0.7
          (residueColour v) "none" 0.0)

/-- `svg/student-1-freshmans-dream.svg`: Pascal's triangle mod 3, twenty-seven rows of it — the
reason `x ↦ x³` is additive, and the reason every iterate `x ↦ x^(3ʲ)` is too. -/
def dreamSvg : String :=
  let w := 1560.0
  let h := 1264.0
  let rows := 26
  let dx := 26.0
  let dy := 37.0
  let top := 196.0
  let cx0 := 420.0
  let cellX (n i : Nat) : Float := cx0 - n.toFloat * dx / 2.0 + i.toFloat * dx
  let cellY (n : Nat) : Float := top + n.toFloat * dy
  let isPow3 (n : Nat) : Bool := n == 1 || n == 3 || n == 9
  let bands := (List.range (rows + 1)).filterMap fun n =>
    if isPow3 n then
      some (rect (cellX n 0 - 22.0) (cellY n - 17.0) (n.toFloat * dx + 44.0) 34.0 17.0
        "#fef3c7" "#f59e0b" 1.4)
    else none
  let labels := (List.range (rows + 1)).flatMap fun n =>
    [ text (cellX n 0 - 34.0) (cellY n + 4.0) ("n = " ++ toString n) 11.5
        (if isPow3 n then "#b45309" else "#94a3b8") "end",
      text (cellX n n + 34.0) (cellY n + 4.0) (toString (PascalAtlas.rowSurvivors 3 n)) 11.0
        (if isPow3 n then "#b45309" else "#cbd5e1") "start" ]
  let cells := (List.range (rows + 1)).flatMap fun n =>
    (List.range (n + 1)).map fun i =>
      let x := cellX n i
      let y := cellY n
      let v := pascalCell 3 n i
      let fill := if v == 0 then "#eef2f6" else if v == 1 then "url(#fill-blue)"
        else "url(#fill-pink)"
      let stroke := if v == 0 then "#cbd5e1" else if v == 1 then "#1d4ed8" else "#be185d"
      nodeGroup
        [ circle x y 11.0 fill stroke 1.3,
          textMid x y (if v == 0 then "·" else toString v) (if v == 0 then 11.5 else 10.5)
            (if v == 0 then "#94a3b8" else "#0f172a") "middle" "bold" ]
  let panelX := 840.0
  let panelW := 660.0
  let panel :=
    [ card panelX 150.0 panelW 268.0 16.0 "#ffffff" "#e2e8f0" 1.2,
      text (panelX + 24.0) 184.0 "The one line that makes Frobenius a homomorphism" 15.0
        "#0f172a" "start" "bold" ] ++
    lines (panelX + 24.0) 214.0 23.0 13.5 "#334155"
      [ "(x + y)³ = x³ + 3x²y + 3xy² + y³, and in characteristic 3 the two",
        "middle terms vanish, so (x + y)³ = x³ + y³.  Row 3 of Pascal's",
        "triangle is 1 3 3 1; mod 3 it reads 1 0 0 1 — the gold band.",
        "",
        "Rows 1, 3, 9 do the same here, and row 27 is the next one: every",
        "row 3ʲ has a vanishing interior, so every iterate x ↦ x^(3ʲ) is",
        "additive too.  Nothing else does: a row of the triangle collapses",
        "to 1 0 ⋯ 0 1 exactly when its index is a power of the prime." ] ++
    [ card panelX 434.0 panelW 306.0 16.0 "#ffffff" "#e2e8f0" 1.2,
      text (panelX + 24.0) 468.0 "The same triangle in other characteristics" 15.0 "#0f172a"
        "start" "bold",
      text (panelX + 24.0) 492.0
        "only the entries not divisible by p are painted — this is Kummer's carrying rule in a picture"
        11.5 "#64748b" "start" ] ++
    miniTriangle 2 32 (panelX + 118.0) 520.0 6.2 ++
    miniTriangle 5 26 (panelX + 336.0) 520.0 6.6 ++
    miniTriangle 7 22 (panelX + 548.0) 520.0 7.2 ++
    [ text (panelX + 118.0) 726.0 "p = 2: Sierpiński, 32 rows" 12.0 "#334155",
      text (panelX + 336.0) 726.0 "p = 5, 26 rows" 12.0 "#334155",
      text (panelX + 548.0) 726.0 "p = 7, 22 rows" 12.0 "#334155" ] ++
    [ card panelX 756.0 panelW 214.0 16.0 "#ffffff" "#e2e8f0" 1.2,
      text (panelX + 24.0) 790.0 "Try it yourself" 15.0 "#b45309" "start" "bold" ] ++
    lines (panelX + 24.0) 818.0 23.0 13.0 "#334155"
      [ "1. Count the coloured cells in each row: 1, 2, 3, 2, 4, 6, 3, 6, 9, 2, …",
        "    Why is that (n₀+1)(n₁+1)(n₂+1), with nᵢ the base-3 digits of n?",
        "2. Add those counts over all 27 rows and you get 216 = 6³.  Predict",
        "    the total for 81 rows before you check it.",
        "3. Which rows come out gold mod 5?  Mod 7?  Guess, then look left.",
        "4. Kummer: p ∤ C(n,i) iff adding i and n−i in base p never carries." ] ++
    [ card panelX 986.0 panelW 190.0 16.0 "#0f172a" "#1e293b" 1.2,
      text (panelX + 24.0) 1018.0 "Proved in this project" 13.5 "#f8fafc" "start" "bold" ] ++
    lines (panelX + 24.0) 1044.0 20.0 12.0 "#a5b4fc"
      [ "PascalAtlas.card_row_not_dvd — the census of a row",
        "PascalAtlas.row_interior_dvd_iff_pow — gold rows = powers of p",
        "PascalAtlas.card_triangle_not_dvd — the census of the triangle",
        "StudentViz.interior_row_prime_pow_dvd, StudentViz.freshmans_dream",
        "PascalAtlas.gold_rows_two / _three / _five / _seven" ]
  let legend :=
    [ circle 120.0 1200.0 11.0 "url(#fill-blue)" "#1d4ed8" 1.3,
      text 138.0 1205.0 "C(n,i) ≡ 1" 13.0 "#334155" "start",
      circle 260.0 1200.0 11.0 "url(#fill-pink)" "#be185d" 1.3,
      text 278.0 1205.0 "C(n,i) ≡ 2" 13.0 "#334155" "start",
      circle 400.0 1200.0 11.0 "#eef2f6" "#cbd5e1" 1.3,
      text 418.0 1205.0 "C(n,i) ≡ 0  (mod 3)" 13.0 "#334155" "start",
      text 610.0 1205.0 "the number at the right of a row is how many of its entries survive"
        12.5 "#94a3b8" "start" ]
  document w h
    (titleBlock w "Why xᵖ is a homomorphism"
        "Pascal's triangle mod 3, 27 rows: the interior of row 3, and of every row 3ʲ, vanishes"
      ++ bands ++ labels ++ cells ++ panel ++ legend ++
      footStrip w h "every entry computed in Lean — checked by PascalAtlas.rowSurvivors_eq_rowWidth_three, PascalAtlas.gold_rows_three and PascalAtlas.rowMod_27")

/-! ## Poster 2 — Frobenius orbits as clocks -/

private def palette : List (String × String) :=
  [ ("url(#fill-blue)", "#1d4ed8"), ("url(#fill-pink)", "#be185d"),
    ("url(#fill-green)", "#047857"), ("url(#fill-violet)", "#7c3aed"),
    ("url(#fill-slate)", "#334155") ]

/-- One clock face `ℤ/m` with the arrows `j ↦ p·j`. -/
private def clockPicture (p m k : Nat) (cx cy rad : Float) (caption sub : String)
    : List String :=
  let orbs := cosets p m k
  let posOf (j : Nat) : Float × Float :=
    let a := -pi / 2.0 + j.toFloat * (2.0 * pi / m.toFloat)
    (cx + rad * Float.cos a, cy + rad * Float.sin a)
  let colourOf (j : Nat) : String × String :=
    if clockStep p m j == j then ("url(#fill-gold)", "#b45309")
    else
      let idx := orbs.findIdx fun o => o.contains j
      palette.getD (idx % palette.length) ("url(#fill-slate)", "#334155")
  let arrows := (List.range m).map fun j =>
    let (x1, y1) := posOf j
    let (x2, y2) := posOf (clockStep p m j)
    if clockStep p m j == j then selfLoop x1 y1 15.0 "#b45309" "gold"
    else curve x1 y1 x2 y2 17.0 19.0 16.0 "#64748b" "slate" 1.5
  let nodes := (List.range m).flatMap fun j =>
    let (x, y) := posOf j
    let (fill, stroke) := colourOf j
    let halo := if clockStep p m j == j then [pulse x y 20.0 "#fbbf24" 2.8 (j.toFloat * 0.2)]
      else []
    halo ++ [ nodeGroup [ circle x y 15.0 fill stroke 1.6 "class=\"pop\"",
        textMid x y (toString j) 12.5 "#0f172a" "middle" "bold" ] ]
  [ circle cx cy rad "none" "#e2e8f0" 1.2,
    text cx (cy - rad - 54.0) caption 17.0 "#0f172a" "middle" "bold",
    text cx (cy - rad - 32.0) sub 12.5 "#475569" ] ++ arrows ++ nodes ++
  [ textMid cx cy ("×" ++ toString p) 22.0 "#94a3b8" ]

/-- `svg/student-2-cyclotomic-clocks.svg`: Frobenius orbits computed without ever building a
field, as multiplication by `p` on the exponent clock. -/
def clocksSvg : String :=
  let w := 1300.0
  let h := 780.0
  let c1 := clockPicture 2 7 3 250.0 340.0 150.0 "GF(8)ˣ ≅ ℤ/7" "j ↦ 2j mod 7 — orbits 1 + 3 + 3"
  let c2 := clockPicture 3 8 2 650.0 340.0 150.0 "GF(9)ˣ ≅ ℤ/8" "j ↦ 3j mod 8 — orbits 1 + 1 + 2 + 2 + 2"
  let c3 := clockPicture 2 15 4 1050.0 340.0 150.0 "GF(16)ˣ ≅ ℤ/15" "j ↦ 2j mod 15 — orbits 1 + 2 + 4 + 4 + 4"
  let panel :=
    [ card 90.0 552.0 1120.0 158.0 16.0 "#ffffff" "#e2e8f0" 1.2 ] ++
    lines 120.0 586.0 24.0 14.0 "#334155"
      [ "Pick a generator g of the cyclic group GF(pᵏ)ˣ and write every nonzero element as gʲ.  Then Frobenius x ↦ xᵖ is simply j ↦ p·j on the clock ℤ/(pᵏ−1),",
        "so its orbits are the cyclotomic cosets — you can list them with nothing but multiplication tables.  A gold point is a fixed point: p·j ≡ j, i.e. (p−1)j ≡ 0,",
        "i.e. j a multiple of (pᵏ−1)/(p−1).  There are exactly p−1 of them, and they are exactly the nonzero elements of the prime subfield 𝔽ₚ.",
        "An orbit through j has length equal to the least d with p^d·j ≡ j, and that d always divides k — which is why orbits assemble into the subfields of poster 3." ]
  document w h
    (titleBlock w "Frobenius orbits without a field" "on the exponent clock ℤ/(pᵏ−1), raising to the p-th power is just multiplying by p"
      ++ c1 ++ c2 ++ c3 ++ panel ++
      footStrip w h "orbits verified in Lean: StudentViz.cosets8_eq, cosets9_eq, cosets16_eq (each clock covered exactly once) and clock8_fixed_iff, clock9_fixed_iff, clock16_fixed_iff")

/-! ## Poster 3 — the subfield tower -/

/-- Where the divisor `d` of 12 sits in the Hasse diagram. -/
private def towerPos (d : Nat) : Float × Float :=
  if d == 12 then (520.0, 190.0)
  else if d == 4 then (350.0, 330.0)
  else if d == 6 then (690.0, 330.0)
  else if d == 2 then (350.0, 470.0)
  else if d == 3 then (690.0, 470.0)
  else (520.0, 610.0)

/-- `svg/student-3-subfield-tower.svg`: the subfields of `GF(2¹²)` are the divisors of 12. -/
def towerSvg : String :=
  let w := 1220.0
  let h := 800.0
  let edges := coverEdges.map fun (d, e) =>
    let (x1, y1) := towerPos d
    let (x2, y2) := towerPos e
    line x1 y1 x2 y2 "#94a3b8" 2.0 "" ""
  let nodes := subfieldDegrees.flatMap fun d =>
    let (x, y) := towerPos d
    let gold := d == 1
    let big := d == 12
    let fill := if gold then "url(#fill-gold)" else if big then "url(#fill-violet)"
      else "url(#fill-blue)"
    let stroke := if gold then "#b45309" else if big then "#4338ca" else "#1d4ed8"
    (if gold || big then [pulse x y 52.0 (if gold then "#fbbf24" else "#a78bfa") 3.0 0.0] else []) ++
    [ nodeGroup
        [ circle x y 44.0 fill stroke 2.0 "class=\"pop\"",
          textMid x (y - 8.0) ("GF(2" ++ (if d == 1 then "" else sup d) ++ ")") 15.0
            "#0f172a" "middle" "bold",
          textMid x (y + 13.0) (toString (2 ^ d) ++ " elts") 11.0 "#475569" ] ]
  let annotations := subfieldDegrees.map fun d =>
    let (x, y) := towerPos d
    text (x + (if d == 4 || d == 2 then -60.0 else 60.0)) (y + 4.0)
      ("Frob" ++ sup d) 12.5 "#7c3aed"
      (if d == 4 || d == 2 then "end" else "start") "bold"
  let panelX := 850.0
  let panel :=
    [ card panelX 160.0 300.0 250.0 16.0 "#ffffff" "#e2e8f0" 1.2,
      text (panelX + 22.0) 194.0 "One rule" 14.0 "#0f172a" "start" "bold" ] ++
    lines (panelX + 22.0) 224.0 23.0 13.0 "#334155"
      [ "The fixed points of the k-th iterate",
        "x ↦ x^(pᵏ) form a subfield with",
        "p^gcd(k,n) elements.  So inside",
        "GF(2¹²) the subfields are exactly",
        "GF(2^d) for d | 12 — six of them,",
        "one per divisor, drawn on the left.",
        "The Galois group is cyclic of order",
        "12, generated by Frobenius." ] ++
    [ card panelX 436.0 300.0 200.0 16.0 "#ffffff" "#e2e8f0" 1.2,
      text (panelX + 22.0) 470.0 "Try it yourself" 14.0 "#b45309" "start" "bold" ] ++
    lines (panelX + 22.0) 500.0 22.0 12.5 "#334155"
      [ "1. Draw the same tower for GF(3⁸)",
        "   and for GF(5⁶).",
        "2. Where does GF(2⁴) ∩ GF(2⁶) sit?",
        "   (Answer: gcd(4,6) = 2.)",
        "3. Which pairs of subfields are",
        "   incomparable, and why?",
        "4. How many elements of GF(2¹²)",
        "   lie in no proper subfield?" ] ++
    [ card panelX 662.0 300.0 84.0 16.0 "#0f172a" "#1e293b" 1.2,
      text (panelX + 22.0) 692.0 "Proved in this project" 13.0 "#f8fafc" "start" "bold",
      text (panelX + 22.0) 716.0 "StudentViz.tower_card" 12.0 "#a5b4fc" "start",
      text (panelX + 22.0) 734.0 "StudentViz.coverEdges_eq" 12.0 "#a5b4fc" "start" ]
  document w h
    (titleBlock w "The subfields of GF(2¹²) are the divisors of 12"
      "each floor of the tower is the fixed field of an iterate of Frobenius; the bottom floor is 𝔽₂ itself"
      ++ edges ++ nodes ++ annotations ++ panel ++
      footStrip w h "lattice computed in Lean: StudentViz.subfieldDegrees_eq and StudentViz.coverEdges_eq")

/-! ## Poster 4 — the dictionary -/

private structure Pair where
  left : String
  right : String
  thm : String

private def dictionary : List Pair :=
  [ ⟨"a finite group G", "a finite field K with pᵏ elements", ""⟩,
    ⟨"the centre Z(G)", "the prime subfield 𝔽ₚ", ""⟩,
    ⟨"conjugation x ↦ gxg⁻¹", "Frobenius x ↦ xᵖ", ""⟩,
    ⟨"Z(G) = points fixed by every conjugation",
      "𝔽ₚ = points fixed by Frobenius",
      "FrobeniusPrimeSubfield.fixedPoints_frobenius_eq_range_zmod"⟩,
    ⟨"a retraction r : G → Z(G), r|Z(G) = id",
      "a retraction N : K → 𝔽ₚ, N|𝔽ₚ = id",
      "FrobeniusPrimeSubfield.frobNorm_retraction_onto_primeSubfield"⟩,
    ⟨"the transfer (Verlagerung) V : G → Z(G)",
      "the orbit product N(x) = x·xᵖ⋯x^(p^(k−1))",
      "FrobeniusTransfer.transfer_primeUnits_eq_frobNorm"⟩,
    ⟨"the index [G : Z(G)]", "1 + p + ⋯ + p^(k−1) = (pᵏ−1)/(p−1)",
      "FrobeniusTransfer.index_primeUnits"⟩,
    ⟨"V restricted to Z(G) is z ↦ z^[G:Z(G)]",
      "N restricted to 𝔽ₚˣ is a ↦ a^k", "FrobeniusTransfer.index_primeUnits_modEq"⟩,
    ⟨"it retracts iff that power is invertible on Z(G)",
      "it retracts iff gcd(k, p−1) = 1", "FrobeniusTransfer.coprime_index_primeUnits_iff"⟩,
    ⟨"fails for Q₈, D₄, every nonabelian p-group",
      "fails for GF(9), GF(16), GF(25), GF(27), …", "not_hasCenterRetraction_of_nilpotent"⟩ ]

/-- `svg/student-4-dictionary.svg`: the two halves of the project as one dictionary. -/
def dictionarySvg : String :=
  let w := 1280.0
  let h := 860.0
  let rowH := 52.0
  let topY := 210.0
  let leftX := 70.0
  let midX := 640.0
  let colW := 540.0
  let headers :=
    [ rect leftX 150.0 colW 46.0 12.0 "#ede9fe" "#7c3aed" 1.4,
      textMid (leftX + colW / 2.0) 173.0 "GROUPS" 17.0 "#4338ca" "middle" "bold",
      rect (midX + 30.0) 150.0 colW 46.0 12.0 "#fef3c7" "#b45309" 1.4,
      textMid (midX + 30.0 + colW / 2.0) 173.0 "FINITE FIELDS" 17.0 "#b45309" "middle" "bold" ]
  let rows := (dictionary.zipIdx).flatMap fun (r, i) =>
    let y := topY + rowH * i.toFloat
    [ rect leftX y colW (rowH - 8.0) 10.0
        (if i % 2 == 0 then "#ffffff" else "#f8fafc") "#e2e8f0" 1.0,
      text (leftX + 18.0) (y + 27.0) r.left 13.5 "#0f172a" "start",
      textMid midX (y + 22.0) "↔" 20.0 "#94a3b8",
      rect (midX + 30.0) y colW (rowH - 8.0) 10.0
        (if i % 2 == 0 then "#ffffff" else "#f8fafc") "#e2e8f0" 1.0,
      text (midX + 48.0) (y + 27.0) r.right 13.5 "#0f172a" "start" ] ++
    (if r.thm == "" then []
     else [ text (midX + 48.0) (y + 42.0) r.thm 10.5 "#1d4ed8" "start" "normal" "italic" ])
  let closing :=
    [ card 70.0 (topY + rowH * 10.0 + 16.0) (w - 140.0) 82.0 16.0 "#0f172a" "#1e293b" 1.2,
      textMid (w / 2.0) (topY + rowH * 10.0 + 46.0)
        "One theorem behind the whole table: the orbit product IS the transfer of Kˣ onto 𝔽ₚˣ."
        15.0 "#f8fafc" "middle" "bold",
      textMid (w / 2.0) (topY + rowH * 10.0 + 72.0)
        "FrobeniusTransfer.transfer_primeUnits_eq_frobNorm — so the same repair criterion, gcd(index, |target|) = 1, governs both columns."
        12.5 "#a5b4fc" ]
  document w h
    (titleBlock w "Two subjects, one diagram"
      "A ↪ B → A with r ∘ ι = id: retract a group onto its centre, retract a field onto its prime subfield"
      ++ headers ++ rows ++ closing ++
      footStrip w h "every right-hand row is a theorem of this project; the left-hand rows are its group-theoretic mirror")

/-! ## Poster 5 — the orbit product spiral -/

/-- `svg/student-5-orbit-spiral.svg`: the orbit product as a spiral closing up on `𝔽₃`. -/
def spiralSvg : String :=
  let w := 1220.0
  let h := 780.0
  let cx := 420.0
  let cy := 430.0
  let k := 4
  let expOf (i : Nat) : Nat := 3 ^ i
  let posOf (i : Nat) : Float × Float :=
    let a := -pi / 2.0 + i.toFloat * (pi / 2.0)
    let r := 130.0 + i.toFloat * 42.0
    (cx + r * Float.cos a, cy + r * Float.sin a)
  let hub :=
    [ pulse cx cy 62.0 "#fbbf24" 3.0 0.0,
      circle cx cy 54.0 "url(#fill-gold)" "#b45309" 2.2 "class=\"pop\"",
      textMid cx (cy - 8.0) "𝔽₃" 22.0 "#0f172a" "middle" "bold",
      textMid cx (cy + 15.0) "{0, 1, 2}" 11.5 "#475569" ]
  let spokes := (List.range k).map fun i =>
    let (x, y) := posOf i
    curve x y cx cy 26.0 58.0 12.0 "#facc15" "gold" 1.4 "opacity=\"0.75\""
  let steps := (List.range (k - 1)).flatMap fun i =>
    let (x1, y1) := posOf i
    let (x2, y2) := posOf (i + 1)
    let d := curveD x1 y1 x2 y2 26.0 28.0 26.0
    [ path d "#1d4ed8" 2.0 "blue", comet d "#60a5fa" 4.0 2.2 (i.toFloat * 0.5) 200.0,
      textMid ((x1 + x2) / 2.0 + 24.0) ((y1 + y2) / 2.0 - 24.0) "(·)³" 14.0 "#1d4ed8" "middle"
        "bold" ]
  let nodes := (List.range k).flatMap fun i =>
    let (x, y) := posOf i
    [ nodeGroup
        [ circle x y 25.0 "url(#fill-blue)" "#1d4ed8" 2.0 "class=\"pop\"",
          textMid x y ("x" ++ (if i == 0 then "" else sup (expOf i))) 15.0 "#0f172a"
            "middle" "bold" ] ]
  let closing :=
    let (x0, y0) := posOf 0
    let (x3, y3) := posOf 3
    [ curve x3 y3 x0 y0 30.0 30.0 (-130.0) "#7c3aed" "violet" 2.0 "stroke-dasharray=\"8 6\"",
      textMid cx (cy - 250.0) "x⁸¹ = x: the spiral closes after k = 4 steps" 13.5
        "#7c3aed" "middle" "bold" ]
  let panelX := 790.0
  let panel :=
    [ card panelX 150.0 370.0 214.0 16.0 "#ffffff" "#e2e8f0" 1.2,
      text (panelX + 22.0) 184.0 "The orbit product" 14.0 "#0f172a" "start" "bold" ] ++
    lines (panelX + 22.0) 214.0 23.0 13.0 "#334155"
      [ "N(x) = x · xᵖ · x^(p²) ⋯ x^(p^(k−1))",
        "     = x^(1 + p + ⋯ + p^(k−1)).",
        "",
        "Multiply the exponent by p − 1:",
        "(p−1)(1 + p + ⋯ + p^(k−1)) = pᵏ − 1,",
        "and x^(pᵏ−1) = 1 for x ≠ 0.  So",
        "N(x)^(p−1) = 1: N(x) lies in 𝔽ₚ." ] ++
    [ card panelX 390.0 370.0 190.0 16.0 "#ffffff" "#e2e8f0" 1.2,
      text (panelX + 22.0) 422.0 "The exponent, field by field" 14.0 "#0f172a" "start" "bold" ] ++
    ((["GF(8):  1+2+4 = 7", "GF(9):  1+3 = 4", "GF(16): 1+2+4+8 = 15",
       "GF(27): 1+3+9 = 13", "GF(81): 1+3+9+27 = 40"]).zipIdx).map (fun (s, i) =>
      text (panelX + 22.0) (452.0 + 24.0 * i.toFloat) s 13.0 "#334155" "start") ++
    [ card panelX 606.0 370.0 122.0 16.0 "#0f172a" "#1e293b" 1.2,
      text (panelX + 22.0) 638.0 "Try it yourself" 13.0 "#fbbf24" "start" "bold" ] ++
    lines (panelX + 22.0) 662.0 20.0 12.0 "#e2e8f0"
      [ "1. Compute N on GF(9): is it the identity on 𝔽₃?",
        "2. It is not — N(2) = 2⁴ = 1.  Find the fix.",
        "3. Show N is the identity on 𝔽ₚ iff p−1 | k−1." ]
  document w h
    (titleBlock w "Why the orbit product lands in the prime subfield"
      "GF(81): four conjugates x, x³, x⁹, x²⁷ multiply to x⁴⁰ ∈ 𝔽₃, and then the spiral closes"
      ++ hub ++ spokes ++ steps ++ nodes ++ closing ++ panel ++
      footStrip w h "exponents computed in Lean: StudentViz.normExp_samples, and StudentViz.normExp_mul_pred is the identity in the panel")

/-! ## Poster 6 — the exercise ladder -/

private structure Rung where
  stars : Nat
  task : String
  hint : String
  thm : String

private def ladder : List Rung :=
  [ ⟨1, "Check that x⁵ = x for every x in 𝔽₅ by hand.",
      "five multiplications; this is Fermat's little theorem", "ZMod.pow_card"⟩,
    ⟨1, "Colour Pascal's triangle mod 2 and mod 3.",
      "the empty rows are the rows pʲ", "StudentViz.interior_row_prime_pow_dvd"⟩,
    ⟨1, "List the Frobenius orbits of GF(16) using only ℤ/15.",
      "double the exponent: 1 → 2 → 4 → 8 → 1", "StudentViz.cosets16_eq"⟩,
    ⟨2, "Prove the fixed points of x ↦ xᵖ are exactly 𝔽ₚ.",
      "Xᵖ − X has at most p roots, and 𝔽ₚ supplies p of them",
      "FrobeniusPrimeSubfield.fixedPoints_frobenius_eq_range_zmod"⟩,
    ⟨2, "Show every Frobenius orbit has length dividing k.",
      "the orbit length is the degree of the element over 𝔽ₚ",
      "FrobeniusPrimeSubfield.card_fixedSubfield"⟩,
    ⟨2, "Compute N(x) = x·x³·x⁹ on all 27 elements of GF(27).",
      "you should get 0 once and 1, 2 thirteen times each", "GF27Viz.normFibre_card"⟩,
    ⟨2, "Find the smallest field where N is NOT a retraction.",
      "GF(9): N(2) = 2⁴ = 1, so 2 is sent to 1", "GF9.error_point"⟩,
    ⟨3, "Prove: N retracts GF(pᵏ) onto 𝔽ₚ iff p−1 divides k−1.",
      "on 𝔽ₚˣ the orbit product is a ↦ aᵏ",
      "FrobeniusPrimeSubfield.frobNorm_retraction_onto_primeSubfield"⟩,
    ⟨3, "Prove the dihedral group Dₙ retracts onto its centre iff 4 ∤ n.",
      "when 4 | n the central half-turn is a commutator",
      "DihedralGroup.hasCenterRetraction_dihedral_iff"⟩,
    ⟨3, "Prove the orbit product is the transfer of Kˣ onto 𝔽ₚˣ.",
      "the index of 𝔽ₚˣ in Kˣ is 1 + p + ⋯ + p^(k−1)",
      "FrobeniusTransfer.transfer_primeUnits_eq_frobNorm"⟩ ]

private def starString (n : Nat) : String :=
  match n with
  | 1 => "★"
  | 2 => "★★"
  | _ => "★★★"

/-- `svg/student-6-exercise-ladder.svg`: ten exercises, easiest first. -/
def ladderSvg : String :=
  let w := 1240.0
  let h := 920.0
  let rowH := 62.0
  let topY := 150.0
  let railX := 120.0
  let rail :=
    [ line railX (topY + 20.0) railX (topY + rowH * 9.0 + 20.0) "#cbd5e1" 6.0 "" "" ]
  let rows := (ladder.zipIdx).flatMap fun (r, i) =>
    let y := topY + rowH * i.toFloat
    let col := if r.stars == 1 then "#047857" else if r.stars == 2 then "#1d4ed8" else "#be185d"
    let fill := if r.stars == 1 then "url(#fill-green)" else if r.stars == 2 then
      "url(#fill-blue)" else "url(#fill-pink)"
    [ card 160.0 (y - 8.0) (w - 240.0) (rowH - 10.0) 12.0 "#ffffff" "#e2e8f0" 1.0,
      nodeGroup
        [ circle railX (y + 20.0) 19.0 fill col 2.0 "class=\"pop\"",
          textMid railX (y + 20.0) (toString (i + 1)) 13.0 "#0f172a" "middle" "bold" ],
      text 182.0 (y + 16.0) (starString r.stars) 14.0 col "start" "bold",
      text 232.0 (y + 16.0) r.task 14.0 "#0f172a" "start" "bold",
      text 232.0 (y + 36.0) ("hint: " ++ r.hint) 12.0 "#64748b" "start",
      text (w - 96.0) (y + 36.0) r.thm 11.0 "#1d4ed8" "end" "normal" "italic" ]
  let closing :=
    [ card 160.0 (topY + rowH * 10.0 + 6.0) (w - 240.0) 86.0 16.0 "#0f172a" "#1e293b" 1.2,
      textMid (w / 2.0) (topY + rowH * 10.0 + 38.0)
        "Every rung above has a machine-checked answer in this project — but the fun is in getting there first."
        14.5 "#f8fafc" "middle" "bold",
      textMid (w / 2.0) (topY + rowH * 10.0 + 66.0)
        "★ = pen and paper · ★★ = one good idea · ★★★ = a small theory"
        12.5 "#a5b4fc" ]
  document w h
    (titleBlock w "Ten things to try" "a ladder through the whole story, from a five-line computation to the transfer homomorphism"
      ++ rail ++ rows ++ closing ++
      footStrip w h "italic names on the right are the theorems in this project that settle each exercise")

end StudentViz
