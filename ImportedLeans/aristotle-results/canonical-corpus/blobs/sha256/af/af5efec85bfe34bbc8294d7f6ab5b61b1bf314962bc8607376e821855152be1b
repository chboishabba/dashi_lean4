import RequestProject.PascalExpanded
import RequestProject.StudentGallery

/-!
# The atlas sheet: the expanded triangle as the index of the gallery

The drawing layer for `RequestProject/PascalExpanded.lean`.  It writes one file:

| picture | function |
| --- | --- |
| `svg/student-0-atlas.svg` | `PascalAtlas.atlasSvg` |

27 rows of Pascal's triangle mod `3`, one per picture of the gallery: row `n` is a link to
`PascalAtlas.atlas[n]`, and the three base-`3` digits of `n` are printed beside it as the element
`c₀ + c₁t + c₂t²` of `GF(27)`.  Everything drawn — the entries of the triangle, which rows come
out gold, how many cells of each row survive mod `3` — is computed in Lean and checked there
(`PascalAtlas.gold_rows_three`, `PascalAtlas.rowSurvivors_eq_rowWidth_three`,
`PascalAtlas.card_row_not_dvd`, `PascalAtlas.card_triangle_not_dvd`).
-/

namespace PascalAtlas

open SvgCore

/-- Row `n` written as an element of `GF(27) = 𝔽₃[t]/(t³ − t − 1)`, from its base-3 digits. -/
def gfLabel (n : Nat) : String :=
  let (c0, c1, c2) := rowLabel n
  let terms : List String :=
    (if c0 == 0 then [] else [toString c0]) ++
    (if c1 == 0 then [] else [if c1 == 1 then "t" else toString c1 ++ "t"]) ++
    (if c2 == 0 then [] else [if c2 == 1 then "t²" else toString c2 ++ "t²"])
  if terms.isEmpty then "0" else String.intercalate " + " terms

/-- The colours of a cell holding the residue `v` mod 3. -/
private def cellColours (v : Nat) : String × String × String :=
  if v == 0 then ("#eef2f6", "#cbd5e1", "#94a3b8")
  else if v == 1 then ("url(#fill-blue)", "#1d4ed8", "#0f172a")
  else ("url(#fill-pink)", "#be185d", "#0f172a")

/-- `svg/student-0-atlas.svg`: the expanded Pascal triangle mod 3, used as the index of the
gallery — one row per picture, each row a link. -/
def atlasSvg : String :=
  let w := 1980.0
  let h := 1300.0
  let dx := 25.0
  let dy := 37.0
  let top := 208.0
  let cx0 := 470.0
  let survX := 840.0
  let labX := 915.0
  let titleX := 1015.0
  let blurbX := 1320.0
  let cellX (n i : Nat) : Float := cx0 - n.toFloat * dx / 2.0 + i.toFloat * dx
  let cellY (n : Nat) : Float := top + n.toFloat * dy
  let isGold (n : Nat) : Bool := goldRows 3 27 |>.contains n
  let rowBlock (n : Nat) : String :=
    let y := cellY n
    let e := atlas.getD n ⟨"index.html", "—", "—"⟩
    let hit :=
      rect 54.0 (y - 17.0) (w - 108.0) 34.0 9.0 "#38bdf8" "none" 0.0 "" "opacity=\"0.02\""
    let band :=
      if isGold n then
        [ rect (cellX n 0 - 21.0) (y - 16.5) (n.toFloat * dx + 42.0) 33.0 16.5 "#fef3c7"
            "#f59e0b" 1.3 ]
      else []
    let cells := (List.range (n + 1)).map fun i =>
      let v := Nat.choose n i % 3
      let (fill, stroke, ink) := cellColours v
      let x := cellX n i
      group "class=\"node\""
        [ circle x y 10.5 fill stroke 1.2,
          textMid x y (if v == 0 then "·" else toString v) (if v == 0 then 11.0 else 10.5) ink
            "middle" "bold" ]
    let rowTag :=
      [ text 60.0 (y + 4.5) ("n = " ++ toString n) 12.0
          (if isGold n then "#b45309" else "#94a3b8") "start" ]
    let connector :=
      line (cellX n n + 18.0) y (survX - 14.0) y "#e2e8f0" 1.0 "" "3 6"
    let labels :=
      [ text survX (y + 4.5) (toString (rowSurvivors 3 n) ++ " left") 11.0 "#94a3b8" "start",
        text labX (y + 4.5) (gfLabel n) 12.5 "#7c3aed" "start" "bold",
        text titleX (y + 4.5) e.title 13.5 "#0f172a" "start" "bold",
        text blurbX (y + 4.5) e.blurb 11.0 "#64748b" "start" ]
    link e.file ([hit] ++ band ++ cells ++ rowTag ++ [connector] ++ labels)
  let header :=
    [ text (w / 2.0) 54.0 "The atlas: 27 rows, 27 pictures" 30.0 "url(#ink)" "middle" "bold",
      text (w / 2.0) 86.0
        "Pascal's triangle mod 3, expanded to 27 = 3³ rows — and used as the index of this gallery: every row is a link"
        15.0 "#475569",
      text (w / 2.0) 112.0
        "Row n carries picture n, and the three base-3 digits of n name the element c₀ + c₁t + c₂t² of GF(27) = 𝔽₃[t]/(t³ − t − 1), the field the whole project turns on"
        13.0 "#64748b",
      text 60.0 168.0 "row" 12.0 "#94a3b8" "start" "bold",
      text survX 168.0 "cells ≢ 0" 12.0 "#94a3b8" "start" "bold",
      text labX 168.0 "GF(27)" 12.0 "#94a3b8" "start" "bold",
      text titleX 168.0 "picture (click the row)" 12.0 "#94a3b8" "start" "bold",
      line 54.0 180.0 (w - 54.0) 180.0 "#e2e8f0" 1.0 ]
  let legend :=
    [ circle 470.0 (h - 82.0) 10.5 "url(#fill-blue)" "#1d4ed8" 1.2,
      text 488.0 (h - 77.0) "C(n,i) ≡ 1" 12.5 "#334155" "start",
      circle 600.0 (h - 82.0) 10.5 "url(#fill-pink)" "#be185d" 1.2,
      text 618.0 (h - 77.0) "≡ 2" 12.5 "#334155" "start",
      circle 680.0 (h - 82.0) 10.5 "#eef2f6" "#cbd5e1" 1.2,
      text 698.0 (h - 77.0) "≡ 0 (mod 3)" 12.5 "#334155" "start",
      rect 830.0 (h - 94.0) 40.0 24.0 12.0 "#fef3c7" "#f59e0b" 1.3,
      text 880.0 (h - 77.0)
        "gold: the interior of the row vanishes — rows 1, 3, 9, exactly the powers of 3 (PascalAtlas.row_interior_dvd_iff_pow)"
        12.5 "#334155" "start" ]
  document w h
    (header ++ (List.range 27).map rowBlock ++ legend ++
      [ rect 0.0 (h - 40.0) w 40.0 0.0 "#0f172a" "none" 0.0,
        text (w / 2.0) (h - 15.0)
          "216 of the 378 cells drawn here survive mod 3 = 6³, the census PascalAtlas.card_triangle_not_dvd proves for every prime and every height"
          12.5 "#94a3b8" ])

end PascalAtlas
