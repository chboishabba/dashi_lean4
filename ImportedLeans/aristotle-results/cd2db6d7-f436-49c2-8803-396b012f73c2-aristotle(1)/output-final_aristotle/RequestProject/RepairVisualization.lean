import RequestProject.GF9Repair
import RequestProject.SvgCore

/-!
# Picture of the smallest error and of its repair

This file draws `svg/gf9-error-repair.svg`, the picture accompanying
`RequestProject/GF9Repair.lean`: the smallest field size whose Frobenius orbit product is
*not* a retraction, `q = 9`, side by side with the repaired map.

* Left panel — **the error.**  The multiplicative orbit product `N(x) = x · x³ = x⁴` of
  `GF(9) = 𝔽₃[t]/(t² − t − 1)`, drawn as a map onto the prime subfield `𝔽₃ = {0, 1, 2}`.
  Two of the three arrows starting inside `𝔽₃` are gold self-returns `N(a) = a`, but the
  third is crimson: `N(2) = 1 ≠ 2`.  That single crossing arrow *is* the error
  `frobDefect 3 2 = 1` (`GF9.error_card`, `GF9.error_point`).
* Right panel — **the repair.**  The normalized additive orbit sum
  `R(x) = 2⁻¹ · (x + x³) = 2 · (x + x³)` on the same nine elements.  Every arrow starting
  inside `𝔽₃` returns to its own node: the error is `0` and `R` is a genuine retraction
  (`GF9.repair_isRetraction`).
* The band between the panels records what the repair cost: no multiplicative map into `𝔽₃`
  can fix `2`, because `2 = (1+t)²` is a square in `GF(9)` but not in `𝔽₃`
  (`GF9.no_multiplicative_repair`), so the repaired map is necessarily only additive
  (`GF9.repair_not_multiplicative`).

Everything drawn is Lean data checked against those theorems by `decide`:
`RepairViz.enum9_complete`, `RepairViz.enum9_nodup`, `RepairViz.normArrows_correct`,
`RepairViz.repairArrows_correct`, `RepairViz.normArrows_bad`, `RepairViz.repairArrows_good`.
-/

namespace RepairViz

open SvgCore

/-! ## The data -/

/-- The nine elements of `GF(9)`, in drawing order: the prime subfield `𝔽₃` first. -/
def enum9 : List GF9 :=
  [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩]

theorem enum9_complete : ∀ x : GF9, x ∈ enum9 := by decide

theorem enum9_nodup : enum9.Nodup := by decide

/-- The arrows of the left panel: `x ↦ N(x) = x⁴`. -/
def normArrows : List (GF9 × GF9) := enum9.map fun x => (x, x ^ 4)

/-- The arrows of the right panel: `x ↦ R(x) = 2·(x + x³)`. -/
def repairArrows : List (GF9 × GF9) := enum9.map fun x => (x, GF9.repair x)

theorem normArrows_correct : ∀ q ∈ normArrows, q.2 = GF9.norm4 q.1 := by decide

theorem repairArrows_correct : ∀ q ∈ repairArrows, q.2 = GF9.repair q.1 := by decide

/-- Both maps land in the prime subfield, so every arrow ends on one of the three target
nodes. -/
theorem arrows_land_in_primeSubfield :
    (∀ q ∈ normArrows, q.2.c1 = 0) ∧ (∀ q ∈ repairArrows, q.2.c1 = 0) := by
  refine ⟨by decide, by decide⟩

/-- **The crimson arrow of the left panel**: the only arrow that starts in `𝔽₃` and does not
return to its own node is `2 ↦ 1`. -/
theorem normArrows_bad :
    normArrows.filter (fun q => q.1.c1 == 0 && q.2 != q.1) = [(⟨2, 0⟩, 1)] := by decide

/-- **The right panel has no crimson arrow**: the repaired map fixes `𝔽₃` pointwise. -/
theorem repairArrows_good :
    repairArrows.filter (fun q => q.1.c1 == 0 && q.2 != q.1) = [] := by decide

/-! ## The drawing -/

/-- `x = c₀ + c₁t` written as a polynomial in `t`. -/
def label (x : GF9) : String :=
  let mono (c : ℕ) (s : String) : List String :=
    if c == 0 then [] else if s == "" then [toString c]
    else if c == 1 then [s] else [toString c ++ s]
  let parts := mono x.c1.val "t" ++ mono x.c0.val ""
  if parts.isEmpty then "0" else String.intercalate " + " parts

/-- Position of an element of `𝔽₃ = {0,1,2}` among the three target nodes. -/
def tgtIdx (x : GF9) : Nat := x.c0.val

private def nodeR : Float := 21.0

private def srcY (i : Nat) : Float := 200.0 + i.toFloat * 47.0
private def tgtY (j : Nat) : Float := 248.0 + j.toFloat * 136.0

private def inPrime (x : GF9) : Bool := x.c1 == 0

/-- One panel: the nine elements on the left, the prime subfield on the right, and one arrow
per element.  `f` is the map drawn, `ox` the horizontal offset of the panel. -/
private def panel (ox : Float) (headline sub formula : String) (f : GF9 → GF9)
    (errCount : Nat) : List String :=
  let srcX := ox + 150.0
  let tgtX := ox + 400.0
  let accent := if errCount == 0 then "#047857" else "#be185d"
  let frame :=
    [ card (ox + 30.0) 120.0 500.0 560.0 22.0 "#ffffff" "#e2e8f0" 1.4,
      text (ox + 280.0) 86.0 headline 21.0 "url(#ink)" "middle" "bold",
      text (ox + 280.0) 108.0 sub 13.0 "#475569",
      text (ox + 280.0) 152.0 formula 15.0 accent "middle" "bold",
      text srcX 166.0 "GF(9)" 12.0 "#64748b",
      text tgtX 166.0 "𝔽₃" 12.0 "#64748b" ]
  let drawArrow (x : GF9) (i : Nat) : List String :=
    let y1 := srcY i
    let y2 := tgtY (tgtIdx (f x))
    let fixedHere := inPrime x && f x == x
    let badHere := inPrime x && f x != x
    let col := if fixedHere then "#b45309" else if badHere then "#be185d" else "#94a3b8"
    let mark := if fixedHere then "gold" else if badHere then "pink" else "slate"
    let width := if inPrime x then 2.4 else 1.2
    let bulge := if badHere then 26.0 else 10.0
    let d := curveD srcX y1 tgtX y2 (nodeR + 4.0) (nodeR + 8.0) bulge
    [path d col width mark] ++
      (if badHere then [comet d "#be185d" 4.0 1.8 0.0 120.0] else [])
  -- the arrows starting outside 𝔽₃ are drawn first, so the three that carry the
  -- retraction property lie on top
  let arrows :=
    ((enum9.zipIdx).filter (fun p => !inPrime p.1)).flatMap (fun (x, i) => drawArrow x i) ++
    ((enum9.zipIdx).filter (fun p => inPrime p.1)).flatMap (fun (x, i) => drawArrow x i)
  let srcNodes := (enum9.zipIdx).flatMap fun (x, i) =>
    let y := srcY i
    let fill := if inPrime x then "url(#fill-gold)" else "url(#fill-slate)"
    let stroke := if inPrime x then "#b45309" else "#334155"
    (if inPrime x && f x != x then [pulse srcX y (nodeR + 9.0) "#fb7185" 2.2 0.0] else []) ++
    [ nodeGroup
        [ circle srcX y nodeR fill stroke 1.8 "class=\"pop\"",
          textMid srcX y (label x) 10.0 "#0f172a" "middle" "bold" ] ]
  let tgtNodes := (List.range 3).flatMap fun j =>
    let y := tgtY j
    [ nodeGroup
        [ circle tgtX y (nodeR + 3.0) "url(#fill-gold)" "#b45309" 2.0 "class=\"pop\"",
          textMid tgtX y (toString j) 13.0 "#0f172a" "middle" "bold" ] ]
  let badge :=
    let msg := if errCount == 0 then "error 0 — a genuine retraction onto 𝔽₃"
               else "error " ++ toString errCount ++ " — one point of 𝔽₃ is moved"
    [ chip (ox + 280.0) 646.0 400.0 34.0 msg
        (if errCount == 0 then "#ecfdf5" else "#fff1f2") accent accent 13.0 ]
  frame ++ arrows ++ srcNodes ++ tgtNodes ++ badge

/-- The picture `svg/gf9-error-repair.svg`. -/
def repairSvg : String :=
  let w := 1160.0
  let h := 840.0
  let title :=
    [ text (w / 2.0) 44.0 "The smallest error, and its repair:  GF(9) = 𝔽₃[t]/(t² − t − 1)"
        26.0 "url(#ink)" "middle" "bold" ]
  let left := panel 20.0 "The error" "the multiplicative orbit product, on the nine elements"
      "N(x) = x · x³ = x⁴" GF9.norm4 1
  let right := panel 600.0 "The repair" "the normalized additive orbit sum, on the same nine"
      "R(x) = 2⁻¹·(x + x³) = 2·(x + x³)" GF9.repair 0
  let bridge :=
    [ card 90.0 706.0 980.0 104.0 20.0 "#f8fafc" "#cbd5e1" 1.4,
      text (w / 2.0) 736.0
        "2 = (1 + t)² is a square in GF(9) but not in 𝔽₃, so no multiplicative map GF(9) → 𝔽₃ can fix it"
        14.0 "#334155",
      text (w / 2.0) 760.0
        "— the crimson arrow cannot be straightened by any choice of exponent (GF9.no_multiplicative_repair)."
        14.0 "#334155",
      text (w / 2.0) 788.0
        "Dividing the additive orbit sum by k = 2 does straighten it; the price is multiplicativity (GF9.repair_not_multiplicative)."
        14.0 "#334155" ]
  let legend :=
    [ line 120.0 682.0 156.0 682.0 "#b45309" 2.2 "gold",
      text 164.0 686.0 "a ↦ a on 𝔽₃ (the retraction property)" 12.5 "#475569" "start",
      line 560.0 682.0 596.0 682.0 "#be185d" 2.2 "pink",
      text 604.0 686.0 "a ↦ N(a) ≠ a — the error" 12.5 "#475569" "start",
      line 900.0 682.0 936.0 682.0 "#94a3b8" 1.2 "slate",
      text 944.0 686.0 "outside 𝔽₃" 12.5 "#475569" "start" ]
  document w h (title ++ left ++ right ++ legend ++ bridge)

end RepairViz
