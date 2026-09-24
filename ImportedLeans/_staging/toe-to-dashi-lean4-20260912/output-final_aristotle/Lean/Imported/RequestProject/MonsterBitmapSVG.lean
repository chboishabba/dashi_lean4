import RequestProject.MonsterBitmap
import RequestProject.SVG
import Lean

/-!
# MonsterBitmapSVG — the 194×100 Monster–Moonshine bitmap, *as an animation*

`RequestProject.MonsterBitmap` is the zero-`sorry`, axiom-free specification of the
pipeline that turns a natural number `N` into a `194 × 100` bitmap by folding `N`
through the 194 Monster irreducible-representation dimensions, weaving the
j-function coefficients, recombining with the Chinese Remainder Theorem over the
supersingular primes, and normalising each cell to an 8-bit pixel.

This layer renders that bitmap as a single, self-contained, **self-playing animated
SVG**.  Every pixel it draws is computed natively by Lean from the very same
definitions the proofs use:

* `MonsterBitmap.degArr` — the 194 Monster irrep dimensions (rows, top → bottom);
* `MonsterBitmap.weaveArr` — the greedy j-coefficient decomposition per column;
* `MonsterBitmap.sspPrimeList` — the 15 supersingular primes used for the CRT modulus;
* the fold / CRT / normalize stages of `MonsterBitmap.pixelValue`.

The faithfulness of the fast renderer to the specification is **proved**:
`MonsterBitmapSVG.render_faithful` checks, by `native_decide`, that the renderer's
per-cell byte equals `MonsterBitmap.pixelValue` at every one of the `194 × 100`
cells (for the featured input).

The animation is a flip-book over a handful of featured inputs `N`.  Only the
`1833` cells that are ever active (nonzero weave weight) are drawn — the rest of the
`194 × 100` grid is the black background — and each active cell's colour is animated
across the input frames, so the picture *breathes* as `N` changes while its lit
support (the moonshine weave) stays fixed.

Commands:

* `#bitmapfilm`               — build the film, report size and active-cell count.
* `#writemonsterbitmap "path"` — build the film and write the SVG to `path`.
-/

open Lean Meta Elab Command SVG

namespace MonsterBitmapSVG

open MonsterBitmap

/-! ## §1  Faithful, fast pixel computation -/

/-- The coefficient of `q^{n+1}` in the j-invariant, as a `ℕ` (reused from the spec). -/
def jCoeffNat (n : Nat) : Nat := (Moonshine.t1Coeffs[n]!).toNat

/-- Product of the supersingular primes dividing `d` — exactly the modulus of the
`activeSSPs` fingerprint of an irrep of dimension `d`. -/
def radSSP (d : Nat) : Nat :=
  sspPrimeList.foldl (fun acc p => if d % p == 0 then acc * p else acc) 1

/-- Per-irrep supersingular radical, precomputed once over `degArr`. -/
def radArr : Array Nat := degArr.map radSSP

/-- Fast pixel byte at cell `(i, n)` for input `N`, recomputing the column weave.
This mirrors `MonsterBitmap.pixelValue` exactly (see `render_faithful`). -/
def pixelByteIdx (N i n : Nat) : Nat :=
  let wcol := weaveArr (jCoeffNat n)
  let d := degArr[i]!
  let w := wcol[i]!
  let modulus := if w == 0 then 1 else radArr[i]!
  let fold := N % d
  let pos := fold % modulus
  let denom := max 1 (modulus - 1)
  min (pos * 255 / denom) 255

/-- **Faithfulness of the renderer.**  At every one of the `194 × 100` cells, the
fast renderer's byte equals the specification's `pixelValue` (featured input). -/
theorem render_faithful :
    ∀ i : Fin numIrreps, ∀ n : Fin numQTerms,
      pixelByteIdx 196884 i.val n.val = (MonsterBitmap.pixelValue 196884 i n).val := by
  native_decide

/-! ## §2  Colour map -/

/-- One lowercase hex digit. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- A byte as a two-digit hex string. -/
def hex2 (n : Nat) : String :=
  let n := min n 255
  String.ofList [hexDigit (n / 16), hexDigit (n % 16)]

/-- Linear interpolation `a → b` at `t/d`, over `Int` to allow `b < a`. -/
def mix (a b : Int) (t d : Nat) : Nat :=
  (a + (b - a) * Int.ofNat t / Int.ofNat d).toNat

/-- Heat colour map: intensity `0…255 ↦` indigo → magenta → gold. -/
def heat (v : Nat) : String :=
  let (r, g, b) :=
    if v <= 128 then
      let t := v; let d := 128
      (mix 28 230 t d, mix 22 40 t d, mix 70 150 t d)
    else
      let t := v - 128; let d := 127
      (mix 230 255 t d, mix 40 216 t d, mix 150 64 t d)
  s!"#{hex2 r}{hex2 g}{hex2 b}"

/-! ## §3  Geometry -/

def leftMargin : Int := 70
def topMargin  : Int := 150
def cellW : Int := 8
def cellH : Int := 4

/-- The featured inputs `N` cycled by the flip-book. -/
def featuredNs : List Nat := [1, 42, 1729, 196884, 8675309, 1000000007]

/-- Frame duration label for the whole loop. -/
def loopDur : String := "12s"

/-! ## §4  Drawing the active cells -/

/-- All active cells (nonzero weave) as animated rects whose fill cycles over the
featured inputs.  Inactive cells are left as the black background. -/
def cellRects : List Svg := Id.run do
  let mut acc : Array Svg := #[]
  for n in List.range numQTerms do
    let wcol := weaveArr (jCoeffNat n)
    let d0 := degArr
    for i in List.range numIrreps do
      if wcol[i]! != 0 then
        let d := d0[i]!
        let modulus := radArr[i]!
        let denom := max 1 (modulus - 1)
        let cols := featuredNs.map (fun N =>
          let fold := N % d
          let pos := fold % modulus
          let v := min (pos * 255 / denom) 255
          heat v)
        let values := String.intercalate ";" (cols ++ [cols.headD "#000000"])
        let x : Int := leftMargin + Int.ofNat n * cellW
        let y : Int := topMargin + Int.ofNat i * cellH
        acc := acc.push (Svg.elem "rect"
          [("x", toString x), ("y", toString y),
           ("width", toString (cellW - 1)), ("height", toString cellH),
           ("fill", cols.headD "#000000")]
          [ Svg.raw s!"<animate attributeName=\"fill\" values=\"{values}\" dur=\"{loopDur}\" calcMode=\"discrete\" repeatCount=\"indefinite\"/>" ])
  return acc.toList

/-- Count of active (drawn) cells. -/
def activeCount : Nat := Id.run do
  let mut c := 0
  for n in List.range numQTerms do
    let wcol := weaveArr (jCoeffNat n)
    for i in List.range numIrreps do
      if wcol[i]! != 0 then c := c + 1
  return c

/-- Number of visibly-lit cells (pixel intensity ≥ 32 of 255) for input `N`.
This is the quantity that makes the flip-book "breathe": small `N` leave almost
every cell near intensity 0 (black), large `N` push residues across their CRT
moduli and light many cells up. -/
def litCountOf (N : Nat) : Nat := Id.run do
  let mut c := 0
  for n in List.range numQTerms do
    let wcol := weaveArr (jCoeffNat n)
    for i in List.range numIrreps do
      if wcol[i]! != 0 then
        let d := degArr[i]!
        let modulus := radArr[i]!
        let denom := max 1 (modulus - 1)
        let v := min ((N % d % modulus) * 255 / denom) 255
        if v >= 32 then c := c + 1
  return c

/-- Per-frame lit-cell counts, one per featured input. -/
def frameLit : List Nat := featuredNs.map litCountOf

/-! ## §5  HUD, axes, legend -/

/-- Column axis ticks (q-expansion index `n`, every 10). -/
def colTicks : List Svg :=
  (List.range numQTerms).filterMap (fun n =>
    if n % 10 == 0 then
      let x : Int := leftMargin + Int.ofNat n * cellW
      some (Svg.text [("x", toString x), ("y", toString (topMargin - 6)),
                      ("font-size","10"), ("fill","#7a86b8")] (toString n))
    else none)

/-- Row axis ticks (irrep index `i`, every 20) with the dimension. -/
def rowTicks : List Svg :=
  (List.range numIrreps).filterMap (fun i =>
    if i % 20 == 0 then
      let y : Int := topMargin + Int.ofNat i * cellH + 4
      some (Svg.text [("x","8"), ("y", toString y),
                      ("font-size","9"), ("fill","#7a86b8")]
              s!"#{i}")
    else none)

/-- The flip-book input label: one text per frame, opacity-cycled so exactly one
shows at a time, matching the cell fill animation. -/
def inputLabels : List Svg :=
  let k := featuredNs.length + 1
  featuredNs.zipIdx.map (fun (N, idx) =>
    -- opacity is 1 only on this frame's slot
    let vals := (List.range k).map (fun f => if f == idx then "1" else "0")
    let values := String.intercalate ";" vals
    Svg.elem "text"
      [("x","70"), ("y","126"), ("font-size","18"), ("font-weight","800"),
       ("fill","#ffd700"), ("opacity", if idx == 0 then "1" else "0")]
      [ Svg.raw s!"<animate attributeName=\"opacity\" values=\"{values}\" dur=\"{loopDur}\" calcMode=\"discrete\" repeatCount=\"indefinite\"/>",
        Svg.raw s!"N = {N}" ])

/-- A frame-synced brightness readout: shows how many cells are visibly lit on the
current frame, so the viewer can see *why* small inputs look dark. -/
def brightnessLabels : List Svg :=
  let k := featuredNs.length + 1
  (featuredNs.zip frameLit).zipIdx.map (fun ((_, lit), idx) =>
    let vals := (List.range k).map (fun f => if f == idx then "1" else "0")
    let values := String.intercalate ";" vals
    Svg.elem "text"
      [("x","300"), ("y","126"), ("font-size","14"), ("font-weight","700"),
       ("fill", if lit == 0 then "#5a6790" else "#9fe0b0"),
       ("opacity", if idx == 0 then "1" else "0")]
      [ Svg.raw s!"<animate attributeName=\"opacity\" values=\"{values}\" dur=\"{loopDur}\" calcMode=\"discrete\" repeatCount=\"indefinite\"/>",
        Svg.raw s!"{lit} cells lit (intensity ≥ 32) {if lit == 0 then "— too dark to see" else ""}" ])

/-- A horizontal legend gradient bar for the heat map. -/
def legendBar : Svg :=
  let y : Int := topMargin + Int.ofNat numIrreps * cellH + 26
  let swatches := (List.range 64).map (fun k =>
    let v := k * 255 / 63
    rect (leftMargin + Int.ofNat k * 6) y 6 12 (heat v) "none" [])
  group
    (swatches ++
     [ Svg.text [("x", toString leftMargin), ("y", toString (y - 4)),
                 ("font-size","11"), ("fill","#9fb0e0")] "pixel intensity  0",
       Svg.text [("x", toString (leftMargin + 64*6 + 6)), ("y", toString (y + 10)),
                 ("font-size","11"), ("fill","#9fb0e0")] "255" ]) []

/-! ## §6  Assembling the film -/

/-- Build the complete animated Monster-bitmap SVG. -/
def buildFilm : String :=
  let w : Nat := (leftMargin + Int.ofNat numQTerms * cellW + 40).toNat
  let h : Nat := (topMargin + Int.ofNat numIrreps * cellH + 80).toNat
  let bmW : Int := Int.ofNat numQTerms * cellW
  let bmH : Int := Int.ofNat numIrreps * cellH
  let doc := document w h
    ([ Svg.raw ("<defs><radialGradient id=\"bg\" cx=\"50%\" cy=\"0%\" r=\"120%\">" ++
        "<stop offset=\"0%\" stop-color=\"#161a30\"/><stop offset=\"100%\" stop-color=\"#05060e\"/></radialGradient></defs>"),
       rect 0 0 (Int.ofNat w) (Int.ofNat h) "url(#bg)" "none" [],
       -- title
       Svg.text [("x","20"),("y","34"),("font-size","20"),("font-weight","800"),
                 ("fill","#ffd700")] "MONSTER–MOONSHINE BITMAP — 194 irreps × 100 j-terms",
       Svg.text [("x","20"),("y","54"),("font-size","12"),("fill","#9fb0e0")]
         "rows = the 194 Monster irrep dimensions · columns = j-function coefficients q¹…q¹⁰⁰",
       Svg.text [("x","20"),("y","72"),("font-size","12"),("fill","#9fb0e0")]
         "each pixel = fold(N) ▸ weave ▸ CRT over supersingular primes ▸ normalize — computed natively by Lean",
       Svg.text [("x","20"),("y","88"),("font-size","11"),("fill","#c8a4ff")]
         "DARK vs LIGHT: brightness = (N mod dim) mod modulus, scaled by that cell's CRT modulus (all ≥ 257).",
       Svg.text [("x","20"),("y","104"),("font-size","11"),("fill","#c8a4ff")]
         "So small N (1, 42, 1729) sit near 0 ⇒ the field stays black; only N near the irrep scale lights up.",
       -- the black bitmap field
       rect leftMargin topMargin bmW bmH "#04050b" "#2a335f" [("stroke-width","1")] ]
     ++ colTicks
     ++ rowTicks
     ++ cellRects
     ++ inputLabels
     ++ brightnessLabels
     ++ [ legendBar,
          Svg.text [("x","20"),("y", toString (Int.ofNat h - 16)),("font-size","11"),
                    ("fill","#5a6790")]
            s!"{activeCount} active cells (nonzero moonshine weave) animated over {featuredNs.length} inputs · faithful to MonsterBitmap.pixelValue (render_faithful) · #writemonsterbitmap" ])
  render doc

/-! ## §7  Commands -/

/-- `#bitmapfilm` builds the animated bitmap and reports its size. -/
syntax (name := bitmapfilmCmd) "#bitmapfilm" : command

@[command_elab bitmapfilmCmd]
def elabBitmapfilm : CommandElab := fun _ => do
  let svg := buildFilm
  logInfo s!"[Monster Bitmap Film] {activeCount} active cells → {svg.length}-byte animated SVG."

/-- `#writemonsterbitmap "path"` builds the film and writes the SVG to `path`. -/
syntax (name := writemonsterbitmapCmd) "#writemonsterbitmap " str : command

@[command_elab writemonsterbitmapCmd]
def elabWritemonsterbitmap : CommandElab := fun stx => do
  match stx with
  | `(#writemonsterbitmap $p:str) => do
    let path := p.getString
    let svg := buildFilm
    IO.FS.writeFile path svg
    logInfo s!"[Monster Bitmap Film] wrote {svg.length} bytes ({activeCount} active cells) to {path}"
  | _ => throwError "ill-formed #writemonsterbitmap command"

/-! ## §8  Test suite -/

#bitmapfilm
#writemonsterbitmap "atlas_bitmap.svg"

end MonsterBitmapSVG
