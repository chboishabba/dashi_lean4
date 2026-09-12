import RequestProject.ExprAddress
import RequestProject.MonsterBitmapSVG
import RequestProject.SVG
import Lean

/-!
# ExprAddressSVG — the Monster bitmap, addressed by *declarations*

`RequestProject.MonsterBitmapSVG` renders the Monster–Moonshine bitmap as a
flip-book over a hand-picked list of inputs `N = [1, 42, 1729, …]`.

This layer keeps the exact same pipeline (same 194 irrep rows, same 100 j-term
columns, same fold ▸ weave ▸ CRT ▸ normalize per cell) but replaces those
arbitrary inputs with the **structural fingerprints of real declarations**
(`ExprAddress.declStructuralSum`).  Each frame of the film is therefore one
declaration, placed in the Monster's arithmetic by the intrinsic shape of its
own expression tree, and annotated on-canvas with its fingerprint `k` and its
CRT address `(k % 71, k % 59, k % 47)`.

The addressing is purely combinatorial — the picture records *where each
declaration's structural fingerprint lands* in the irrep / CRT coordinate space,
and nothing more.

Commands:

* `#exprfilm`               — gather the declaration frames and report film size.
* `#writeexpraddress "path"` — write the declaration-addressed bitmap SVG.
-/

open Lean Meta Elab Command SVG

namespace ExprAddressSVG

open MonsterBitmap MonsterBitmapSVG ExprAddress

/-! ## §1  Choosing the declaration frames -/

/-- A reasonable spread of declarations to animate: a few project declarations
plus some Lean-core staples, so the viewer sees both small foundational
fingerprints and larger derived ones. -/
def frameDecls : List Name :=
  [`Nat.add, `Nat.mul, `List.map, `List.foldr, `Prod.fst,
   `DualAtlas.cogProj, `MonsterBitmap.fold, `ExprAddress.crtTriple]

/-- Compute the `(name, fingerprint)` frame list for the chosen declarations,
keeping only those that resolve in the current environment. -/
def gatherFrames : CommandElabM (Array (Name × Nat)) := do
  let env ← getEnv
  let mut acc : Array (Name × Nat) := #[]
  for decl in frameDecls do
    if let some info := env.find? decl then
      let tSum := exprStructuralSum info.type
      let vSum := match info.value? with
        | some v => exprStructuralSum v
        | none   => 0
      acc := acc.push (decl, tSum + vSum)
  return acc

/-! ## §2  Building the film from declaration frames -/

/-- The animated bitmap cells: every active cell's fill cycles over the
declaration fingerprints. -/
def cellRectsOf (frames : Array (Name × Nat)) : List Svg := Id.run do
  let ks := frames.map (·.2)
  let mut acc : Array Svg := #[]
  for n in List.range numQTerms do
    let wcol := weaveArr (jCoeffNat n)
    for i in List.range numIrreps do
      if wcol[i]! != 0 then
        let d := degArr[i]!
        let modulus := radArr[i]!
        let denom := max 1 (modulus - 1)
        let cols := ks.toList.map (fun k =>
          let v := min ((k % d % modulus) * 255 / denom) 255
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

/-- The per-frame declaration label: name, fingerprint and CRT triple,
opacity-cycled so exactly one shows at a time. -/
def frameLabelsOf (frames : Array (Name × Nat)) : List Svg :=
  let k := frames.size + 1
  frames.toList.zipIdx.map (fun ((name, kk), idx) =>
    let (a, b, c) := crtTriple kk
    let vals := (List.range k).map (fun f => if f == idx then "1" else "0")
    let values := String.intercalate ";" vals
    Svg.elem "text"
      [("x","70"), ("y","126"), ("font-size","16"), ("font-weight","800"),
       ("fill","#ffd700"), ("opacity", if idx == 0 then "1" else "0")]
      [ Svg.raw s!"<animate attributeName=\"opacity\" values=\"{values}\" dur=\"{loopDur}\" calcMode=\"discrete\" repeatCount=\"indefinite\"/>",
        Svg.raw s!"{SVG.esc name.toString}   k={kk}   CRT=({a},{b},{c})" ])

/-- Build the complete declaration-addressed bitmap SVG. -/
def buildFilm (frames : Array (Name × Nat)) : String :=
  let w : Nat := (leftMargin + Int.ofNat numQTerms * cellW + 40).toNat
  let h : Nat := (topMargin + Int.ofNat numIrreps * cellH + 80).toNat
  let bmW : Int := Int.ofNat numQTerms * cellW
  let bmH : Int := Int.ofNat numIrreps * cellH
  let doc := document w h
    ([ Svg.raw ("<defs><radialGradient id=\"bg\" cx=\"50%\" cy=\"0%\" r=\"120%\">" ++
        "<stop offset=\"0%\" stop-color=\"#161a30\"/><stop offset=\"100%\" stop-color=\"#05060e\"/></radialGradient></defs>"),
       rect 0 0 (Int.ofNat w) (Int.ofNat h) "url(#bg)" "none" [],
       Svg.text [("x","20"),("y","34"),("font-size","20"),("font-weight","800"),
                 ("fill","#ffd700")] "DECLARATION-ADDRESSED MONSTER BITMAP — 194 irreps × 100 j-terms",
       Svg.text [("x","20"),("y","54"),("font-size","12"),("fill","#9fb0e0")]
         "each frame is one declaration; its input k = sum of Expr constructor codes over the whole expression tree",
       Svg.text [("x","20"),("y","72"),("font-size","12"),("fill","#9fb0e0")]
         "rows = the 194 Monster irrep dimensions · columns = j-function coefficients q¹…q¹⁰⁰ · pipeline identical to MonsterBitmap",
       Svg.text [("x","20"),("y","88"),("font-size","11"),("fill","#c8a4ff")]
         "CRT address (k mod 71,59,47) uniquely locates k in [0,196883) since 196883 = 47·59·71 (ExprAddress.crtTriple_inj).",
       Svg.text [("x","20"),("y","104"),("font-size","11"),("fill","#c8a4ff")]
         "Addressing is purely combinatorial: it records where each declaration's structural fingerprint lands, nothing more.",
       rect leftMargin topMargin bmW bmH "#04050b" "#2a335f" [("stroke-width","1")] ]
     ++ colTicks
     ++ rowTicks
     ++ cellRectsOf frames
     ++ frameLabelsOf frames
     ++ [ legendBar,
          Svg.text [("x","20"),("y", toString (Int.ofNat h - 16)),("font-size","11"),
                    ("fill","#5a6790")]
            s!"{activeCount} active cells (nonzero moonshine weave) animated over {frames.size} declarations · pipeline faithful to MonsterBitmap.pixelValue · #writeexpraddress" ])
  render doc

/-! ## §3  Commands -/

/-- `#exprfilm` gathers the declaration frames and reports the film size. -/
syntax (name := exprfilmCmd) "#exprfilm" : command

@[command_elab exprfilmCmd]
def elabExprfilm : CommandElab := fun _ => do
  let frames ← gatherFrames
  let svg := buildFilm frames
  logInfo s!"[Declaration Bitmap Film] {frames.size} declaration frames, {activeCount} active cells → {svg.length}-byte animated SVG."

/-- `#writeexpraddress "path"` writes the declaration-addressed bitmap SVG. -/
syntax (name := writeexpraddressCmd) "#writeexpraddress " str : command

@[command_elab writeexpraddressCmd]
def elabWriteexpraddress : CommandElab := fun stx => do
  match stx with
  | `(#writeexpraddress $p:str) => do
    let path := p.getString
    let frames ← gatherFrames
    let svg := buildFilm frames
    IO.FS.writeFile path svg
    logInfo s!"[Declaration Bitmap Film] wrote {svg.length} bytes ({frames.size} frames, {activeCount} active cells) to {path}"
  | _ => throwError "ill-formed #writeexpraddress command"

/-! ## §4  Build-time generation -/

#exprfilm
#writeexpraddress "atlas_expraddress.svg"

end ExprAddressSVG
