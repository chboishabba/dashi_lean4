import RequestProject.PrimeProjection
import Lean

/-!
# IrrepFold: forcing every declaration into the available prime dimensions

This layer realises the request:

> force each element into the irrep — all other dimensions must fold into the
> available ones; nothing can exist outside of the available primes (and the
> repetitions of the q-expansion).  In the first step they are all at **one
> point** on the surface of the sphere; then on `71·59·47`; then on
> `71·59·41·31·…`.  Each step they take a new form — all the decls are squeezed
> into those layers so we can see them **deform** — but the **arrows between
> them must be preserved**.

## The construction

* **The atoms.** Every project declaration is reflected into an atom carrying its
  hash, its harmonic style class, and — crucially — the list of *other project
  declarations it references* (`FoldAtom.deps`, extracted via
  `Expr.getUsedConstants` over its value and type).  These references are the
  **arrows**.

* **The layers (folds).** A *layer* is a finite list of Monster primes — the only
  dimensions that exist in that fold.  `foldLayers` grows them step by step:
  the empty list (everything collapses to a **single point** on the sphere),
  then the requested `[71,59,47]`, then `[71,59,41,31]`, then ever larger
  prefixes of the fifteen Monster primes, ending at the full faithful
  fifteen-prime address.  Nothing is ever placed outside these primes.

* **Folding an atom into a layer.** For a hash `h` and a layer
  `ps = [p₀,…,p_{n-1}]`, atom `h` is squeezed onto the available dimensions: each
  prime `pᵢ` contributes its residue fraction `(h mod pᵢ)/pᵢ` along direction
  `2π i / n`, and the normalised vector sum gives its 2D location
  (`foldPos`).  The empty layer has no dimensions, so every atom lands at the one
  shared point.

* **Deformation, with arrows preserved.** Each atom carries a single SMIL
  `translate` animation that morphs it continuously through its per-layer
  locations, so we watch it *deform* as the available primes change.  Every arrow
  is a line whose four endpoint coordinates are animated in lockstep with the two
  atoms it joins, so the dependency arrows are **preserved** through every fold —
  they stretch and bend but never detach.

Commands:

* `#irrepfold`              — build the fold animation; report its size.
* `#writeirrepfold "path"`  — write the fold-animation SVG to `path`.
-/

open Lean Meta Elab Command SVG

namespace IrrepFold

open Introspect IntrospectSVG DualAtlas Moonshine PrimeProjection

/-! ## Atoms with their arrows -/

/-- One source-code atom for the fold animation: its name, reflected hash,
harmonic style class, and the list of other project declarations it references
(the **arrows** out of it). -/
structure FoldAtom where
  name  : Name
  hash  : Nat
  style : Nat
  deps  : List Name
deriving Repr

/-- Enumerate every project declaration into a `FoldAtom`, recording for each the
project declarations referenced in its value and type (its outgoing arrows). -/
def projectFoldAtoms : CommandElabM (List FoldAtom) := do
  let env ← getEnv
  let mut raw : List (Name × Nat × List Name) := []
  for (name, info) in env.constants.toList do
    if isProjectDecl name.toString then
      if let some e := info.value? then
        let h := e.hash.toNat
        let used := e.getUsedConstants ++ info.type.getUsedConstants
        let deps := (used.toList.filter
          (fun n => isProjectDecl n.toString && n != name)).eraseDups
        raw := (name, h, deps) :: raw
  let sorted := raw.toArray.qsort (fun a b => a.1.toString < b.1.toString) |>.toList
  return sorted.map (fun (n, h, deps) =>
    { name := n, hash := h, style := styleOfHarm (harmCode h), deps := deps })

/-- The arrows as index pairs `(i, j)`: atom `i` references atom `j`.  Self-loops
and references to declarations outside the atom list are dropped. -/
def foldEdges (atoms : List FoldAtom) : List (Nat × Nat) :=
  let names := atoms.map (·.name)
  (atoms.zipIdx.flatMap (fun (a, i) =>
    a.deps.filterMap (fun d =>
      match names.findIdx? (· == d) with
      | some j => if j == i then none else some (i, j)
      | none   => none))).eraseDups

/-! ## The fold layers (the available prime dimensions per step) -/

/-- The fold layers.  Step 0 is the empty layer (a single shared point — the
"surface of the sphere"); step 1 is the requested `71·59·47`; step 2 is the
requested `71·59·41·31`; the remaining steps grow through prefixes of the fifteen
Monster primes, ending at the full faithful fifteen-prime address.  Every layer
is a sublist of `monsterPrimes`, so nothing ever leaves Monster-prime space. -/
def foldLayers : List (List Nat) :=
  [[], [71, 59, 47], [71, 59, 41, 31]] ++
    (List.range 11).map (fun k => monsterPrimes.take (k + 5))

/-- Step 1 is exactly the requested single-prime-product tuple `71·59·47`. -/
theorem foldLayers_one : foldLayers[1]? = some [71, 59, 47] := by decide

/-- Step 2 is exactly the requested tuple `71·59·41·31`. -/
theorem foldLayers_two : foldLayers[2]? = some [71, 59, 41, 31] := by decide

/-- Every prime appearing in any fold layer is a Monster prime: nothing exists
outside the available primes. -/
theorem foldLayers_subset : ∀ l ∈ foldLayers, ∀ p ∈ l, p ∈ monsterPrimes := by
  native_decide

/-- The number of fold layers (steps). -/
def numLayers : Nat := foldLayers.length

/-! ## Folding an atom into a layer -/

/-- Plot centre and radius. -/
def foldCx : Float := 700.0
def foldCy : Float := 540.0
def foldR  : Float := 400.0

/-- Truncate a `Float` to an `Int` (for SVG coordinates). -/
def f2i (f : Float) : Int := f.toInt64.toInt

/-- Fold the atom with hash `h` onto the dimensions available in layer `ps`.
The empty layer has no dimensions, so every atom lands at one shared point on the
surface of the sphere; otherwise each available prime contributes its residue
fraction along its own direction and the normalised vector sum is the location. -/
def foldPos (h : Nat) (ps : List Nat) : Float × Float :=
  match ps with
  | [] => (foldCx, foldCy - foldR)
  | _  =>
    let n := ps.length
    let acc := ps.zipIdx.foldl
      (fun (s : Float × Float) (pi : Nat × Nat) =>
        let p := pi.1
        let i := pi.2
        let frac := if p == 0 then 0.0 else Float.ofNat (h % p) / Float.ofNat p
        let ang := PrimeProjection.tau * Float.ofNat i / Float.ofNat (max n 1)
        (s.1 + frac * Float.cos ang, s.2 + frac * Float.sin ang))
      (0.0, 0.0)
    let nf := Float.ofNat (max n 1)
    (foldCx + foldR * acc.1 / nf, foldCy + foldR * acc.2 / nf)

/-- The full list of per-layer locations for an atom (one point per fold step). -/
def trajectory (h : Nat) : List (Int × Int) :=
  foldLayers.map (fun ps => let (x, y) := foldPos h ps; (f2i x, f2i y))

/-! ## Animation value strings -/

/-- Duration of one full fold cycle. -/
def foldDur : String := "44s"

/-- A `;`-joined value string in which each entry is **doubled**, so that under
even time spacing every layer is held for one interval and then morphs to the
next over the following interval (settle, then deform). -/
def heldValues (xs : List String) : String :=
  String.intercalate ";" (xs.flatMap (fun s => [s, s]))

/-- The `translate` value string for an atom: its doubled per-layer positions. -/
def translateValues (h : Nat) : String :=
  heldValues ((trajectory h).map (fun (x, y) => s!"{x} {y}"))

/-- The doubled value string of one endpoint coordinate (x or y) of an atom. -/
def coordValues (h : Nat) (useX : Bool) : String :=
  heldValues ((trajectory h).map (fun (x, y) => toString (if useX then x else y)))

/-- The number of value frames (two per layer). -/
def numFrames : Nat := 2 * numLayers

/-! ## Rendering: arrows first, then atoms on top -/

/-- One dependency arrow as a line whose endpoints are animated in lockstep with
the two atoms it joins, so it deforms through every fold but stays attached. -/
def arrow (atoms : List FoldAtom) (e : Nat × Nat) : Svg :=
  match atoms[e.1]?, atoms[e.2]? with
  | some a, some b =>
    let (sx, sy) := (f2i foldCx, f2i (foldCy - foldR))
    Svg.elem "line"
      [("x1", toString sx), ("y1", toString sy),
       ("x2", toString sx), ("y2", toString sy),
       ("stroke", "#5566aa"), ("stroke-width", "1"), ("opacity", "0.28")]
      [ Svg.raw s!"<animate attributeName=\"x1\" dur=\"{foldDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{coordValues a.hash true}\"/>",
        Svg.raw s!"<animate attributeName=\"y1\" dur=\"{foldDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{coordValues a.hash false}\"/>",
        Svg.raw s!"<animate attributeName=\"x2\" dur=\"{foldDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{coordValues b.hash true}\"/>",
        Svg.raw s!"<animate attributeName=\"y2\" dur=\"{foldDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{coordValues b.hash false}\"/>" ]
  | _, _ => group []

/-- One atom: a marker group translated continuously through its per-layer
locations, so we watch it deform as the available primes change. -/
def atomMarker (a : FoldAtom) : Svg :=
  let (fill, glow) := colorOf a.style
  let (sx, sy) := (f2i foldCx, f2i (foldCy - foldR))
  Svg.elem "g"
    [("transform", s!"translate({sx} {sy})")]
    [ Svg.raw s!"<title>{SVG.esc a.name.toString} · hash {a.hash} · {styleName a.style} · {a.deps.length} arrows</title>",
      circle 0 0 7 "none" glow [("opacity", "0.40"), ("filter", "url(#fglow)")],
      circle 0 0 5 fill "#05060f" [("stroke-width", "1")],
      Svg.raw s!"<animateTransform attributeName=\"transform\" attributeType=\"XML\" type=\"translate\" dur=\"{foldDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{translateValues a.hash}\"/>" ]

/-! ## Chrome (background sphere, banner, HUD) -/

/-- A faint reference "sphere": the boundary circle whose surface holds the
single collapsed point, plus a couple of inner guides. -/
def sphereFrame : Svg :=
  group
    [ circle (f2i foldCx) (f2i foldCy) (f2i foldR) "none" "#23305f"
        [("stroke-width", "1"), ("opacity", "0.6")],
      circle (f2i foldCx) (f2i foldCy) (f2i (foldR * 0.66)) "none" "#1a2348"
        [("stroke-width", "1"), ("opacity", "0.45")],
      circle (f2i foldCx) (f2i foldCy) (f2i (foldR / 3.0)) "none" "#1a2348"
        [("stroke-width", "1"), ("opacity", "0.4")],
      circle (f2i foldCx) (f2i (foldCy - foldR)) 4 "#ffd700" "#05060f"
        [("opacity", "0.8")],
      Svg.text [("x", toString (f2i foldCx + 10)), ("y", toString (f2i (foldCy - foldR) - 8)),
                ("font-size", "12"), ("fill", "#ffd700")]
        "step 1 · all decls at one point on the sphere" ]

/-- A `;`-joined visibility string (length `numFrames`) that is "1" exactly while
fold layer `i` is the active step. -/
def hudVis (i : Nat) : String :=
  String.intercalate ";"
    ((List.range numFrames).map (fun f => if f / 2 == i then "1" else "0"))

/-- One HUD frame for fold layer `i`, visible only during that step. -/
def hudFrame (i : Nat) : Svg :=
  let ps := foldLayers.getD i []
  let tuple :=
    if ps.isEmpty then "(single point — sphere surface)"
    else String.intercalate "·" (ps.map toString)
  group
    [ Svg.text [("x", "40"), ("y", "1000"), ("font-size", "22"), ("font-weight", "800"),
                ("fill", "#ffd700")]
        s!"FOLD {i + 1} / {numLayers}",
      Svg.text [("x", "230"), ("y", "1000"), ("font-size", "16"), ("fill", "#7ad9ff")]
        s!"available dimensions:  {tuple}",
      Svg.text [("x", "40"), ("y", "1026"), ("font-size", "13"), ("fill", "#9fb0e0")]
        s!"every decl squeezed onto {ps.length} prime dimension(s) — arrows preserved through the deformation",
      Svg.raw s!"<animate attributeName=\"opacity\" dur=\"{foldDur}\" repeatCount=\"indefinite\" calcMode=\"discrete\" values=\"{hudVis i}\"/>" ]

def defsRaw : String :=
  "<defs>" ++
  "<radialGradient id=\"fbg\" cx=\"46%\" cy=\"40%\" r=\"85%\">" ++
    "<stop offset=\"0%\" stop-color=\"#141a3a\"/><stop offset=\"100%\" stop-color=\"#05060f\"/></radialGradient>" ++
  "<linearGradient id=\"fbanner\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">" ++
    "<stop offset=\"0%\" stop-color=\"#00c2c2\"/><stop offset=\"50%\" stop-color=\"#ffd700\"/><stop offset=\"100%\" stop-color=\"#8a2be2\"/></linearGradient>" ++
  "<filter id=\"fglow\" x=\"-60%\" y=\"-60%\" width=\"220%\" height=\"220%\">" ++
    "<feGaussianBlur stdDeviation=\"2.4\"/></filter>" ++
  "</defs>"

def banner : Svg :=
  group
    [ rect 30 22 1340 86 "url(#fbanner)" "#0b0c18" [("rx", "14"), ("stroke-width", "3")],
      Svg.text [("x", "56"), ("y", "68"), ("font-size", "30"), ("font-weight", "800"),
                ("fill", "#0b0c18"), ("letter-spacing", "1")]
        "IRREP FOLD · DECLS SQUEEZED INTO THE AVAILABLE PRIMES · ARROWS PRESERVED",
      Svg.text [("x", "58"), ("y", "96"), ("font-size", "14"), ("font-weight", "600"),
                ("fill", "#1a1f3c")]
        "from one point on the sphere, to 71·59·47, to 71·59·41·31, … to the full 15-prime address — every decl deforms, dependency arrows stay attached" ]

/-! ## Assembly -/

/-- Build the full fold-animation SVG document string. -/
def buildFold (atoms : List FoldAtom) : String :=
  let edges := foldEdges atoms
  let arrows := group (edges.map (arrow atoms))
  let markers := group (atoms.map atomMarker)
  let huds := group ((List.range numLayers).map hudFrame)
  let doc := document 1400 1040
    [ Svg.raw defsRaw,
      rect 0 0 1400 1040 "url(#fbg)" "none" [],
      banner,
      sphereFrame,
      arrows,
      markers,
      huds,
      Svg.text [("x", "40"), ("y", "1010"), ("font-size", "11"), ("fill", "#5a6790")]
        s!"generated natively by Lean · {atoms.length} decls · {edges.length} arrows · folds = prefixes of the 15 Monster primes · positions = Σᵢ (h mod pᵢ)/pᵢ · e^(2πi·i/n) · #writeirrepfold" ]
  render doc

/-! ## Commands -/

/-- `#irrepfold` builds the fold animation and reports its size. -/
syntax (name := irrepfoldCmd) "#irrepfold" : command

@[command_elab irrepfoldCmd]
def elabIrrepfold : CommandElab := fun _ => do
  let atoms ← projectFoldAtoms
  let edges := foldEdges atoms
  let svg := buildFold atoms
  logInfo s!"[Irrep Fold] folded {atoms.length} decls (with {edges.length} preserved arrows) through {numLayers} prime-layer steps → {svg.length}-byte animated SVG."

/-- `#writeirrepfold "path"` writes the fold-animation SVG to `path`. -/
syntax (name := writeirrepfoldCmd) "#writeirrepfold " str : command

@[command_elab writeirrepfoldCmd]
def elabWriteirrepfold : CommandElab := fun stx => do
  match stx with
  | `(#writeirrepfold $p:str) => do
    let path := p.getString
    let atoms ← projectFoldAtoms
    let edges := foldEdges atoms
    let svg := buildFold atoms
    IO.FS.writeFile path svg
    logInfo s!"[Irrep Fold] wrote {svg.length} bytes ({atoms.length} decls, {edges.length} arrows, {numLayers} folds) to {path}"
  | _ => throwError "ill-formed #writeirrepfold command"

/-! ## Build-time generation -/

#irrepfold

#writeirrepfold "atlas_irrepfold.svg"

end IrrepFold
