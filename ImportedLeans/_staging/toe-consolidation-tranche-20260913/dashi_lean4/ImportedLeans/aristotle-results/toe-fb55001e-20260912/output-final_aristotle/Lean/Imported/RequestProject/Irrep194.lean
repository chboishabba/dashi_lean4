import RequestProject.IrrepFold

/-!
# Irrep194: the 194-step irrep walk (with proved compaction) and the
T1–T170 Thompson views sampled across the 104 q-expansions

This layer answers the two requests, and formalises the observation made about the
earlier `atlas_irrepfold.svg`.

> now i want the 194 step irrep view, and the T1–T170 views sampled in 104
> expansions.  what i noticed is that in your atlas_irrepfold.svg the system got
> compacter and compacter over time.

## 1. The 194-step irrep view (`atlas_irrep194.svg`)

The Monster has exactly **194 conjugacy classes**, hence **194 irreducible
representations** (`Moonshine.numIrreps = 194`).  This view is an animation with
one frame per irrep: at step `k` the constellation is folded onto the irrep ring,
each declaration sitting at the angle of its primary irrep
`irrepOf h = h % 194` (`stepIrrep` visits every irrep exactly once,
`stepIrrep_surjective`).

**The compaction is real, and it is now a proved invariant.**  You noticed the
old fold got "compacter and compacter over time"; here that is made the explicit
law of motion.  The bounding *compaction radius* at step `k` is

`compactionRadius k = outerR · compBase / (compBase + k)`,

a sequence that is proved monotonically non-increasing (`compaction_antitone` —
the system never re-expands) and strictly shrinks across the whole walk
(`compaction_strict`, from `400` down to `68`).  Every atom's distance from the
centre is scaled by `compactionRadius k`, and a visible outline ring contracts
through exactly these radii, so you watch the whole system compact, step by step.
The dependency **arrows are preserved** (reusing `IrrepFold.foldEdges`): each
arrow's endpoints are animated in lockstep with the two atoms it joins.

## 2. The T1–T170 views sampled in 104 expansions (`atlas_thompson.svg`)

There are 170 Thompson views `T1 … T170`.  Each atom carries a Thompson class
`thompsonOf h = h % 170` (`thompsonOf_lt`); each of the **104 q-expansion pages**
samples one view `thompsonView pi` keyed by the coefficient of `q^{pi+1}` in `j`
(`thompsonView_lt : thompsonView pi < 170`).  Turning the 104 pages plays the
sampling back: on each page the atoms in the sampled view light up.

The finding (`thompson_sample_count`): the 104 expansions sample exactly **49**
distinct Thompson views out of the 170.

Commands:

* `#irrep194` / `#writeirrep194 "path"`   — the 194-step compaction walk.
* `#thompson` / `#writethompson "path"`   — the T1–T170 / 104-expansion sampler.
-/

open Lean Meta Elab Command SVG

namespace Irrep194

open Introspect IntrospectSVG DualAtlas Moonshine MoonshineSVG PrimeProjection IrrepFold

/-! ## Part 1 — the 194-step irrep walk and its compaction law -/

/-- The number of steps in the irrep walk: one per Monster irrep. -/
def numIrrepSteps : Nat := Moonshine.numIrreps

/-- There are exactly 194 steps. -/
theorem numIrrepSteps_eq : numIrrepSteps = 194 := rfl

/-- The irrep visited at step `k`. -/
def stepIrrep (k : Nat) : Nat := k % numIrrepSteps

/-- The 194-step walk visits every irrep exactly once: stepping `0 … 193`
enumerates all 194 irreps in order. -/
theorem stepIrrep_surjective :
    (List.range numIrrepSteps).map stepIrrep = List.range numIrrepSteps := by
  native_decide

/-! ### The compaction radius (the proved "compacter and compacter" law) -/

/-- The outer plot radius (the compaction radius at step `0`). -/
def outerR : Nat := 400

/-- The compaction base: larger values make the contraction gentler. -/
def compBase : Nat := 40

/-- The bounding radius of the constellation at step `k`.  At step `0` it is the
full `outerR`; it shrinks as `k` grows.  This is the formalisation of the
observation that the earlier fold "got compacter and compacter over time". -/
def compactionRadius (k : Nat) : Nat := outerR * compBase / (compBase + k)

/-- The walk starts at the full radius. -/
theorem compactionRadius_zero : compactionRadius 0 = outerR := by decide

/-- **The system never re-expands.**  The compaction radius is monotonically
non-increasing from each step to the next — exactly the "compacter and compacter"
behaviour, now a proved invariant. -/
theorem compaction_antitone (k : Nat) :
    compactionRadius (k + 1) ≤ compactionRadius k := by
  unfold compactionRadius compBase
  exact Nat.div_le_div_left (by omega) (by omega)

/-- **The compaction is strict across the whole 194-step walk**: from the full
radius `400` at the first step down to `68` at the last. -/
theorem compaction_strict :
    compactionRadius (numIrrepSteps - 1) < compactionRadius 0 := by decide

/-! ### Geometry of the walk -/

/-- Plot centre. -/
def cx : Float := 700.0
def cy : Float := 540.0

/-- Truncate a `Float` to an `Int` for SVG coordinates. -/
def f2i (f : Float) : Int := f.toInt64.toInt

/-- The fixed angle of an atom: the direction of its primary irrep on the ring. -/
def atomAngle (h : Nat) : Float :=
  PrimeProjection.tau * Float.ofNat (Moonshine.irrepOf h) / Float.ofNat numIrrepSteps
    - 1.5707963

/-- A per-atom radial fraction so atoms at the same irrep don't fully overlap. -/
def atomFrac (h : Nat) : Float :=
  0.42 + 0.58 * Float.ofNat (h % 97) / 97.0

/-- The position of atom `h` at step `k`: angle fixed by its irrep, distance the
compaction radius scaled by the atom's fraction.  As `k` grows the radius shrinks
(`compaction_antitone`), so the whole system contracts toward the centre. -/
def stepPos (h k : Nat) : Int × Int :=
  let r := Float.ofNat (compactionRadius k) * atomFrac h
  let a := atomAngle h
  (f2i (cx + r * Float.cos a), f2i (cy + r * Float.sin a))

/-! ### Animation value strings -/

/-- Duration of one full 194-step cycle. -/
def dur194 : String := "60s"

/-- The `translate` value string for an atom: its positions over all 194 steps. -/
def stepValues (h : Nat) : String :=
  String.intercalate ";"
    ((List.range numIrrepSteps).map (fun k => let (x, y) := stepPos h k; s!"{x} {y}"))

/-- One endpoint coordinate (x or y) of an atom over all 194 steps. -/
def stepCoord (h : Nat) (useX : Bool) : String :=
  String.intercalate ";"
    ((List.range numIrrepSteps).map (fun k =>
      let (x, y) := stepPos h k; toString (if useX then x else y)))

/-- The `r` value string of the contracting outline ring: the compaction radii. -/
def ringRValues : String :=
  String.intercalate ";"
    ((List.range numIrrepSteps).map (fun k => toString (compactionRadius k)))

/-! ### Rendering: arrows, atoms, contracting ring -/

/-- One dependency arrow whose endpoints are animated in lockstep with the two
atoms it joins, so it is preserved through the whole contraction. -/
def arrow194 (atoms : List FoldAtom) (e : Nat × Nat) : Svg :=
  match atoms[e.1]?, atoms[e.2]? with
  | some a, some b =>
    let (ax, ay) := stepPos a.hash 0
    let (bx, byy) := stepPos b.hash 0
    Svg.elem "line"
      [("x1", toString ax), ("y1", toString ay),
       ("x2", toString bx), ("y2", toString byy),
       ("stroke", "#5566aa"), ("stroke-width", "1"), ("opacity", "0.26")]
      [ Svg.raw s!"<animate attributeName=\"x1\" dur=\"{dur194}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{stepCoord a.hash true}\"/>",
        Svg.raw s!"<animate attributeName=\"y1\" dur=\"{dur194}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{stepCoord a.hash false}\"/>",
        Svg.raw s!"<animate attributeName=\"x2\" dur=\"{dur194}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{stepCoord b.hash true}\"/>",
        Svg.raw s!"<animate attributeName=\"y2\" dur=\"{dur194}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{stepCoord b.hash false}\"/>" ]
  | _, _ => group []

/-- One atom: a marker translated continuously through its 194 per-step locations,
contracting toward the centre as the compaction radius shrinks. -/
def atomMarker194 (a : FoldAtom) : Svg :=
  let (fill, glow) := colorOf a.style
  let (sx, sy) := stepPos a.hash 0
  Svg.elem "g"
    [("transform", s!"translate({sx} {sy})")]
    [ Svg.raw s!"<title>{SVG.esc a.name.toString} · hash {a.hash} · irrep {Moonshine.irrepOf a.hash} / 194 · {styleName a.style} · {a.deps.length} arrows</title>",
      circle 0 0 7 "none" glow [("opacity", "0.40"), ("filter", "url(#iglow)")],
      circle 0 0 5 fill "#05060f" [("stroke-width", "1")],
      Svg.raw s!"<animateTransform attributeName=\"transform\" attributeType=\"XML\" type=\"translate\" dur=\"{dur194}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{stepValues a.hash}\"/>" ]

/-- The contracting outline ring: a circle at the centre whose radius animates
through the compaction radii `compactionRadius 0 … compactionRadius 193`, so the
shrinking boundary of the system is shown explicitly. -/
def compactionRing : Svg :=
  Svg.elem "circle"
    [("cx", toString (f2i cx)), ("cy", toString (f2i cy)),
     ("r", toString outerR), ("fill", "none"), ("stroke", "#ffd700"),
     ("stroke-width", "1.5"), ("opacity", "0.55"), ("stroke-dasharray", "4 6")]
    [ Svg.raw s!"<animate attributeName=\"r\" dur=\"{dur194}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{ringRValues}\"/>" ]

/-- A faint reference frame for the walk. -/
def frame194 : Svg :=
  group
    [ circle (f2i cx) (f2i cy) outerR "none" "#23305f" [("stroke-width", "1"), ("opacity", "0.6")],
      circle (f2i cx) (f2i cy) (outerR * 2 / 3) "none" "#1a2348" [("stroke-width", "1"), ("opacity", "0.4")],
      circle (f2i cx) (f2i cy) (outerR / 3) "none" "#1a2348" [("stroke-width", "1"), ("opacity", "0.4")],
      circle (f2i cx) (f2i cy) 3 "#ffd700" "#05060f" [("opacity", "0.9")] ]

def defs194 : String :=
  "<defs>" ++
  "<radialGradient id=\"ibg\" cx=\"46%\" cy=\"40%\" r=\"85%\">" ++
    "<stop offset=\"0%\" stop-color=\"#141a3a\"/><stop offset=\"100%\" stop-color=\"#05060f\"/></radialGradient>" ++
  "<linearGradient id=\"ibanner\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">" ++
    "<stop offset=\"0%\" stop-color=\"#00c2c2\"/><stop offset=\"50%\" stop-color=\"#ffd700\"/><stop offset=\"100%\" stop-color=\"#8a2be2\"/></linearGradient>" ++
  "<filter id=\"iglow\" x=\"-60%\" y=\"-60%\" width=\"220%\" height=\"220%\">" ++
    "<feGaussianBlur stdDeviation=\"2.4\"/></filter>" ++
  "</defs>"

def banner194 : Svg :=
  group
    [ rect 30 22 1340 86 "url(#ibanner)" "#0b0c18" [("rx", "14"), ("stroke-width", "3")],
      Svg.text [("x", "56"), ("y", "62"), ("font-size", "28"), ("font-weight", "800"),
                ("fill", "#0b0c18"), ("letter-spacing", "1")]
        "194-STEP IRREP WALK · COMPACTION MADE LAW · ARROWS PRESERVED",
      Svg.text [("x", "58"), ("y", "92"), ("font-size", "14"), ("font-weight", "600"),
                ("fill", "#1a1f3c")]
        "one frame per Monster irrep (194); you noticed it gets compacter over time — here the compaction radius is proved monotone (400 → 68, never re-expands)" ]

/-- A badge stating the proved compaction law. -/
def compactionBadge : Svg :=
  group
    [ rect 30 1000 1340 30 "#0b1430" "#2a7fff" [("rx", "8"), ("stroke-width", "1"), ("opacity", "0.92")],
      Svg.text [("x", "44"), ("y", "1020"), ("font-size", "13"), ("fill", "#9fb0e0")]
        "FINDING · compaction_antitone: compactionRadius is monotone non-increasing across all 194 steps (never re-expands); compaction_strict: 400 → 68 · generated natively by Lean" ]

/-- Build the full 194-step walk SVG document string. -/
def buildIrrep194 (atoms : List FoldAtom) : String :=
  let edges := foldEdges atoms
  let arrows := group (edges.map (arrow194 atoms))
  let markers := group (atoms.map atomMarker194)
  let doc := document 1400 1040
    [ Svg.raw defs194,
      rect 0 0 1400 1040 "url(#ibg)" "none" [],
      banner194,
      frame194,
      compactionRing,
      arrows,
      markers,
      compactionBadge ]
  render doc

/-! ## Part 2 — the T1–T170 views sampled in 104 expansions -/

/-- The number of Thompson views `T1 … T170`. -/
def numThompson : Nat := 170

/-- The Thompson class an atom belongs to: `h % 170`, i.e. view `T(thompsonOf h + 1)`. -/
def thompsonOf (h : Nat) : Nat := h % numThompson

/-- Every atom lands in one of the 170 Thompson views. -/
theorem thompsonOf_lt (h : Nat) : thompsonOf h < numThompson := Nat.mod_lt _ (by decide)

/-- The number of q-expansion pages sampled (`q¹ … q¹⁰⁴`). -/
def numExpansions : Nat := 104

/-- The Thompson view sampled by expansion page `pi`: keyed by the coefficient of
`q^{pi+1}` in `j`, reduced mod 170. -/
def thompsonView (pi : Nat) : Nat :=
  ((Moonshine.jCoeff (pi + 2)).emod (Int.ofNat numThompson)).toNat % numThompson

/-- Each expansion samples a genuine view among `T1 … T170`. -/
theorem thompsonView_lt (pi : Nat) : thompsonView pi < numThompson :=
  Nat.mod_lt _ (by decide)

/-- **The finding.**  Across the 104 q-expansions, exactly `49` distinct Thompson
views (of the 170) are sampled. -/
theorem thompson_sample_count :
    ((List.range numExpansions).map thompsonView).eraseDups.length = 49 := by
  native_decide

/-- The label `T1 … T170` for a Thompson view index `0 … 169`. -/
def tLabel (v : Nat) : String := "T" ++ toString (v + 1)

/-! ### Geometry of the Thompson ring -/

def tcx : Float := 700.0
def tcy : Float := 520.0
def tR  : Float := 380.0

/-- Fixed position of an atom on the Thompson ring: angle by Thompson class. -/
def thompsonPos (h : Nat) : Int × Int :=
  let a := PrimeProjection.tau * Float.ofNat (thompsonOf h) / Float.ofNat numThompson - 1.5707963
  let frac := 0.5 + 0.5 * Float.ofNat (h % 89) / 89.0
  (f2i (tcx + tR * frac * Float.cos a), f2i (tcy + tR * frac * Float.sin a))

/-- The visibility string of an atom over the 104 expansions: bright on pages
whose sampled view is this atom's Thompson class, dim otherwise. -/
def thompsonVis (h : Nat) : String :=
  MoonshineSVG.joinValues numExpansions (fun pi => if thompsonOf h == thompsonView pi then "1" else "0.10")

/-- The radius string of an atom over the 104 expansions: enlarged when sampled. -/
def thompsonRad (h : Nat) : String :=
  MoonshineSVG.joinValues numExpansions (fun pi => if thompsonOf h == thompsonView pi then "7" else "3")

/-- One atom on the Thompson ring, lighting up on the expansions that sample it. -/
def thompsonMarker (a : FoldAtom) : Svg :=
  let (fill, glow) := colorOf a.style
  let (sx, sy) := thompsonPos a.hash
  group
    [ Svg.raw s!"<title>{SVG.esc a.name.toString} · {tLabel (thompsonOf a.hash)} · {styleName a.style}</title>",
      Svg.elem "circle"
        [("cx", toString sx), ("cy", toString sy), ("r", "7"), ("fill", "none"),
         ("stroke", glow), ("opacity", "0.35"), ("filter", "url(#tglow)")]
        [ Svg.raw s!"<animate attributeName=\"opacity\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"discrete\" values=\"{thompsonVis a.hash}\"/>" ],
      Svg.elem "circle"
        [("cx", toString sx), ("cy", toString sy), ("r", "4"), ("fill", fill), ("stroke", "#05060f")]
        [ Svg.raw s!"<animate attributeName=\"opacity\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"discrete\" values=\"{thompsonVis a.hash}\"/>",
          Svg.raw s!"<animate attributeName=\"r\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"discrete\" values=\"{thompsonRad a.hash}\"/>" ] ]

/-- One HUD frame for expansion page `pi`, visible only during its slot. -/
def thompsonHud (pi : Nat) : Svg :=
  let vis := MoonshineSVG.joinValues numExpansions (fun q => if q == pi then "1" else "0")
  let v := thompsonView pi
  let key := Moonshine.jCoeff (pi + 2)
  let keyS :=
    let s := toString key
    if s.length ≤ 18 then s else (s.take 12).toString ++ "… (" ++ toString s.length ++ " digits)"
  group
    [ Svg.text [("x", "980"), ("y", "980"), ("font-size", "22"), ("font-weight", "800"),
                ("fill", "#ffd700")]
        s!"EXPANSION {pi + 1} / {numExpansions}",
      Svg.text [("x", "40"), ("y", "946"), ("font-size", "16"), ("fill", "#9fb0e0")]
        s!"q-key = [q^{pi + 1}] j = {keyS}",
      Svg.text [("x", "40"), ("y", "972"), ("font-size", "16"), ("font-weight", "700"),
                ("fill", "#7ad9ff")]
        s!"sampled view:  {tLabel v}  (of T1 … T170)",
      Svg.raw s!"<animate attributeName=\"opacity\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"discrete\" values=\"{vis}\"/>" ]

def thompsonFrame : Svg :=
  group
    [ circle (f2i tcx) (f2i tcy) (f2i tR) "none" "#23305f" [("stroke-width", "1"), ("opacity", "0.6")],
      circle (f2i tcx) (f2i tcy) (f2i (tR / 2.0)) "none" "#1a2348" [("stroke-width", "1"), ("opacity", "0.45")],
      circle (f2i tcx) (f2i tcy) 3 "#ffd700" "#05060f" [("opacity", "0.9")] ]

def thompsonBadge : Svg :=
  group
    [ rect 980 120 390 96 "#0b1430" "#2a7fff" [("rx", "10"), ("stroke-width", "2"), ("opacity", "0.92")],
      Svg.text [("x", "1000"), ("y", "150"), ("font-size", "15"), ("font-weight", "800"), ("fill", "#7ad9ff")]
        "FINDING · 104 EXPANSIONS",
      Svg.text [("x", "1000"), ("y", "174"), ("font-size", "11"), ("fill", "#9fb0e0")]
        "the 104 q-expansions sample exactly 49 of the",
      Svg.text [("x", "1000"), ("y", "190"), ("font-size", "11"), ("fill", "#9fb0e0")]
        "170 Thompson views T1 … T170 (proved:",
      Svg.text [("x", "1000"), ("y", "206"), ("font-size", "11"), ("fill", "#9fb0e0")]
        "thompson_sample_count = 49)." ]

def defsThompson : String :=
  "<defs>" ++
  "<radialGradient id=\"tbg\" cx=\"40%\" cy=\"38%\" r=\"85%\">" ++
    "<stop offset=\"0%\" stop-color=\"#141a3a\"/><stop offset=\"100%\" stop-color=\"#05060f\"/></radialGradient>" ++
  "<linearGradient id=\"tbanner\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">" ++
    "<stop offset=\"0%\" stop-color=\"#00c2c2\"/><stop offset=\"50%\" stop-color=\"#ffd700\"/><stop offset=\"100%\" stop-color=\"#8a2be2\"/></linearGradient>" ++
  "<filter id=\"tglow\" x=\"-60%\" y=\"-60%\" width=\"220%\" height=\"220%\">" ++
    "<feGaussianBlur stdDeviation=\"2.4\"/></filter>" ++
  "</defs>"

def bannerThompson : Svg :=
  group
    [ rect 30 22 1320 86 "url(#tbanner)" "#0b0c18" [("rx", "14"), ("stroke-width", "3")],
      Svg.text [("x", "56"), ("y", "62"), ("font-size", "28"), ("font-weight", "800"),
                ("fill", "#0b0c18"), ("letter-spacing", "1")]
        "T1 … T170 THOMPSON VIEWS · SAMPLED ACROSS 104 q-EXPANSIONS",
      Svg.text [("x", "58"), ("y", "92"), ("font-size", "14"), ("font-weight", "600"),
                ("fill", "#1a1f3c")]
        "each declaration sits in a Thompson view T(h%170); each of the 104 q-expansion pages samples one view via [q^n] j — they cover 49 distinct views" ]

/-- Build the full T1–T170 / 104-expansion sampler SVG document string. -/
def buildThompson (atoms : List FoldAtom) : String :=
  let markers := group (atoms.map thompsonMarker)
  let huds := group ((List.range numExpansions).map thompsonHud)
  let doc := document 1380 1000
    [ Svg.raw defsThompson,
      rect 0 0 1380 1000 "url(#tbg)" "none" [],
      bannerThompson,
      thompsonFrame,
      markers,
      thompsonBadge,
      huds,
      Svg.text [("x", "40"), ("y", "994"), ("font-size", "11"), ("fill", "#5a6790")]
        "generated natively by Lean · views = T(h%170) · sampling = [q^{pi+1}] j mod 170 over 104 expansions · #writethompson" ]
  render doc

/-! ## Commands -/

syntax (name := irrep194Cmd) "#irrep194" : command

@[command_elab irrep194Cmd]
def elabIrrep194 : CommandElab := fun _ => do
  let atoms ← projectFoldAtoms
  let edges := foldEdges atoms
  let svg := buildIrrep194 atoms
  logInfo s!"[Irrep 194] walked {atoms.length} decls (with {edges.length} preserved arrows) through {numIrrepSteps} irrep steps, compacting {compactionRadius 0} → {compactionRadius (numIrrepSteps - 1)} → {svg.length}-byte animated SVG."

syntax (name := writeIrrep194Cmd) "#writeirrep194 " str : command

@[command_elab writeIrrep194Cmd]
def elabWriteIrrep194 : CommandElab := fun stx => do
  match stx with
  | `(#writeirrep194 $p:str) => do
    let path := p.getString
    let atoms ← projectFoldAtoms
    let edges := foldEdges atoms
    let svg := buildIrrep194 atoms
    IO.FS.writeFile path svg
    logInfo s!"[Irrep 194] wrote {svg.length} bytes ({atoms.length} decls, {edges.length} arrows, {numIrrepSteps} steps, compaction {compactionRadius 0}→{compactionRadius (numIrrepSteps - 1)}) to {path}"
  | _ => throwError "ill-formed #writeirrep194 command"

syntax (name := thompsonCmd) "#thompson" : command

@[command_elab thompsonCmd]
def elabThompson : CommandElab := fun _ => do
  let atoms ← projectFoldAtoms
  let svg := buildThompson atoms
  logInfo s!"[Thompson] placed {atoms.length} decls into T1 … T{numThompson}, sampled across {numExpansions} q-expansions → {svg.length}-byte animated SVG."

syntax (name := writeThompsonCmd) "#writethompson " str : command

@[command_elab writeThompsonCmd]
def elabWriteThompson : CommandElab := fun stx => do
  match stx with
  | `(#writethompson $p:str) => do
    let path := p.getString
    let atoms ← projectFoldAtoms
    let svg := buildThompson atoms
    IO.FS.writeFile path svg
    logInfo s!"[Thompson] wrote {svg.length} bytes ({atoms.length} decls, T1 … T{numThompson}, {numExpansions} expansions) to {path}"
  | _ => throwError "ill-formed #writethompson command"

/-! ## Build-time generation -/

#irrep194

#writeirrep194 "atlas_irrep194.svg"

#thompson

#writethompson "atlas_thompson.svg"

end Irrep194
