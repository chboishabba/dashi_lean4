/-!
# A tiny SVG writer

Pure-`String` helpers used by `RequestProject/Visualization.lean`,
`RequestProject/ScanVisualization.lean`, `RequestProject/EyeCandy.lean` and
`RequestProject/Heatmap3D.lean` to emit the pictures in `svg/`.  Nothing here is
mathematical: it is a small combinator library producing well-formed SVG 1.1 markup — a
header carrying arrow markers, gradients, soft shadow / glow filters and a stylesheet, plus
circles, rectangles, polygons, lines, polylines, quadratic arcs, sectors, animations and
text.

Keeping the drawing primitives separate means the visualization files themselves only
contain the *data* being drawn — data that is checked against the formal statements by
`decide`.
-/

namespace SvgCore

/-- Format a float with two decimals, for SVG coordinates. -/
def num (x : Float) : String := toString ((x * 100.0).round / 100.0)

/-- Escape the characters that may not occur literally in XML character data. -/
def esc (s : String) : String :=
  ((s.replace "&" "&amp;").replace "<" "&lt;").replace ">" "&gt;"

/-! ### Colour helpers -/

private def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD (n % 16) '0'

/-- A byte as two hexadecimal digits. -/
def hex2 (n : Nat) : String :=
  let n := min n 255
  String.ofList [hexDigit (n / 16), hexDigit n]

/-- An `#rrggbb` colour from three bytes. -/
def rgb (r g b : Nat) : String := "#" ++ hex2 r ++ hex2 g ++ hex2 b

private def clamp01 (u : Float) : Float := if u < 0.0 then 0.0 else if u > 1.0 then 1.0 else u

/-- Linear interpolation between two `(r,g,b)` triples; `u = 0` gives the first colour. -/
def lerpColor (c₁ c₂ : Nat × Nat × Nat) (u : Float) : String :=
  let u := clamp01 u
  let mix (a b : Nat) : Nat := (a.toFloat + (b.toFloat - a.toFloat) * u).round.toUInt32.toNat
  rgb (mix c₁.1 c₂.1) (mix c₁.2.1 c₂.2.1) (mix c₁.2.2 c₂.2.2)

/-- A pale-amber-to-crimson ramp for error magnitudes (`u ∈ [0,1]`), used by the heat map. -/
def heatRamp (u : Float) : String :=
  let u := clamp01 u
  if u ≤ 0.5 then lerpColor (254, 243, 199) (251, 146, 60) (u * 2.0)
  else lerpColor (251, 146, 60) (159, 18, 57) ((u - 0.5) * 2.0)

/-! ### Document scaffolding -/

/-- The colours used for arrow heads; each gets its own `<marker>` in the header. -/
def arrowColors : List (String × String) :=
  [("slate", "#334155"), ("gold", "#b45309"), ("blue", "#1d4ed8"), ("pink", "#be185d"),
   ("green", "#047857"), ("violet", "#7c3aed"), ("white", "#f8fafc")]

private def markerDefs : String :=
  String.intercalate "\n" (arrowColors.map fun (name, col) =>
    "    <marker id=\"arrow-" ++ name ++ "\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" " ++
      "markerWidth=\"6\" markerHeight=\"6\" orient=\"auto-start-reverse\">" ++
      "<path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"" ++ col ++ "\"/></marker>")

/-- Glossy radial fills for the nodes: `url(#fill-gold)` and friends. -/
private def sphereFills : List (String × String × String) :=
  [("gold", "#fef3c7", "#fbbf24"), ("blue", "#dbeafe", "#93c5fd"),
   ("pink", "#fce7f3", "#f9a8d4"), ("slate", "#f1f5f9", "#cbd5e1"),
   ("green", "#d1fae5", "#6ee7b7"), ("violet", "#ede9fe", "#c4b5fd")]

private def sphereDefs : String :=
  String.intercalate "\n" (sphereFills.map fun (name, lo, hi) =>
    "    <radialGradient id=\"fill-" ++ name ++ "\" cx=\"35%\" cy=\"30%\" r=\"75%\">" ++
      "<stop offset=\"0%\" stop-color=\"#ffffff\"/>" ++
      "<stop offset=\"45%\" stop-color=\"" ++ lo ++ "\"/>" ++
      "<stop offset=\"100%\" stop-color=\"" ++ hi ++ "\"/></radialGradient>")

private def filterDefs : String :=
  "    <linearGradient id=\"bg\" x1=\"0\" y1=\"0\" x2=\"0.35\" y2=\"1\">" ++
    "<stop offset=\"0%\" stop-color=\"#ffffff\"/>" ++
    "<stop offset=\"55%\" stop-color=\"#f8fafc\"/>" ++
    "<stop offset=\"100%\" stop-color=\"#eef2ff\"/></linearGradient>\n" ++
  "    <linearGradient id=\"ink\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">" ++
    "<stop offset=\"0%\" stop-color=\"#1d4ed8\"/>" ++
    "<stop offset=\"50%\" stop-color=\"#7c3aed\"/>" ++
    "<stop offset=\"100%\" stop-color=\"#be185d\"/></linearGradient>\n" ++
  "    <linearGradient id=\"warm\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">" ++
    "<stop offset=\"0%\" stop-color=\"#fef3c7\"/>" ++
    "<stop offset=\"50%\" stop-color=\"#fb923c\"/>" ++
    "<stop offset=\"100%\" stop-color=\"#9f1239\"/></linearGradient>\n" ++
  "    <linearGradient id=\"hot\" x1=\"0\" y1=\"0\" x2=\"0\" y2=\"1\">" ++
    "<stop offset=\"0%\" stop-color=\"#f97316\"/>" ++
    "<stop offset=\"100%\" stop-color=\"#b91c1c\"/></linearGradient>\n" ++
  "    <filter id=\"soft-shadow\" x=\"-40%\" y=\"-40%\" width=\"180%\" height=\"180%\">" ++
    "<feDropShadow dx=\"0\" dy=\"1.6\" stdDeviation=\"2.2\" flood-color=\"#0f172a\" " ++
    "flood-opacity=\"0.28\"/></filter>\n" ++
  "    <filter id=\"card-shadow\" x=\"-20%\" y=\"-20%\" width=\"140%\" height=\"140%\">" ++
    "<feDropShadow dx=\"0\" dy=\"4\" stdDeviation=\"6\" flood-color=\"#1e293b\" " ++
    "flood-opacity=\"0.18\"/></filter>\n" ++
  "    <filter id=\"glow\" x=\"-70%\" y=\"-70%\" width=\"240%\" height=\"240%\">" ++
    "<feGaussianBlur stdDeviation=\"4\" result=\"b\"/>" ++
    "<feMerge><feMergeNode in=\"b\"/><feMergeNode in=\"b\"/>" ++
    "<feMergeNode in=\"SourceGraphic\"/></feMerge></filter>"

private def styleDefs : String :=
  "  <style>\n" ++
  "    .node circle { transition: transform .18s ease, filter .18s ease; " ++
      "transform-box: fill-box; transform-origin: center; }\n" ++
  "    .node:hover circle { transform: scale(1.16); filter: url(#glow); }\n" ++
  "    .node:hover text { font-weight: bold; }\n" ++
  "    .card { filter: url(#card-shadow); }\n" ++
  "    .pop { filter: url(#soft-shadow); }\n" ++
  "    .cell { transition: opacity .15s ease; }\n" ++
  "    .cell:hover { opacity: .65; }\n" ++
  "    .flow { stroke-dasharray: 7 6; animation: dash 1.6s linear infinite; }\n" ++
  "    @keyframes dash { to { stroke-dashoffset: -26; } }\n" ++
  "  </style>"

/-- Opening tag of a picture of the given size, with a soft background, arrow markers,
glossy node fills, shadow/glow filters and a small stylesheet.  `extraDefs` is spliced into
`<defs>` for picture-specific gradients. -/
def headerWith (w h : Float) (extraDefs : List String) : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
  "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"" ++ num w ++ "\" height=\"" ++ num h ++
    "\" viewBox=\"0 0 " ++ num w ++ " " ++ num h ++ "\" " ++
    "font-family=\"'DejaVu Sans','Helvetica Neue',Helvetica,Arial,sans-serif\">\n" ++
  "  <defs>\n" ++ markerDefs ++ "\n" ++ sphereDefs ++ "\n" ++ filterDefs ++
    (if extraDefs.isEmpty then "" else "\n" ++ String.intercalate "\n" extraDefs) ++
    "\n  </defs>\n" ++ styleDefs ++ "\n" ++
  "  <rect x=\"0\" y=\"0\" width=\"" ++ num w ++ "\" height=\"" ++ num h ++
    "\" fill=\"url(#bg)\"/>"

/-- Opening tag of a picture of the given size. -/
def header (w h : Float) : String := headerWith w h []

def footer : String := "</svg>"

def circle (cx cy r : Float) (fill stroke : String) (strokeWidth : Float := 1.5)
    (extra : String := "") : String :=
  "  <circle cx=\"" ++ num cx ++ "\" cy=\"" ++ num cy ++ "\" r=\"" ++ num r ++
    "\" fill=\"" ++ fill ++ "\" stroke=\"" ++ stroke ++ "\" stroke-width=\"" ++
    num strokeWidth ++ "\"" ++ (if extra == "" then "" else " " ++ extra) ++ "/>"

def rect (x y w h rx : Float) (fill stroke : String) (strokeWidth : Float := 1.5)
    (dash : String := "") (extra : String := "") : String :=
  "  <rect x=\"" ++ num x ++ "\" y=\"" ++ num y ++ "\" width=\"" ++ num w ++ "\" height=\"" ++
    num h ++ "\" rx=\"" ++ num rx ++ "\" fill=\"" ++ fill ++ "\" stroke=\"" ++ stroke ++
    "\" stroke-width=\"" ++ num strokeWidth ++
    (if dash == "" then "" else "\" stroke-dasharray=\"" ++ dash) ++ "\"" ++
    (if extra == "" then "" else " " ++ extra) ++ "/>"

/-- A text label.  `anchor` is `start`, `middle` or `end`. -/
def text (x y : Float) (s : String) (size : Float := 13.0) (fill : String := "#0f172a")
    (anchor : String := "middle") (weight : String := "normal")
    (style : String := "normal") (extra : String := "") : String :=
  "  <text x=\"" ++ num x ++ "\" y=\"" ++ num y ++ "\" font-size=\"" ++ num size ++
    "\" fill=\"" ++ fill ++ "\" text-anchor=\"" ++ anchor ++ "\" font-weight=\"" ++ weight ++
    "\" font-style=\"" ++ style ++ "\"" ++ (if extra == "" then "" else " " ++ extra) ++
    ">" ++ esc s ++ "</text>"

/-- A text label vertically centred on `y`. -/
def textMid (x y : Float) (s : String) (size : Float := 13.0) (fill : String := "#0f172a")
    (anchor : String := "middle") (weight : String := "normal")
    (extra : String := "") : String :=
  "  <text x=\"" ++ num x ++ "\" y=\"" ++ num y ++ "\" font-size=\"" ++ num size ++
    "\" fill=\"" ++ fill ++ "\" text-anchor=\"" ++ anchor ++ "\" font-weight=\"" ++ weight ++
    "\" dominant-baseline=\"central\"" ++ (if extra == "" then "" else " " ++ extra) ++
    ">" ++ esc s ++ "</text>"

def line (x1 y1 x2 y2 : Float) (stroke : String) (width : Float := 1.4)
    (arrow : String := "") (dash : String := "") (extra : String := "") : String :=
  "  <line x1=\"" ++ num x1 ++ "\" y1=\"" ++ num y1 ++ "\" x2=\"" ++ num x2 ++ "\" y2=\"" ++
    num y2 ++ "\" stroke=\"" ++ stroke ++ "\" stroke-width=\"" ++ num width ++ "\"" ++
    (if dash == "" then "" else " stroke-dasharray=\"" ++ dash ++ "\"") ++
    (if arrow == "" then "" else " marker-end=\"url(#arrow-" ++ arrow ++ ")\"") ++
    (if extra == "" then "" else " " ++ extra) ++ "/>"

/-- A filled polygon through the given points — the faces of the 3-d bars. -/
def polygon (pts : List (Float × Float)) (fill stroke : String) (width : Float := 1.0)
    (extra : String := "") : String :=
  "  <polygon points=\"" ++
    String.intercalate " " (pts.map fun (x, y) => num x ++ "," ++ num y) ++
    "\" fill=\"" ++ fill ++ "\" stroke=\"" ++ stroke ++ "\" stroke-width=\"" ++ num width ++
    "\" stroke-linejoin=\"round\"" ++ (if extra == "" then "" else " " ++ extra) ++ "/>"

def path (d : String) (stroke : String) (width : Float := 1.4) (arrow : String := "")
    (fill : String := "none") (extra : String := "") : String :=
  "  <path d=\"" ++ d ++ "\" fill=\"" ++ fill ++ "\" stroke=\"" ++ stroke ++
    "\" stroke-width=\"" ++ num width ++ "\"" ++
    (if arrow == "" then "" else " marker-end=\"url(#arrow-" ++ arrow ++ ")\"") ++
    (if extra == "" then "" else " " ++ extra) ++ "/>"

/-- An arrow from `(x1,y1)` to `(x2,y2)`, shortened by `t1` at the tail and `t2` at the head
(so that it starts and ends outside the two nodes it connects). -/
def arrow (x1 y1 x2 y2 t1 t2 : Float) (stroke : String) (color : String)
    (width : Float := 1.6) (extra : String := "") : String :=
  let dx := x2 - x1
  let dy := y2 - y1
  let len := Float.sqrt (dx * dx + dy * dy)
  let len := if len == 0.0 then 1.0 else len
  let ux := dx / len
  let uy := dy / len
  line (x1 + ux * t1) (y1 + uy * t1) (x2 - ux * t2) (y2 - uy * t2) stroke width color "" extra

/-- The `d` attribute of a quadratic Bézier from `(x1,y1)` to `(x2,y2)` bulging by `bulge`
pixels sideways, shortened by `t1`/`t2` at the two ends. -/
def curveD (x1 y1 x2 y2 t1 t2 bulge : Float) : String :=
  let dx := x2 - x1
  let dy := y2 - y1
  let len := Float.sqrt (dx * dx + dy * dy)
  let len := if len == 0.0 then 1.0 else len
  let ux := dx / len
  let uy := dy / len
  let ax := x1 + ux * t1
  let ay := y1 + uy * t1
  let bx := x2 - ux * t2
  let by' := y2 - uy * t2
  let mx := (ax + bx) / 2.0 - uy * bulge
  let my := (ay + by') / 2.0 + ux * bulge
  "M " ++ num ax ++ " " ++ num ay ++ " Q " ++ num mx ++ " " ++ num my ++ " " ++
    num bx ++ " " ++ num by'

/-- A quadratic Bézier from `(x1,y1)` to `(x2,y2)` bulging by `bulge` pixels sideways,
shortened by `t1`/`t2` at the two ends. -/
def curve (x1 y1 x2 y2 t1 t2 bulge : Float) (stroke : String) (color : String)
    (width : Float := 1.4) (extra : String := "") : String :=
  path (curveD x1 y1 x2 y2 t1 t2 bulge) stroke width color "none" extra

/-- A little self-loop hanging below the node centred at `(x,y)` of radius `r`. -/
def selfLoop (x y r : Float) (stroke : String) (color : String) : String :=
  path ("M " ++ num (x - 0.45 * r) ++ " " ++ num (y + 0.9 * r) ++
        " C " ++ num (x - 2.0 * r) ++ " " ++ num (y + 2.6 * r) ++
        " "   ++ num (x + 2.0 * r) ++ " " ++ num (y + 2.6 * r) ++
        " "   ++ num (x + 0.5 * r) ++ " " ++ num (y + 0.95 * r)) stroke 1.6 color

def joinLines (l : List String) : String := String.intercalate "\n" l

/-! ### Eye candy -/

/-- Wrap elements in a `<g>` carrying the given attributes (e.g. `class="node"`). -/
def group (attrs : String) (body : List String) : String :=
  "  <g " ++ attrs ++ ">\n" ++ joinLines body ++ "\n  </g>"

/-- A `<g>` marked `class="node"`, which the stylesheet makes grow and glow on hover. -/
def nodeGroup (body : List String) : String := group "class=\"node\"" body

/-- An `<animate>` element, to be nested inside a shape. -/
def animate (attr from_ to_ : String) (dur : Float) (repeatCount : String := "indefinite")
    (begin_ : Float := 0.0) : String :=
  "<animate attributeName=\"" ++ attr ++ "\" values=\"" ++ from_ ++ ";" ++ to_ ++ ";" ++
    from_ ++ "\" dur=\"" ++ num dur ++ "s\" begin=\"" ++ num begin_ ++
    "s\" repeatCount=\"" ++ repeatCount ++ "\"/>"

/-- A short bright dash that runs forever along the path `d` — a "comet" showing the
direction of the arrow.  Static renderers, which ignore the animation, still show a tasteful
bead of colour on the path. -/
def comet (d : String) (color : String) (width : Float) (dur : Float)
    (delay : Float := 0.0) (span : Float := 240.0) : String :=
  "  <path d=\"" ++ d ++ "\" fill=\"none\" stroke=\"" ++ color ++ "\" stroke-width=\"" ++
    num width ++ "\" stroke-linecap=\"round\" stroke-dasharray=\"9 " ++ num span ++
    "\" opacity=\"0.95\">" ++
    "<animate attributeName=\"stroke-dashoffset\" from=\"" ++ num (span + 9.0) ++
    "\" to=\"0\" dur=\"" ++ num dur ++ "s\" begin=\"" ++ num delay ++
    "s\" repeatCount=\"indefinite\"/></path>"

/-- A circle whose radius breathes: a soft halo behind a highlighted node. -/
def pulse (cx cy r : Float) (fill : String) (dur : Float := 2.6) (delay : Float := 0.0)
    : String :=
  "  <circle cx=\"" ++ num cx ++ "\" cy=\"" ++ num cy ++ "\" r=\"" ++ num r ++
    "\" fill=\"" ++ fill ++ "\" opacity=\"0.35\">" ++
    animate "r" (num r) (num (r * 1.35)) dur "indefinite" delay ++
    animate "opacity" "0.35" "0.05" dur "indefinite" delay ++ "</circle>"

/-- A rounded "card": the panel behind a block of a picture. -/
def card (x y w h rx : Float) (fill : String := "#ffffff") (stroke : String := "#e2e8f0")
    (strokeWidth : Float := 1.2) : String :=
  rect x y w h rx fill stroke strokeWidth "" "class=\"card\""

/-- A small rounded label chip with centred text. -/
def chip (cx cy w h : Float) (s : String) (fill stroke textColor : String)
    (size : Float := 12.0) : String :=
  joinLines
    [ rect (cx - w / 2.0) (cy - h / 2.0) w h (h / 2.0) fill stroke 1.2 "" "class=\"pop\"",
      textMid cx cy s size textColor "middle" "bold" ]

/-- The `d` of a circular arc from angle `a₁` to `a₂` (radians) on the circle of centre
`(cx,cy)` and radius `r`, drawn the short way when `a₂ - a₁ ≤ π`. -/
def arcPath (cx cy r a₁ a₂ : Float) : String :=
  let x1 := cx + r * Float.cos a₁
  let y1 := cy + r * Float.sin a₁
  let x2 := cx + r * Float.cos a₂
  let y2 := cy + r * Float.sin a₂
  let large := if a₂ - a₁ > 3.14159265358979 then "1" else "0"
  "M " ++ num x1 ++ " " ++ num y1 ++ " A " ++ num r ++ " " ++ num r ++ " 0 " ++ large ++
    " 1 " ++ num x2 ++ " " ++ num y2

/-- A gradient ramp bar with tick labels, used as a heat-map legend. -/
def rampBar (x y w h : Float) (steps : Nat) (colorOf : Float → String) : List String :=
  (List.range steps).map fun i =>
    let u := i.toFloat / (steps - 1 : Nat).toFloat
    rect (x + w * i.toFloat / steps.toFloat) y (w / steps.toFloat + 0.6) h 0.0
      (colorOf u) "none" 0.0

/-- Wrap a block of elements in a hyperlink, so that clicking anywhere on them opens `href`.
Used by the atlas sheet, whose rows are links to the other pictures. -/
def link (href : String) (body : List String) : String :=
  "  <a href=\"" ++ esc href ++ "\">\n" ++ joinLines body ++ "\n  </a>"

/-- Assemble a complete document. -/
def document (w h : Float) (body : List String) : String :=
  header w h ++ "\n" ++ joinLines body ++ "\n" ++ footer ++ "\n"

/-- Assemble a complete document with extra picture-specific `<defs>`. -/
def documentWith (w h : Float) (extraDefs : List String) (body : List String) : String :=
  headerWith w h extraDefs ++ "\n" ++ joinLines body ++ "\n" ++ footer ++ "\n"

end SvgCore
