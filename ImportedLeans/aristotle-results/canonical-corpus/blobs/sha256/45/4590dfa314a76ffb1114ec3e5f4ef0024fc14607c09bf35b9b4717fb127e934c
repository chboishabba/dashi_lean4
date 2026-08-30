/-!
# SVG: a tiny native SVG abstract-syntax tree and pretty-printer

Lean can emit SVG natively: an `Svg` value is just a term, and `svgToString`
serialises it to a self-contained `<svg>…</svg>` document fragment.  This is the
rendering substrate for the *introspective atlas comic book* (`IntrospectSVG`).

The AST is deliberately small but total:

* `Svg.elem tag attrs children` — a generic element (covers `rect`, `circle`,
  `polygon`, `g`, `path`, `defs`, …).
* `Svg.text attrs content` — a text node.
* `Svg.raw content` — an escape hatch for verbatim markup (used for SMIL
  `<animate>` / `<animateTransform>` and gradient/filter definitions).

Convenience builders (`rect`, `circle`, `line`, `polygon`, `group`) reproduce the
classic constructor names while delegating to `Svg.elem`.
-/

namespace SVG

/-- A minimal, total SVG abstract syntax tree. -/
inductive Svg where
  | elem (tag : String) (attrs : List (String × String)) (children : List Svg)
  | text (attrs : List (String × String)) (content : String)
  | raw  (content : String)
deriving Inhabited

/-- XML-escape a string for safe inclusion in SVG text/attributes. -/
def esc (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (match c with
      | '&' => "&amp;"
      | '<' => "&lt;"
      | '>' => "&gt;"
      | '"' => "&quot;"
      | '\'' => "&apos;"
      | c   => String.singleton c)) ""

/-- Render an attribute list as `k="v" …`. -/
def renderAttrs (attrs : List (String × String)) : String :=
  String.intercalate " " (attrs.map (fun (k, v) => s!"{k}=\"{v}\""))

/-- Serialise an `Svg` value to a string. -/
partial def svgToString : Svg → String
  | .raw s => s
  | .text attrs content =>
      s!"<text {renderAttrs attrs}>{esc content}</text>"
  | .elem tag attrs children =>
      if children.isEmpty then
        s!"<{tag} {renderAttrs attrs}/>"
      else
        let inner := String.join (children.map svgToString)
        s!"<{tag} {renderAttrs attrs}>{inner}</{tag}>"

/-! ## Convenience builders -/

/-- A `<g>` group element. -/
def group (children : List Svg) (attrs : List (String × String) := []) : Svg :=
  .elem "g" attrs children

/-- A `<rect>`. -/
def rect (x y w h : Int) (fill stroke : String)
    (extra : List (String × String) := []) : Svg :=
  .elem "rect"
    ([("x", toString x), ("y", toString y), ("width", toString w),
      ("height", toString h), ("fill", fill), ("stroke", stroke)] ++ extra) []

/-- A `<circle>`. -/
def circle (cx cy r : Int) (fill stroke : String)
    (extra : List (String × String) := []) : Svg :=
  .elem "circle"
    ([("cx", toString cx), ("cy", toString cy), ("r", toString r),
      ("fill", fill), ("stroke", stroke)] ++ extra) []

/-- A `<line>`. -/
def line (x1 y1 x2 y2 : Int) (stroke : String)
    (extra : List (String × String) := []) : Svg :=
  .elem "line"
    ([("x1", toString x1), ("y1", toString y1), ("x2", toString x2),
      ("y2", toString y2), ("stroke", stroke)] ++ extra) []

/-- A `<polygon>` from a list of points. -/
def polygon (pts : List (Int × Int)) (fill stroke : String)
    (extra : List (String × String) := []) : Svg :=
  let p := String.intercalate " " (pts.map (fun (x, y) => s!"{x},{y}"))
  .elem "polygon" ([("points", p), ("fill", fill), ("stroke", stroke)] ++ extra) []

/-- Wrap a list of elements into a complete `<svg>` document of the given size. -/
def document (w h : Nat) (children : List Svg) : Svg :=
  .elem "svg"
    [("xmlns", "http://www.w3.org/2000/svg"),
     ("viewBox", s!"0 0 {w} {h}"),
     ("width", toString w), ("height", toString h),
     ("font-family", "ui-monospace, Menlo, Consolas, monospace")] children

/-- Serialise a document with the XML prologue. -/
def render (doc : Svg) : String :=
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++ svgToString doc

end SVG
