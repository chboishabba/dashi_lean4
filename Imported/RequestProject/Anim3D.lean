import RequestProject.SvgCore

/-!
# A tiny animated-3-d toolkit for SVG

The pictures of `RequestProject/Repair3D.lean` and `RequestProject/RepairAtlas3D.lean` are
genuinely three-dimensional: world points are rotated about the vertical axis and projected
orthographically, and the animation is produced by emitting one keyframe per rotation step
into an SVG `<animate values="…">` list.  A viewer that ignores SMIL still shows the first
frame, which is a perfectly good static picture.

Nothing here is mathematical — it is the drawing layer:

* `P3`, `rotZ`, `Cam`, `proj` : points, rotation about the `z` axis, an orthographic camera
  looking slightly down (`tilt`);
* `spinDot`, `spinEdge`, `spinLabel` : a sphere, a segment and a text label carried around by
  the rotation, each emitted as a shape with `<animate>` keyframe lists;
* `depthShade` : darker and smaller at the back, so the rotation reads as depth.
-/

namespace Anim3D

open SvgCore

/-- A point of the world. -/
structure P3 where
  x : Float
  y : Float
  z : Float
  deriving Inhabited

/-- Rotation about the vertical (`z`) axis by `t` radians. -/
def rotZ (t : Float) (p : P3) : P3 :=
  ⟨p.x * Float.cos t - p.y * Float.sin t, p.x * Float.sin t + p.y * Float.cos t, p.z⟩

/-- An orthographic camera: `x` runs right, `z` runs up the page, and `y` runs into the page,
foreshortened by `tilt`. -/
structure Cam where
  cx : Float
  cy : Float
  scale : Float
  tilt : Float
  deriving Inhabited

/-- Project a world point to the page. -/
def proj (c : Cam) (p : P3) : Float × Float :=
  (c.cx + c.scale * p.x, c.cy - c.scale * p.z + c.scale * c.tilt * p.y)

/-- How close the point is to the camera, normalized to `[-1,1]` for a unit-radius scene. -/
def closeness (p : P3) : Float := p.y

/-! ### Keyframes -/

/-- Number of rotation keyframes emitted per turn. -/
def frameCount : Nat := 36

def tau : Float := 6.283185307179586

/-- The rotation angles of the keyframes, one full turn. -/
def frameAngles : List Float :=
  (List.range frameCount).map fun i => tau * i.toFloat / frameCount.toFloat

/-- A `;`-separated keyframe list, closed up by repeating the first value so that the loop is
seamless. -/
def valueList (vs : List Float) : String :=
  let vs := vs ++ [vs.headD 0.0]
  String.intercalate ";" (vs.map num)

/-- An `<animate>` element cycling an attribute through the given keyframe values. -/
def animValues (attr : String) (vs : List Float) (dur : Float) : String :=
  "<animate attributeName=\"" ++ attr ++ "\" values=\"" ++ valueList vs ++
    "\" dur=\"" ++ num dur ++ "s\" repeatCount=\"indefinite\" calcMode=\"linear\"/>"

/-- The same, for a string-valued attribute such as `points` or `fill`. -/
def animStrings (attr : String) (vs : List String) (dur : Float) : String :=
  let vs := vs ++ [vs.headD ""]
  "<animate attributeName=\"" ++ attr ++ "\" values=\"" ++ String.intercalate ";" vs ++
    "\" dur=\"" ++ num dur ++ "s\" repeatCount=\"indefinite\" calcMode=\"linear\"/>"

/-! ### Spinning primitives -/

/-- Radius scaled by depth: points at the front are bigger. -/
def depthRadius (r : Float) (p : P3) : Float := r * (1.0 + 0.30 * closeness p)

/-- Opacity scaled by depth: points at the back fade out. -/
def depthOpacity (p : P3) : Float := 0.55 + 0.40 * (closeness p + 1.0) / 2.0

/-- A sphere at world point `p`, carried around by the rotation of the scene: its projected
centre, radius and opacity are animated through one full turn in `dur` seconds. -/
def spinDot (c : Cam) (p : P3) (r : Float) (fill stroke : String) (dur : Float)
    (strokeWidth : Float := 1.0) (extra : String := "") : String :=
  let pts := frameAngles.map fun t => rotZ t p
  let xs := pts.map fun q => (proj c q).1
  let ys := pts.map fun q => (proj c q).2
  let rs := pts.map fun q => depthRadius r q
  let os := pts.map fun q => depthOpacity q
  "  <circle cx=\"" ++ num (xs.headD 0.0) ++ "\" cy=\"" ++ num (ys.headD 0.0) ++
    "\" r=\"" ++ num (rs.headD r) ++ "\" fill=\"" ++ fill ++ "\" stroke=\"" ++ stroke ++
    "\" stroke-width=\"" ++ num strokeWidth ++ "\"" ++
    (if extra == "" then "" else " " ++ extra) ++ ">" ++
    animValues "cx" xs dur ++ animValues "cy" ys dur ++ animValues "r" rs dur ++
    animValues "opacity" os dur ++ "</circle>"

/-- A segment between two world points, carried around by the rotation.  The endpoints are
pulled back by `t₁`, `t₂` page pixels so that the segment stops short of the two spheres. -/
def spinEdge (c : Cam) (p q : P3) (t₁ t₂ : Float) (stroke : String) (dur : Float)
    (width : Float := 1.2) (opacity : Float := 0.75) (dash : String := "")
    (extra : String := "") (child : String := "") : String :=
  let ends := frameAngles.map fun t =>
    let a := proj c (rotZ t p)
    let b := proj c (rotZ t q)
    let dx := b.1 - a.1
    let dy := b.2 - a.2
    let len := Float.sqrt (dx * dx + dy * dy)
    let len := if len == 0.0 then 1.0 else len
    ((a.1 + dx / len * t₁, a.2 + dy / len * t₁), (b.1 - dx / len * t₂, b.2 - dy / len * t₂))
  let x1s := ends.map fun e => e.1.1
  let y1s := ends.map fun e => e.1.2
  let x2s := ends.map fun e => e.2.1
  let y2s := ends.map fun e => e.2.2
  "  <line x1=\"" ++ num (x1s.headD 0.0) ++ "\" y1=\"" ++ num (y1s.headD 0.0) ++
    "\" x2=\"" ++ num (x2s.headD 0.0) ++ "\" y2=\"" ++ num (y2s.headD 0.0) ++
    "\" stroke=\"" ++ stroke ++ "\" stroke-width=\"" ++ num width ++ "\" opacity=\"" ++
    num opacity ++ "\" stroke-linecap=\"round\"" ++
    (if dash == "" then "" else " stroke-dasharray=\"" ++ dash ++ "\"") ++
    (if extra == "" then "" else " " ++ extra) ++ ">" ++
    animValues "x1" x1s dur ++ animValues "y1" y1s dur ++
    animValues "x2" x2s dur ++ animValues "y2" y2s dur ++ child ++ "</line>"

/-- A text label pinned to a world point and carried around by the rotation (the glyphs stay
upright — only the anchor moves). -/
def spinLabel (c : Cam) (p : P3) (s : String) (size : Float) (fill : String) (dur : Float)
    (dy : Float := 0.0) (weight : String := "normal") : String :=
  let pts := frameAngles.map fun t => rotZ t p
  let xs := pts.map fun q => (proj c q).1
  let ys := pts.map fun q => (proj c q).2 + dy
  let os := pts.map fun q => depthOpacity q
  "  <text x=\"" ++ num (xs.headD 0.0) ++ "\" y=\"" ++ num (ys.headD 0.0) ++
    "\" font-size=\"" ++ num size ++ "\" fill=\"" ++ fill ++
    "\" text-anchor=\"middle\" dominant-baseline=\"central\" font-weight=\"" ++ weight ++
    "\">" ++ esc s ++
    animValues "x" xs dur ++ animValues "y" ys dur ++ animValues "opacity" os dur ++ "</text>"

/-- A flat ellipse: the shadow of a horizontal circle of radius `r` at height `z`. -/
def ringOutline (c : Cam) (r z : Float) (stroke : String) (width : Float := 1.0)
    (dash : String := "") (opacity : Float := 0.5) : String :=
  let ctr := proj c ⟨0.0, 0.0, z⟩
  "  <ellipse cx=\"" ++ num ctr.1 ++ "\" cy=\"" ++ num ctr.2 ++ "\" rx=\"" ++
    num (c.scale * r) ++ "\" ry=\"" ++ num (c.scale * c.tilt * r) ++
    "\" fill=\"none\" stroke=\"" ++ stroke ++ "\" stroke-width=\"" ++ num width ++
    "\" opacity=\"" ++ num opacity ++ "\"" ++
    (if dash == "" then "" else " stroke-dasharray=\"" ++ dash ++ "\"") ++ "/>"

/-- A point of the horizontal circle of radius `r` at height `z`, at angle `2π·i/n`. -/
def ringPoint (n i : Nat) (r z : Float) : P3 :=
  let t := tau * i.toFloat / n.toFloat
  ⟨r * Float.cos t, r * Float.sin t, z⟩

end Anim3D
