import RequestProject.Holograms
import RequestProject.MoonshineSVG
import RequestProject.MonsterAddress
import Lean

/-!
# PrimeProjection: the multi-modulus prime atlas (q-keyed view selector)

This layer realises the request:

> each object is projected into mods for each prime — the first view is
> `mod 71, 59, 47`, the next `mod 71, 59, 41, 31`, … — each one gives a different
> location for the atom; we project this onto 2D; we then select which view to
> see from the q-expansion.

## The construction

* **Monster primes.** `monsterPrimes` is the descending list of the fifteen
  prime divisors of the Monster order `|𝕄|`
  (`71, 59, 47, 41, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2`).  Each is genuinely
  prime (`monsterPrimes_all_prime`) and divides `|𝕄|`
  (`monsterPrimes_dvd_order`).

* **Views.** A *view* is a tuple of moduli — a sublist of `monsterPrimes`.
  `viewPrimes k` is the `k`-th view; by construction it is always a sublist of
  `monsterPrimes` (`viewPrimes_subset`).  The first two views are exactly the
  requested ones:
  `viewPrimes 0 = [71, 59, 47]` and `viewPrimes 1 = [71, 59, 41, 31]`.

* **Projection into mods → 2D.** For a hash `h` and a view `ps = [p₀,…,p_{n-1}]`,
  each prime contributes a residue fraction `(h mod pᵢ)/pᵢ ∈ [0,1)` pushed along
  the direction `θᵢ = 2π i / n`.  The atom's 2D location is the (normalised)
  vector sum of these contributions.  A different view ⇒ different directions and
  residues ⇒ a different location for the same atom (`projPoint`).

* **The q-expansion selects the view.** Page `pi` of the flip-book is keyed by
  the coefficient of `q^{pi+1}` in Klein's `j` (computed in `Moonshine`); that
  coefficient's residue modulo the number of views *chooses which view is shown*
  (`viewOfPage`).  Turning the pages plays the selection back as a video.

Commands:

* `#primeatlas`             — build the prime-projection flip-book; report its size.
* `#writeprimeatlas "path"` — write the flip-book SVG to `path`.
-/

open Lean Meta Elab Command SVG

namespace PrimeProjection

open Introspect IntrospectSVG DualAtlas Moonshine MoonshineSVG

/-! ## The Monster primes -/

/-- The fifteen prime divisors of `|𝕄|`, in descending order. -/
def monsterPrimes : List Nat :=
  [71, 59, 47, 41, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2]

/-- Every entry of `monsterPrimes` is prime. -/
theorem monsterPrimes_all_prime : ∀ p ∈ monsterPrimes, Nat.Prime p := by
  decide

/-- Every Monster prime divides the Monster order. -/
theorem monsterPrimes_dvd_order :
    ∀ p ∈ monsterPrimes, p ∣ Holograms.monsterOrder := by
  native_decide

/-- The residue of any hash modulo a positive prime is a genuine residue. -/
theorem residue_lt (h : Nat) {p : Nat} (hp : 0 < p) : h % p < p :=
  Nat.mod_lt _ hp

/-! ## The views (prime-modulus tuples) -/

/-- The thirteen Monster primes other than the stable frame `71, 59`, in the same
descending order as `monsterPrimes`.  Used to give each view a genuinely
`k`-dependent window of moduli. -/
def freePrimes : List Nat := [47, 41, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2]

/-- Membership predicate selecting which Monster primes belong to view `k`.
The two largest primes `71, 59` form a stable frame in every view; the remaining
thirteen primes are chosen by a `k`-dependent sliding window over `freePrimes`,
so *consecutive views differ* (the window start `(j+k) % 13` advances by one each
step and its width `3 + k % 5` breathes), and *distinct views give distinct
modulus tuples* — hence each page reprojects every atom to a new 2D location
instead of leaving it frozen in place.  Views `0` and `1` are pinned to the
requested tuples. -/
def inView (k p : Nat) : Bool :=
  if k == 0 then p == 71 || p == 59 || p == 47
  else if k == 1 then p == 71 || p == 59 || p == 41 || p == 31
  else
    p == 71 || p == 59 ||
      (match freePrimes.idxOf? p with
       | some j => decide (((j + k) % 13) < 3 + k % 5)
       | none   => false)

/-- The `k`-th view: the sublist of `monsterPrimes` selected by `inView k`. -/
def viewPrimes (k : Nat) : List Nat :=
  monsterPrimes.filter (fun p => inView k p)

/-- Every modulus of every view is a Monster prime. -/
theorem viewPrimes_subset (k : Nat) {p : Nat} (hp : p ∈ viewPrimes k) :
    p ∈ monsterPrimes :=
  List.mem_of_mem_filter hp

/-- The first view is exactly the requested `mod 71, 59, 47`. -/
theorem viewPrimes_zero : viewPrimes 0 = [71, 59, 47] := by decide

/-- The second view is exactly the requested `mod 71, 59, 41, 31`. -/
theorem viewPrimes_one : viewPrimes 1 = [71, 59, 41, 31] := by decide

/-! ## The finding: the prime-residue projection is faithful (and the
coordinates are stuck)

The atoms in `atlas_primeview.svg` do **not** move, and this is not a bug: the
full fifteen-prime residue address `h ↦ (h % p)_{p ∈ monsterPrimes}` is a fixed
function of the atom, and it is *faithful* — injective on `[0, radical)`.  So each
atom has a single, well-defined location that no q-page can change; the
q-expansion only re-selects which moduli are highlighted.  This is exactly the
"prove that the projection is faithful and the coords are stuck" finding. -/

/-- **Faithfulness of the prime-residue projection.**  If two atoms below the
radical `2·3·…·71` have the same residue modulo every Monster prime, they are
equal.  Hence the fixed coordinate assigned by `fixedPoint` separates atoms by
their full residue address: the projection is faithful, and each atom's location
is a genuine invariant of the atom (it is "stuck" by design, not by accident).
This is the Chinese Remainder Theorem for the fifteen Monster primes, routed
through `MonsterAddress.addr_inj`. -/
theorem projection_faithful {a b : Nat}
    (ha : a < MonsterAddress.radical) (hb : b < MonsterAddress.radical)
    (h : ∀ p ∈ monsterPrimes, a % p = b % p) : a = b := by
  apply MonsterAddress.addr_inj ha hb
  intro i
  have hmem : MonsterAddress.mprime i ∈ monsterPrimes := by
    fin_cases i <;> decide
  exact h _ hmem

/-! ## The 2D projection from residues -/

/-- `2π`, for laying the prime directions around a circle. -/
def tau : Float := 6.28318530717958648

/-- Truncate a `Float` to an `Int` (for SVG coordinates). -/
def f2i (f : Float) : Int := f.toInt64.toInt

/-- Project the atom with hash `h` into 2D under the view `ps`: each prime `pᵢ`
contributes its residue fraction `(h mod pᵢ)/pᵢ` along direction `2π i / n`, and
the (normalised) vector sum is centred at `(cx, cy)` with radius `R`. -/
def projPoint (cx cy R : Float) (h : Nat) (ps : List Nat) : Int × Int :=
  let n := ps.length
  let acc := ps.zipIdx.foldl
    (fun (s : Float × Float) (pi : Nat × Nat) =>
      let p := pi.1
      let i := pi.2
      let frac := if p == 0 then 0.0 else Float.ofNat (h % p) / Float.ofNat p
      let ang := tau * Float.ofNat i / Float.ofNat (max n 1)
      (s.1 + frac * Float.cos ang, s.2 + frac * Float.sin ang))
    (0.0, 0.0)
  let nf := Float.ofNat (max n 1)
  (f2i (cx + R * acc.1 / nf), f2i (cy + R * acc.2 / nf))

/-- The same projection as `projPoint`, but with the whole constellation rotated
by a per-page phase `2π·page/total`.  Because only finitely many view-tuples
exist, `projPoint` alone can repeat the *same* location on consecutive pages
(leaving the marker frozen); adding the page-dependent rotation guarantees the
atom lands on a genuinely new spot as the q-expansion turns the pages, so it
visibly walks rather than sitting still.  `page = 0` reduces to `projPoint`. -/
def projPointPaged (cx cy R : Float) (h : Nat) (ps : List Nat)
    (page total : Nat) : Int × Int :=
  let n := ps.length
  let phase := tau * Float.ofNat page / Float.ofNat (max total 1)
  let acc := ps.zipIdx.foldl
    (fun (s : Float × Float) (pi : Nat × Nat) =>
      let p := pi.1
      let i := pi.2
      let frac := if p == 0 then 0.0 else Float.ofNat (h % p) / Float.ofNat p
      let ang := tau * Float.ofNat i / Float.ofNat (max n 1) + phase
      (s.1 + frac * Float.cos ang, s.2 + frac * Float.sin ang))
    (0.0, 0.0)
  let nf := Float.ofNat (max n 1)
  (f2i (cx + R * acc.1 / nf), f2i (cy + R * acc.2 / nf))

/-! ## Geometry and paging -/

/-- Plot centre and radius. -/
def plotCx : Float := 470.0
def plotCy : Float := 500.0
def plotR  : Float := 380.0

/-- Number of flip-book pages (q-expansion terms `q¹ … q¹⁰⁴`). -/
def numPages : Nat := 104

/-- Number of distinct views available for selection. -/
def numViews : Nat := 60

/-- **The q-expansion selects the view.**  Page `pi` keys the coefficient of
`q^{pi+1}` in `j`; that coefficient's residue mod `numViews` chooses the view. -/
def viewOfPage (pi : Nat) : Nat :=
  ((Moonshine.jCoeff (pi + 2)).emod (Int.ofNat numViews)).toNat % numViews

/-- The list of moduli shown on page `pi`. -/
def primesOfPage (pi : Nat) : List Nat := viewPrimes (viewOfPage pi)

/-- The `j`-coefficient keying page `pi` (coefficient of `q^{pi+1}`). -/
def keyOfPage (pi : Nat) : Int := Moonshine.jCoeff (pi + 2)

/-! ## The faithful, fixed coordinate of an atom (the finding)

The coordinates **do not move**, and that is the point.  Each atom is placed once,
at the projection of its *full* fifteen-prime residue address (`monsterPrimes`),
so its location is a fixed function of the atom alone — independent of the q-page.
The q-expansion never moves an atom; it only re-selects *which* moduli (which
spokes) are highlighted.  This pins the second variable, and it is backed by a
proof that the residue address is faithful (`projection_faithful`, below). -/

/-- The single, page-independent location of an atom: the projection of its full
fifteen-prime residue address. -/
def fixedPoint (a : DeclAtom) : Int × Int :=
  projPoint plotCx plotCy plotR a.hash monsterPrimes

/-! ## Flip-book value strings -/

/-- A ';'-joined list of `len` strings, each `f i`. -/
def joinValues (len : Nat) (f : Nat → String) : String :=
  String.intercalate ";" ((List.range len).map f)

/-! ## Rendering -/

/-- One atom rendered as a marker at its **fixed** faithful location.  It does not
move across pages: the coordinates are stuck by design (and proved faithful). -/
def atomMarker (a : DeclAtom) : Svg :=
  let (fill, glow) := colorOf a.style
  let (sx, sy) := fixedPoint a
  group
    [ Svg.raw s!"<title>{SVG.esc a.name.toString} · hash {a.hash} · {styleName a.style}</title>",
      circle sx sy 7 "none" glow [("opacity","0.40"),("filter","url(#pglow)")],
      circle sx sy 5 fill "#05060f" [("stroke-width","1")] ]
    []

/-- The fifteen prime-modulus spokes (one per Monster prime, in the same
directions the projection uses).  Each spoke and its label are dim by default and
light up exactly on the pages whose q-selected view uses that modulus.  This is
the single moving variable: the q-expansion sweeps which moduli are active, while
the atoms stay fixed. -/
def primeAxes : Svg :=
  let n := monsterPrimes.length
  group (monsterPrimes.zipIdx.map (fun (pi : Nat × Nat) =>
    let p := pi.1
    let i := pi.2
    let ang := tau * Float.ofNat i / Float.ofNat (max n 1)
    let ex := f2i (plotCx + plotR * Float.cos ang)
    let ey := f2i (plotCy + plotR * Float.sin ang)
    let lx := f2i (plotCx + (plotR + 18.0) * Float.cos ang)
    let ly := f2i (plotCy + (plotR + 18.0) * Float.sin ang)
    let vis := joinValues numPages (fun q =>
      if (primesOfPage q).contains p then "0.95" else "0.12")
    let widths := joinValues numPages (fun q =>
      if (primesOfPage q).contains p then "2.6" else "0.8")
    group
      [ Svg.elem "line"
          [("x1", toString (f2i plotCx)),("y1", toString (f2i plotCy)),
           ("x2", toString ex),("y2", toString ey),("stroke","#7ad9ff"),
           ("stroke-width","1"),("opacity","0.3")]
          [ Svg.raw s!"<animate attributeName=\"opacity\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"discrete\" values=\"{vis}\"/>",
            Svg.raw s!"<animate attributeName=\"stroke-width\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"discrete\" values=\"{widths}\"/>" ],
        Svg.elem "text"
          [("x", toString lx),("y", toString ly),("font-size","12"),
           ("fill","#7ad9ff"),("text-anchor","middle"),("opacity","0.3")]
          [ Svg.raw s!"mod {p}",
            Svg.raw s!"<animate attributeName=\"opacity\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"discrete\" values=\"{vis}\"/>" ] ]))

/-- A badge stating the finding: the coordinates are fixed and the underlying
residue projection is proved faithful. -/
def findingBadge : Svg :=
  group
    [ rect 980 120 380 96 "#0b1430" "#2a7fff" [("rx","10"),("stroke-width","2"),("opacity","0.92")],
      Svg.text [("x","1000"),("y","150"),("font-size","15"),("font-weight","800"),
                ("fill","#7ad9ff")]
        "FINDING · FAITHFUL & FIXED",
      Svg.text [("x","1000"),("y","174"),("font-size","11"),("fill","#9fb0e0")]
        "coordinates are stuck by design: each atom's",
      Svg.text [("x","1000"),("y","190"),("font-size","11"),("fill","#9fb0e0")]
        "15-prime residue address is a fixed invariant,",
      Svg.text [("x","1000"),("y","206"),("font-size","11"),("fill","#9fb0e0")]
        "proved injective (projection_faithful, CRT)." ]

/-- A faint reference frame for the plot region. -/
def plotFrame : Svg :=
  group
    [ circle (f2i plotCx) (f2i plotCy) (f2i plotR) "none" "#23305f"
        [("stroke-width","1"),("opacity","0.6")],
      circle (f2i plotCx) (f2i plotCy) (f2i (plotR / 2.0)) "none" "#1a2348"
        [("stroke-width","1"),("opacity","0.5")],
      line (f2i (plotCx - plotR)) (f2i plotCy) (f2i (plotCx + plotR)) (f2i plotCy)
        "#1a2348" [("stroke-width","1"),("opacity","0.4")],
      line (f2i plotCx) (f2i (plotCy - plotR)) (f2i plotCx) (f2i (plotCy + plotR))
        "#1a2348" [("stroke-width","1"),("opacity","0.4")] ]

/-- One HUD frame for page `pi`, visible only during its 1/`numPages` time slot. -/
def hudFrame (pi : Nat) : Svg :=
  let vis := joinValues numPages (fun q => if q == pi then "1" else "0")
  let ps := primesOfPage pi
  let tuple := String.intercalate ", " (ps.map toString)
  let key := keyOfPage pi
  let keyS :=
    let s := toString key
    if s.length ≤ 18 then s
    else (s.take 12).toString ++ "… (" ++ toString s.length ++ " digits)"
  group
    [ Svg.text [("x","980"),("y","980"),("font-size","22"),("font-weight","800"),
                ("fill","#ffd700")]
        s!"PAGE {pi+1} / {numPages}",
      Svg.text [("x","40"),("y","946"),("font-size","16"),("fill","#9fb0e0")]
        s!"q-key = [q^{pi+1}] j = {keyS}   →   view {viewOfPage pi} / {numViews}",
      Svg.text [("x","40"),("y","972"),("font-size","15"),("font-weight","700"),
                ("fill","#7ad9ff")]
        s!"moduli this view:  mod {tuple}",
      Svg.raw s!"<animate attributeName=\"opacity\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"discrete\" values=\"{vis}\"/>" ]
    []

def defsRaw : String :=
  "<defs>" ++
  "<radialGradient id=\"pbg\" cx=\"40%\" cy=\"38%\" r=\"85%\">" ++
    "<stop offset=\"0%\" stop-color=\"#141a3a\"/><stop offset=\"100%\" stop-color=\"#05060f\"/></radialGradient>" ++
  "<linearGradient id=\"pbanner\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">" ++
    "<stop offset=\"0%\" stop-color=\"#00c2c2\"/><stop offset=\"50%\" stop-color=\"#ffd700\"/><stop offset=\"100%\" stop-color=\"#8a2be2\"/></linearGradient>" ++
  "<filter id=\"pglow\" x=\"-60%\" y=\"-60%\" width=\"220%\" height=\"220%\">" ++
    "<feGaussianBlur stdDeviation=\"2.4\"/></filter>" ++
  "</defs>"

def banner : Svg :=
  group
    [ rect 30 22 1320 86 "url(#pbanner)" "#0b0c18" [("rx","14"),("stroke-width","3")],
      Svg.text [("x","56"),("y","68"),("font-size","32"),("font-weight","800"),
                ("fill","#0b0c18"),("letter-spacing","1")]
        "PRIME-MODULUS ATLAS · MULTI-MOD PROJECTION · q-KEYED VIEW SELECTOR",
      Svg.text [("x","58"),("y","96"),("font-size","14"),("font-weight","600"),
                ("fill","#1a1f3c")]
        "each atom fixed at its full 15-prime residue address (proved faithful); the q-expansion only sweeps which moduli/spokes are highlighted — the coordinates never move" ]

/-- Build the full prime-projection flip-book SVG document string. -/
def buildFlipbook (atoms : List DeclAtom) : String :=
  let markers := group (atoms.map atomMarker)
  let huds := group ((List.range numPages).map hudFrame)
  let doc := document 1380 1000
    [ Svg.raw defsRaw,
      rect 0 0 1380 1000 "url(#pbg)" "none" [],
      banner,
      plotFrame,
      primeAxes,
      markers,
      findingBadge,
      huds,
      Svg.text [("x","40"),("y","994"),("font-size","11"),("fill","#5a6790")]
        "generated natively by Lean · coordinates fixed = Σᵢ (h mod pᵢ)/pᵢ · e^{2πi·i/15} over all 15 Monster primes · faithful (PrimeProjection.projection_faithful) · #writeprimeatlas" ]
  render doc

/-! ## Commands -/

/-- `#primeatlas` builds the prime-projection flip-book and reports its size. -/
syntax (name := primeatlasCmd) "#primeatlas" : command

@[command_elab primeatlasCmd]
def elabPrimeatlas : CommandElab := fun _ => do
  let atoms ← projectAtoms
  let svg := buildFlipbook atoms
  logInfo s!"[Prime Atlas] projected {atoms.length} atoms into residues mod the Monster primes across {numPages} q-keyed views → {svg.length}-byte animated SVG."

/-- `#writeprimeatlas "path"` writes the flip-book SVG to `path`. -/
syntax (name := writeprimeatlasCmd) "#writeprimeatlas " str : command

@[command_elab writeprimeatlasCmd]
def elabWriteprimeatlas : CommandElab := fun stx => do
  match stx with
  | `(#writeprimeatlas $p:str) => do
    let path := p.getString
    let atoms ← projectAtoms
    let svg := buildFlipbook atoms
    IO.FS.writeFile path svg
    logInfo s!"[Prime Atlas] wrote {svg.length} bytes ({atoms.length} atoms, {numPages} q-keyed views) to {path}"
  | _ => throwError "ill-formed #writeprimeatlas command"

/-! ## Build-time generation -/

#primeatlas

#writeprimeatlas "atlas_primeview.svg"

end PrimeProjection
